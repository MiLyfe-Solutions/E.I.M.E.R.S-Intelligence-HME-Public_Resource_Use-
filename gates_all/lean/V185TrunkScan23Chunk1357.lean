import V185TrunkScan23Chunk1356

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8036019 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 7]
def baseStart_8036019 : Nat := 118140960795 + 8036019 * 2 ^ 59
def prefixEnd_8036019 : Nat := 4983230072969 + 3 ^ 40 * 8036019 * 2
def baseEnd_8036019 : Nat := 458482255073677752489503

theorem tailTrace_8036019 : CollatzResearch.WordTrace tailWord_8036019 prefixEnd_8036019 458482255073677752489503 := by
  unfold tailWord_8036019
  simp only [CollatzResearch.WordTrace]
  refine ⟨293097691873883080624559111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195398461249255387083039407 293097691873883080624559111)
  ·
    refine ⟨439646537810824620936838667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293097691873883080624559111 439646537810824620936838667)
    ·
      refine ⟨659469806716236931405258001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439646537810824620936838667 659469806716236931405258001)
      ·
        refine ⟨494602355037177698553943501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659469806716236931405258001 494602355037177698553943501)
        ·
          refine ⟨185475883138941636957728813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494602355037177698553943501 185475883138941636957728813)
          ·
            refine ⟨69553456177103113859148305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185475883138941636957728813 69553456177103113859148305)
            ·
              refine ⟨52165092132827335394361229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69553456177103113859148305 52165092132827335394361229)
              ·
                refine ⟨19561909549810250772885461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52165092132827335394361229 19561909549810250772885461)
                ·
                  refine ⟨458482255073677752489503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19561909549810250772885461 458482255073677752489503)
                  ·
                    rfl

theorem cell23_8036019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 7].length) (baseStart_8036019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036019 prefixEnd_8036019 := by exact prefixLift 8036019
  have htrace : WordTrace (prefixWord ++ tailWord_8036019) baseStart_8036019 baseEnd_8036019 := by
    simpa [prefixWord, tailWord_8036019, baseEnd_8036019] using wordTrace_append hprefix tailTrace_8036019
  have hstable : (prefixWord ++ tailWord_8036019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036019).length < 2 ^ (prefixWord ++ tailWord_8036019).sum := by decide
  have hdescent : baseEnd_8036019 < baseStart_8036019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036026 : List Nat := [3, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4]
def baseStart_8036026 : Nat := 118140960795 + 8036026 * 2 ^ 59
def prefixEnd_8036026 : Nat := 4983230072969 + 3 ^ 40 * 8036026 * 2
def baseEnd_8036026 : Nat := 4126343890027681245017995

theorem tailTrace_8036026 : CollatzResearch.WordTrace tailWord_8036026 prefixEnd_8036026 4126343890027681245017995 := by
  unfold tailWord_8036026
  simp only [CollatzResearch.WordTrace]
  refine ⟨73274486796214430205015983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195398631456571813880042621 73274486796214430205015983)
  ·
    refine ⟨109911730194321645307523975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73274486796214430205015983 109911730194321645307523975)
    ·
      refine ⟨164867595291482467961285963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109911730194321645307523975 164867595291482467961285963)
      ·
        refine ⟨247301392937223701941928945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164867595291482467961285963 247301392937223701941928945)
        ·
          refine ⟨185476044702917776456446709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247301392937223701941928945 185476044702917776456446709)
          ·
            refine ⟨17388379190898541542791879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185476044702917776456446709 17388379190898541542791879)
            ·
              refine ⟨26082568786347812314187819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17388379190898541542791879 26082568786347812314187819)
              ·
                refine ⟨39123853179521718471281729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26082568786347812314187819 39123853179521718471281729)
                ·
                  refine ⟨29342889884641288853461297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39123853179521718471281729 29342889884641288853461297)
                  ·
                    refine ⟨22007167413480966640095973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29342889884641288853461297 22007167413480966640095973)
                    ·
                      refine ⟨4126343890027681245017995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22007167413480966640095973 4126343890027681245017995)
                      ·
                        rfl

theorem cell23_8036026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_8036026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036026 prefixEnd_8036026 := by exact prefixLift 8036026
  have htrace : WordTrace (prefixWord ++ tailWord_8036026) baseStart_8036026 baseEnd_8036026 := by
    simpa [prefixWord, tailWord_8036026, baseEnd_8036026] using wordTrace_append hprefix tailTrace_8036026
  have hstable : (prefixWord ++ tailWord_8036026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036026).length < 2 ^ (prefixWord ++ tailWord_8036026).sum := by decide
  have hdescent : baseEnd_8036026 < baseStart_8036026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036030 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_8036030 : Nat := 118140960795 + 8036030 * 2 ^ 59
def prefixEnd_8036030 : Nat := 4983230072969 + 3 ^ 40 * 8036030 * 2
def baseEnd_8036030 : Nat := 4126345943950299229367977

theorem tailTrace_8036030 : CollatzResearch.WordTrace tailWord_8036030 prefixEnd_8036030 4126345943950299229367977 := by
  unfold tailWord_8036030
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637261634605403687901193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195398728717895486335473029 36637261634605403687901193)
  ·
    refine ⟨27477946225954052765925895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36637261634605403687901193 27477946225954052765925895)
    ·
      refine ⟨41216919338931079148888843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27477946225954052765925895 41216919338931079148888843)
      ·
        refine ⟨61825379008396618723333265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41216919338931079148888843 61825379008396618723333265)
        ·
          refine ⟨46369034256297464042499949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61825379008396618723333265 46369034256297464042499949)
          ·
            refine ⟨17388387846111549015937481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46369034256297464042499949 17388387846111549015937481)
            ·
              refine ⟨13041290884583661761953111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17388387846111549015937481 13041290884583661761953111)
              ·
                refine ⟨19561936326875492642929667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041290884583661761953111 19561936326875492642929667)
                ·
                  refine ⟨29342904490313238964394501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19561936326875492642929667 29342904490313238964394501)
                  ·
                    refine ⟨5501794591933732305823969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29342904490313238964394501 5501794591933732305823969)
                    ·
                      refine ⟨4126345943950299229367977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501794591933732305823969 4126345943950299229367977)
                      ·
                        rfl

theorem cell23_8036030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_8036030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036030 prefixEnd_8036030 := by exact prefixLift 8036030
  have htrace : WordTrace (prefixWord ++ tailWord_8036030) baseStart_8036030 baseEnd_8036030 := by
    simpa [prefixWord, tailWord_8036030, baseEnd_8036030] using wordTrace_append hprefix tailTrace_8036030
  have hstable : (prefixWord ++ tailWord_8036030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036030).length < 2 ^ (prefixWord ++ tailWord_8036030).sum := by decide
  have hdescent : baseEnd_8036030 < baseStart_8036030 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036036 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 7]
def baseStart_8036036 : Nat := 118140960795 + 8036036 * 2 ^ 59
def prefixEnd_8036036 : Nat := 4983230072969 + 3 ^ 40 * 8036036 * 2
def baseEnd_8036036 : Nat := 458483224981580689543661

theorem tailTrace_8036036 : CollatzResearch.WordTrace tailWord_8036036 prefixEnd_8036036 458483224981580689543661 := by
  unfold tailWord_8036036
  simp only [CollatzResearch.WordTrace]
  refine ⟨146549155957410746263963981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195398874609880995018618641 146549155957410746263963981)
  ·
    refine ⟨54955933484029029848986493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146549155957410746263963981 54955933484029029848986493)
    ·
      refine ⟨20608475056510886193369935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54955933484029029848986493 20608475056510886193369935)
      ·
        refine ⟨30912712584766329290054903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20608475056510886193369935 30912712584766329290054903)
        ·
          refine ⟨46369068877149493935082355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30912712584766329290054903 46369068877149493935082355)
          ·
            refine ⟨69553603315724240902623533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46369068877149493935082355 69553603315724240902623533)
            ·
              refine ⟨26082601243396590338483825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69553603315724240902623533 26082601243396590338483825)
              ·
                refine ⟨19561950932547442753862869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26082601243396590338483825 19561950932547442753862869)
                ·
                  refine ⟨458483224981580689543661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19561950932547442753862869 458483224981580689543661)
                  ·
                    rfl

theorem cell23_8036036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_8036036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036036 prefixEnd_8036036 := by exact prefixLift 8036036
  have htrace : WordTrace (prefixWord ++ tailWord_8036036) baseStart_8036036 baseEnd_8036036 := by
    simpa [prefixWord, tailWord_8036036, baseEnd_8036036] using wordTrace_append hprefix tailTrace_8036036
  have hstable : (prefixWord ++ tailWord_8036036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036036).length < 2 ^ (prefixWord ++ tailWord_8036036).sum := by decide
  have hdescent : baseEnd_8036036 < baseStart_8036036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036046 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_8036046 : Nat := 118140960795 + 8036046 * 2 ^ 59
def prefixEnd_8036046 : Nat := 4983230072969 + 3 ^ 40 * 8036046 * 2
def baseEnd_8036046 : Nat := 4126354159640771166767903

theorem tailTrace_8036046 : CollatzResearch.WordTrace tailWord_8036046 prefixEnd_8036046 4126354159640771166767903 := by
  unfold tailWord_8036046
  simp only [CollatzResearch.WordTrace]
  refine ⟨36637334580598158029473999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195399117763190176157194661 36637334580598158029473999)
  ·
    refine ⟨54956001870897237044210999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36637334580598158029473999 54956001870897237044210999)
    ·
      refine ⟨82434002806345855566316499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54956001870897237044210999 82434002806345855566316499)
      ·
        refine ⟨123651004209518783349474749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82434002806345855566316499 123651004209518783349474749)
        ·
          refine ⟨46369126578569543756053031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123651004209518783349474749 46369126578569543756053031)
          ·
            refine ⟨69553689867854315634079547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46369126578569543756053031 69553689867854315634079547)
            ·
              refine ⟨104330534801781473451119321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69553689867854315634079547 104330534801781473451119321)
              ·
                refine ⟨78247901101336105088339491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104330534801781473451119321 78247901101336105088339491)
                ·
                  refine ⟨117371851652004157632509237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78247901101336105088339491 117371851652004157632509237)
                  ·
                    refine ⟨11003611092375389778047741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117371851652004157632509237 11003611092375389778047741)
                    ·
                      refine ⟨4126354159640771166767903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11003611092375389778047741 4126354159640771166767903)
                      ·
                        rfl

theorem cell23_8036046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_8036046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036046 prefixEnd_8036046 := by exact prefixLift 8036046
  have htrace : WordTrace (prefixWord ++ tailWord_8036046) baseStart_8036046 baseEnd_8036046 := by
    simpa [prefixWord, tailWord_8036046, baseEnd_8036046] using wordTrace_append hprefix tailTrace_8036046
  have hstable : (prefixWord ++ tailWord_8036046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036046).length < 2 ^ (prefixWord ++ tailWord_8036046).sum := by decide
  have hdescent : baseEnd_8036046 < baseStart_8036046 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036186 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_8036186 : Nat := 118140960795 + 8036186 * 2 ^ 59
def prefixEnd_8036186 : Nat := 4983230072969 + 3 ^ 40 * 8036186 * 2
def baseEnd_8036186 : Nat := 1375475348977466873005753

theorem tailTrace_8036186 : CollatzResearch.WordTrace tailWord_8036186 prefixEnd_8036186 1375475348977466873005753 := by
  unfold tailWord_8036186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73275945716069517036472103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195402521909518712097258941 73275945716069517036472103)
  ·
    refine ⟨109913918574104275554708155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73275945716069517036472103 109913918574104275554708155)
    ·
      refine ⟨164870877861156413332062233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109913918574104275554708155 164870877861156413332062233)
      ·
        refine ⟨123653158395867309999046675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164870877861156413332062233 123653158395867309999046675)
        ·
          refine ⟨185479737593800964998570013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123653158395867309999046675 185479737593800964998570013)
          ·
            refine ⟨69554901597675361874463755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185479737593800964998570013 69554901597675361874463755)
            ·
              refine ⟨104332352396513042811695633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69554901597675361874463755 104332352396513042811695633)
              ·
                refine ⟨78249264297384782108771725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104332352396513042811695633 78249264297384782108771725)
                ·
                  refine ⟨29343474111519293290789397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78249264297384782108771725 29343474111519293290789397)
                  ·
                    refine ⟨1375475348977466873005753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29343474111519293290789397 1375475348977466873005753)
                    ·
                      rfl

theorem cell23_8036186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_8036186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036186 prefixEnd_8036186 := by exact prefixLift 8036186
  have htrace : WordTrace (prefixWord ++ tailWord_8036186) baseStart_8036186 baseEnd_8036186 := by
    simpa [prefixWord, tailWord_8036186, baseEnd_8036186] using wordTrace_append hprefix tailTrace_8036186
  have hstable : (prefixWord ++ tailWord_8036186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036186).length < 2 ^ (prefixWord ++ tailWord_8036186).sum := by decide
  have hdescent : baseEnd_8036186 < baseStart_8036186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036227 : List Nat := [1, 1, 1, 3, 4, 4, 2, 1, 1, 1, 4]
def baseStart_8036227 : Nat := 118140960795 + 8036227 * 2 ^ 59
def prefixEnd_8036227 : Nat := 4983230072969 + 3 ^ 40 * 8036227 * 2
def baseEnd_8036227 : Nat := 4126447099639234958604571

theorem tailTrace_8036227 : CollatzResearch.WordTrace tailWord_8036227 prefixEnd_8036227 4126447099639234958604571 := by
  unfold tailWord_8036227
  simp only [CollatzResearch.WordTrace]
  refine ⟨293105278257129532148130935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195403518838086354765420623 293105278257129532148130935)
  ·
    refine ⟨439657917385694298222196403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293105278257129532148130935 439657917385694298222196403)
    ·
      refine ⟨659486876078541447333294605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439657917385694298222196403 659486876078541447333294605)
      ·
        refine ⟨247307578529453042749985477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659486876078541447333294605 247307578529453042749985477)
        ·
          refine ⟨46370170974272445515622277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247307578529453042749985477 46370170974272445515622277)
          ·
            refine ⟨8694407057676083534179177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46370170974272445515622277 8694407057676083534179177)
            ·
              refine ⟨6520805293257062650634383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694407057676083534179177 6520805293257062650634383)
              ·
                refine ⟨9781207939885593975951575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6520805293257062650634383 9781207939885593975951575)
                ·
                  refine ⟨14671811909828390963927363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781207939885593975951575 14671811909828390963927363)
                  ·
                    refine ⟨22007717864742586445891045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14671811909828390963927363 22007717864742586445891045)
                    ·
                      refine ⟨4126447099639234958604571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22007717864742586445891045 4126447099639234958604571)
                      ·
                        rfl

theorem cell23_8036227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_8036227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036227 prefixEnd_8036227 := by exact prefixLift 8036227
  have htrace : WordTrace (prefixWord ++ tailWord_8036227) baseStart_8036227 baseEnd_8036227 := by
    simpa [prefixWord, tailWord_8036227, baseEnd_8036227] using wordTrace_append hprefix tailTrace_8036227
  have hstable : (prefixWord ++ tailWord_8036227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036227).length < 2 ^ (prefixWord ++ tailWord_8036227).sum := by decide
  have hdescent : baseEnd_8036227 < baseStart_8036227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036236 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6]
def baseStart_8036236 : Nat := 118140960795 + 8036236 * 2 ^ 59
def prefixEnd_8036236 : Nat := 4983230072969 + 3 ^ 40 * 8036236 * 2
def baseEnd_8036236 : Nat := 4126451720965125423392029

theorem tailTrace_8036236 : CollatzResearch.WordTrace tailWord_8036236 prefixEnd_8036236 4126451720965125423392029 := by
  unfold tailWord_8036236
  simp only [CollatzResearch.WordTrace]
  refine ⟨146552803257048463342604281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195403737676064617790139041 146552803257048463342604281)
  ·
    refine ⟨109914602442786347506953211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146552803257048463342604281 109914602442786347506953211)
    ·
      refine ⟨164871903664179521260429817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109914602442786347506953211 164871903664179521260429817)
      ·
        refine ⟨123653927748134640945322363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164871903664179521260429817 123653927748134640945322363)
        ·
          refine ⟨185480891622201961417983545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123653927748134640945322363 185480891622201961417983545)
          ·
            refine ⟨139110668716651471063487659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185480891622201961417983545 139110668716651471063487659)
            ·
              refine ⟨208666003074977206595231489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139110668716651471063487659 208666003074977206595231489)
              ·
                refine ⟨156499502306232904946423617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208666003074977206595231489 156499502306232904946423617)
                ·
                  refine ⟨117374626729674678709817713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156499502306232904946423617 117374626729674678709817713)
                  ·
                    refine ⟨88030970047256009032363285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117374626729674678709817713 88030970047256009032363285)
                    ·
                      refine ⟨4126451720965125423392029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88030970047256009032363285 4126451720965125423392029)
                      ·
                        rfl

theorem cell23_8036236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_8036236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036236 prefixEnd_8036236 := by exact prefixLift 8036236
  have htrace : WordTrace (prefixWord ++ tailWord_8036236) baseStart_8036236 baseEnd_8036236 := by
    simpa [prefixWord, tailWord_8036236, baseEnd_8036236] using wordTrace_append hprefix tailTrace_8036236
  have hstable : (prefixWord ++ tailWord_8036236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036236).length < 2 ^ (prefixWord ++ tailWord_8036236).sum := by decide
  have hdescent : baseEnd_8036236 < baseStart_8036236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036244 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_8036244 : Nat := 118140960795 + 8036244 * 2 ^ 59
def prefixEnd_8036244 : Nat := 4983230072969 + 3 ^ 40 * 8036244 * 2
def baseEnd_8036244 : Nat := 4126455828810361392091993

theorem tailTrace_8036244 : CollatzResearch.WordTrace tailWord_8036244 prefixEnd_8036244 4126455828810361392091993 := by
  unfold tailWord_8036244
  simp only [CollatzResearch.WordTrace]
  refine ⟨146552949149033972025749893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195403932198711962700999857 146552949149033972025749893)
  ·
    refine ⟨27478677965443869754828105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146552949149033972025749893 27478677965443869754828105)
    ·
      refine ⟨20609008474082902316121079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27478677965443869754828105 20609008474082902316121079)
      ·
        refine ⟨30913512711124353474181619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20609008474082902316121079 30913512711124353474181619)
        ·
          refine ⟨46370269066686530211272429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30913512711124353474181619 46370269066686530211272429)
          ·
            refine ⟨17388850900007448829227161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46370269066686530211272429 17388850900007448829227161)
            ·
              refine ⟨13041638175005586621920371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17388850900007448829227161 13041638175005586621920371)
              ·
                refine ⟨19562457262508379932880557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041638175005586621920371 19562457262508379932880557)
                ·
                  refine ⟨7335921473440642474830209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19562457262508379932880557 7335921473440642474830209)
                  ·
                    refine ⟨5501941105080481856122657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7335921473440642474830209 5501941105080481856122657)
                    ·
                      refine ⟨4126455828810361392091993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5501941105080481856122657 4126455828810361392091993)
                      ·
                        rfl

theorem cell23_8036244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_8036244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036244 prefixEnd_8036244 := by exact prefixLift 8036244
  have htrace : WordTrace (prefixWord ++ tailWord_8036244) baseStart_8036244 baseEnd_8036244 := by
    simpa [prefixWord, tailWord_8036244, baseEnd_8036244] using wordTrace_append hprefix tailTrace_8036244
  have hstable : (prefixWord ++ tailWord_8036244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036244).length < 2 ^ (prefixWord ++ tailWord_8036244).sum := by decide
  have hdescent : baseEnd_8036244 < baseStart_8036244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036254 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_8036254 : Nat := 118140960795 + 8036254 * 2 ^ 59
def prefixEnd_8036254 : Nat := 4983230072969 + 3 ^ 40 * 8036254 * 2
def baseEnd_8036254 : Nat := 1375486987872302117655649

theorem tailTrace_8036254 : CollatzResearch.WordTrace tailWord_8036254 prefixEnd_8036254 1375486987872302117655649 := by
  unfold tailWord_8036254
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638282878503964469920477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195404175352021143839575877 36638282878503964469920477)
  ·
    refine ⟨13739356079438986676220179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36638282878503964469920477 13739356079438986676220179)
    ·
      refine ⟨20609034119158480014330269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13739356079438986676220179 20609034119158480014330269)
      ·
        refine ⟨7728387794684430005373851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20609034119158480014330269 7728387794684430005373851)
        ·
          refine ⟨11592581692026645008060777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728387794684430005373851 11592581692026645008060777)
          ·
            refine ⟨8694436269019983756045583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11592581692026645008060777 8694436269019983756045583)
            ·
              refine ⟨13041654403529975634068375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694436269019983756045583 13041654403529975634068375)
              ·
                refine ⟨19562481605294963451102563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041654403529975634068375 19562481605294963451102563)
                ·
                  refine ⟨29343722407942445176653845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19562481605294963451102563 29343722407942445176653845)
                  ·
                    refine ⟨1375486987872302117655649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29343722407942445176653845 1375486987872302117655649)
                    ·
                      rfl

theorem cell23_8036254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_8036254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036254 prefixEnd_8036254 := by exact prefixLift 8036254
  have htrace : WordTrace (prefixWord ++ tailWord_8036254) baseStart_8036254 baseEnd_8036254 := by
    simpa [prefixWord, tailWord_8036254, baseEnd_8036254] using wordTrace_append hprefix tailTrace_8036254
  have hstable : (prefixWord ++ tailWord_8036254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036254).length < 2 ^ (prefixWord ++ tailWord_8036254).sum := by decide
  have hdescent : baseEnd_8036254 < baseStart_8036254 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036257 : List Nat := [1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_8036257 : Nat := 118140960795 + 8036257 * 2 ^ 59
def prefixEnd_8036257 : Nat := 4983230072969 + 3 ^ 40 * 8036257 * 2
def baseEnd_8036257 : Nat := 4126462504058869841229433

theorem tailTrace_8036257 : CollatzResearch.WordTrace tailWord_8036257 prefixEnd_8036257 4126462504058869841229433 := by
  unfold tailWord_8036257
  simp only [CollatzResearch.WordTrace]
  refine ⟨293106372447020847271723025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195404248298013898181148683 293106372447020847271723025)
  ·
    refine ⟨219829779335265635453792269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293106372447020847271723025 219829779335265635453792269)
    ·
      refine ⟨82436167250724613295172101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219829779335265635453792269 82436167250724613295172101)
      ·
        refine ⟨15456781359510864992844769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82436167250724613295172101 15456781359510864992844769)
        ·
          refine ⟨11592586019633148744633577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15456781359510864992844769 11592586019633148744633577)
          ·
            refine ⟨8694439514724861558475183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11592586019633148744633577 8694439514724861558475183)
            ·
              refine ⟨13041659272087292337712775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694439514724861558475183 13041659272087292337712775)
              ·
                refine ⟨19562488908130938506569163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041659272087292337712775 19562488908130938506569163)
                ·
                  refine ⟨29343733362196407759853745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19562488908130938506569163 29343733362196407759853745)
                  ·
                    refine ⟨22007800021647305819890309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29343733362196407759853745 22007800021647305819890309)
                    ·
                      refine ⟨4126462504058869841229433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22007800021647305819890309 4126462504058869841229433)
                      ·
                        rfl

theorem cell23_8036257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_8036257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036257 prefixEnd_8036257 := by exact prefixLift 8036257
  have htrace : WordTrace (prefixWord ++ tailWord_8036257) baseStart_8036257 baseEnd_8036257 := by
    simpa [prefixWord, tailWord_8036257, baseEnd_8036257] using wordTrace_append hprefix tailTrace_8036257
  have hstable : (prefixWord ++ tailWord_8036257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036257).length < 2 ^ (prefixWord ++ tailWord_8036257).sum := by decide
  have hdescent : baseEnd_8036257 < baseStart_8036257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036260 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 1, 3, 3]
def baseStart_8036260 : Nat := 118140960795 + 8036260 * 2 ^ 59
def prefixEnd_8036260 : Nat := 4983230072969 + 3 ^ 40 * 8036260 * 2
def baseEnd_8036260 : Nat := 4126464044500833329491919

theorem tailTrace_8036260 : CollatzResearch.WordTrace tailWord_8036260 prefixEnd_8036260 4126464044500833329491919 := by
  unfold tailWord_8036260
  simp only [CollatzResearch.WordTrace]
  refine ⟨146553240933004989392041117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195404321244006652522721489 146553240933004989392041117)
  ·
    refine ⟨54957465349876871022015419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146553240933004989392041117 54957465349876871022015419)
    ·
      refine ⟨82436198024815306533023129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54957465349876871022015419 82436198024815306533023129)
      ·
        refine ⟨61827148518611479899767347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82436198024815306533023129 61827148518611479899767347)
        ·
          refine ⟨92740722777917219849651021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61827148518611479899767347 92740722777917219849651021)
          ·
            refine ⟨34777771041718957443619133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92740722777917219849651021 34777771041718957443619133)
            ·
              refine ⟨13041664140644609041357175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34777771041718957443619133 13041664140644609041357175)
              ·
                refine ⟨19562496210966913562035763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13041664140644609041357175 19562496210966913562035763)
                ·
                  refine ⟨29343744316450370343053645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19562496210966913562035763 29343744316450370343053645)
                  ·
                    refine ⟨11003904118668888878645117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29343744316450370343053645 11003904118668888878645117)
                    ·
                      refine ⟨4126464044500833329491919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11003904118668888878645117 4126464044500833329491919)
                      ·
                        rfl

theorem cell23_8036260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_8036260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036260 prefixEnd_8036260 := by exact prefixLift 8036260
  have htrace : WordTrace (prefixWord ++ tailWord_8036260) baseStart_8036260 baseEnd_8036260 := by
    simpa [prefixWord, tailWord_8036260, baseEnd_8036260] using wordTrace_append hprefix tailTrace_8036260
  have hstable : (prefixWord ++ tailWord_8036260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036260).length < 2 ^ (prefixWord ++ tailWord_8036260).sum := by decide
  have hdescent : baseEnd_8036260 < baseStart_8036260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036273 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_8036273 : Nat := 118140960795 + 8036273 * 2 ^ 59
def prefixEnd_8036273 : Nat := 4983230072969 + 3 ^ 40 * 8036273 * 2
def baseEnd_8036273 : Nat := 4126470719749341778629359

theorem tailTrace_8036273 : CollatzResearch.WordTrace tailWord_8036273 prefixEnd_8036273 4126470719749341778629359 := by
  unfold tailWord_8036273
  simp only [CollatzResearch.WordTrace]
  refine ⟨293106956014962882004305473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195404637343308588002870315 293106956014962882004305473)
  ·
    refine ⟨219830217011222161503229105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293106956014962882004305473 219830217011222161503229105)
    ·
      refine ⟨164872662758416621127421829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219830217011222161503229105 164872662758416621127421829)
      ·
        refine ⟨30913624267203116461391593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164872662758416621127421829 30913624267203116461391593)
        ·
          refine ⟨23185218200402337346043695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30913624267203116461391593 23185218200402337346043695)
          ·
            refine ⟨34777827300603506019065543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23185218200402337346043695 34777827300603506019065543)
            ·
              refine ⟨52166740950905259028598315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34777827300603506019065543 52166740950905259028598315)
              ·
                refine ⟨78250111426357888542897473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52166740950905259028598315 78250111426357888542897473)
                ·
                  refine ⟨58687583569768416407173105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78250111426357888542897473 58687583569768416407173105)
                  ·
                    refine ⟨44015687677326312305379829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58687583569768416407173105 44015687677326312305379829)
                    ·
                      refine ⟨4126470719749341778629359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44015687677326312305379829 4126470719749341778629359)
                      ·
                        rfl

theorem cell23_8036273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_8036273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036273 prefixEnd_8036273 := by exact prefixLift 8036273
  have htrace : WordTrace (prefixWord ++ tailWord_8036273) baseStart_8036273 baseEnd_8036273 := by
    simpa [prefixWord, tailWord_8036273, baseEnd_8036273] using wordTrace_append hprefix tailTrace_8036273
  have hstable : (prefixWord ++ tailWord_8036273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036273).length < 2 ^ (prefixWord ++ tailWord_8036273).sum := by decide
  have hdescent : baseEnd_8036273 < baseStart_8036273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036303 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_8036303 : Nat := 118140960795 + 8036303 * 2 ^ 59
def prefixEnd_8036303 : Nat := 4983230072969 + 3 ^ 40 * 8036303 * 2
def baseEnd_8036303 : Nat := 4126486124168976661254221

theorem tailTrace_8036303 : CollatzResearch.WordTrace tailWord_8036303 prefixEnd_8036303 4126486124168976661254221 := by
  unfold tailWord_8036303
  simp only [CollatzResearch.WordTrace]
  refine ⟨293108050204854197127897563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195405366803236131418598375 293108050204854197127897563)
  ·
    refine ⟨439662075307281295691846345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293108050204854197127897563 439662075307281295691846345)
    ·
      refine ⟨329746556480460971768884759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439662075307281295691846345 329746556480460971768884759)
      ·
        refine ⟨494619834720691457653327139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329746556480460971768884759 494619834720691457653327139)
        ·
          refine ⟨741929752081037186479990709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494619834720691457653327139 741929752081037186479990709)
          ·
            refine ⟨69555914257597236232499129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 741929752081037186479990709 69555914257597236232499129)
            ·
              refine ⟨52166935693197927174374347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69555914257597236232499129 52166935693197927174374347)
              ·
                refine ⟨78250403539796890761561521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52166935693197927174374347 78250403539796890761561521)
                ·
                  refine ⟨58687802654847668071171141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78250403539796890761561521 58687802654847668071171141)
                  ·
                    refine ⟨11003962997783937763344589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58687802654847668071171141 11003962997783937763344589)
                    ·
                      refine ⟨4126486124168976661254221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11003962997783937763344589 4126486124168976661254221)
                      ·
                        rfl

theorem cell23_8036303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_8036303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036303 prefixEnd_8036303 := by exact prefixLift 8036303
  have htrace : WordTrace (prefixWord ++ tailWord_8036303) baseStart_8036303 baseEnd_8036303 := by
    simpa [prefixWord, tailWord_8036303, baseEnd_8036303] using wordTrace_append hprefix tailTrace_8036303
  have hstable : (prefixWord ++ tailWord_8036303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036303).length < 2 ^ (prefixWord ++ tailWord_8036303).sum := by decide
  have hdescent : baseEnd_8036303 < baseStart_8036303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036357 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 5]
def baseStart_8036357 : Nat := 118140960795 + 8036357 * 2 ^ 59
def prefixEnd_8036357 : Nat := 4983230072969 + 3 ^ 40 * 8036357 * 2
def baseEnd_8036357 : Nat := 458501539124924383330997

theorem tailTrace_8036357 : CollatzResearch.WordTrace tailWord_8036357 prefixEnd_8036357 458501539124924383330997 := by
  unfold tailWord_8036357
  simp only [CollatzResearch.WordTrace]
  refine ⟨293110019746658564350363325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195406679831105709566908883 293110019746658564350363325)
  ·
    refine ⟨109916257404996961631386247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293110019746658564350363325 109916257404996961631386247)
    ·
      refine ⟨164874386107495442447079371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109916257404996961631386247 164874386107495442447079371)
      ·
        refine ⟨247311579161243163670619057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164874386107495442447079371 247311579161243163670619057)
        ·
          refine ⟨185483684370932372752964293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247311579161243163670619057 185483684370932372752964293)
          ·
            refine ⟨34778190819549819891180805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185483684370932372752964293 34778190819549819891180805)
            ·
              refine ⟨6520910778665591229596401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34778190819549819891180805 6520910778665591229596401)
              ·
                refine ⟨4890683083999193422197301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6520910778665591229596401 4890683083999193422197301)
                ·
                  refine ⟨458501539124924383330997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4890683083999193422197301 458501539124924383330997)
                  ·
                    rfl

theorem cell23_8036357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_8036357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036357 prefixEnd_8036357 := by exact prefixLift 8036357
  have htrace : WordTrace (prefixWord ++ tailWord_8036357) baseStart_8036357 baseEnd_8036357 := by
    simpa [prefixWord, tailWord_8036357, baseEnd_8036357] using wordTrace_append hprefix tailTrace_8036357
  have hstable : (prefixWord ++ tailWord_8036357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036357).length < 2 ^ (prefixWord ++ tailWord_8036357).sum := by decide
  have hdescent : baseEnd_8036357 < baseStart_8036357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036360 : List Nat := [2, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_8036360 : Nat := 118140960795 + 8036360 * 2 ^ 59
def prefixEnd_8036360 : Nat := 4983230072969 + 3 ^ 40 * 8036360 * 2
def baseEnd_8036360 : Nat := 4126515392566282938241459

theorem tailTrace_8036360 : CollatzResearch.WordTrace tailWord_8036360 prefixEnd_8036360 4126515392566282938241459 := by
  unfold tailWord_8036360
  simp only [CollatzResearch.WordTrace]
  refine ⟨146555064582823847931361267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195406752777098463908481689 146555064582823847931361267)
  ·
    refine ⟨219832596874235771897041901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146555064582823847931361267 219832596874235771897041901)
    ·
      refine ⟨82437223827838414461390713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219832596874235771897041901 82437223827838414461390713)
      ·
        refine ⟨61827917870878810846043035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82437223827838414461390713 61827917870878810846043035)
        ·
          refine ⟨92741876806318216269064553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61827917870878810846043035 92741876806318216269064553)
          ·
            refine ⟨69556407604738662201798415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92741876806318216269064553 69556407604738662201798415)
            ·
              refine ⟨104334611407107993302697623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69556407604738662201798415 104334611407107993302697623)
              ·
                refine ⟨156501917110661989954046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104334611407107993302697623 156501917110661989954046435)
                ·
                  refine ⟨234752875665992984931069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156501917110661989954046435 234752875665992984931069653)
                  ·
                    refine ⟨5502020523421710584321945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234752875665992984931069653 5502020523421710584321945)
                    ·
                      refine ⟨4126515392566282938241459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502020523421710584321945 4126515392566282938241459)
                      ·
                        rfl

theorem cell23_8036360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_8036360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036360 prefixEnd_8036360 := by exact prefixLift 8036360
  have htrace : WordTrace (prefixWord ++ tailWord_8036360) baseStart_8036360 baseEnd_8036360 := by
    simpa [prefixWord, tailWord_8036360, baseEnd_8036360] using wordTrace_append hprefix tailTrace_8036360
  have hstable : (prefixWord ++ tailWord_8036360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036360).length < 2 ^ (prefixWord ++ tailWord_8036360).sum := by decide
  have hdescent : baseEnd_8036360 < baseStart_8036360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036363 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5]
def baseStart_8036363 : Nat := 118140960795 + 8036363 * 2 ^ 59
def prefixEnd_8036363 : Nat := 4983230072969 + 3 ^ 40 * 8036363 * 2
def baseEnd_8036363 : Nat := 4126516933008246426503945

theorem tailTrace_8036363 : CollatzResearch.WordTrace tailWord_8036363 prefixEnd_8036363 4126516933008246426503945 := by
  unfold tailWord_8036363
  simp only [CollatzResearch.WordTrace]
  refine ⟨293110238584636827375081743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195406825723091218250054495 293110238584636827375081743)
  ·
    refine ⟨439665357876955241062622615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293110238584636827375081743 439665357876955241062622615)
    ·
      refine ⟨659498036815432861593933923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439665357876955241062622615 659498036815432861593933923)
      ·
        refine ⟨989247055223149292390900885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659498036815432861593933923 989247055223149292390900885)
        ·
          refine ⟨46370955713585123080823479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 989247055223149292390900885 46370955713585123080823479)
          ·
            refine ⟨69556433570377684621235219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46370955713585123080823479 69556433570377684621235219)
            ·
              refine ⟨104334650355566526931852829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69556433570377684621235219 104334650355566526931852829)
              ·
                refine ⟨39125493883337447599444811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104334650355566526931852829 39125493883337447599444811)
                ·
                  refine ⟨58688240825006171399167217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39125493883337447599444811 58688240825006171399167217)
                  ·
                    refine ⟨44016180618754628549375413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58688240825006171399167217 44016180618754628549375413)
                    ·
                      refine ⟨4126516933008246426503945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44016180618754628549375413 4126516933008246426503945)
                      ·
                        rfl

theorem cell23_8036363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 5].length) (baseStart_8036363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036363 prefixEnd_8036363 := by exact prefixLift 8036363
  have htrace : WordTrace (prefixWord ++ tailWord_8036363) baseStart_8036363 baseEnd_8036363 := by
    simpa [prefixWord, tailWord_8036363, baseEnd_8036363] using wordTrace_append hprefix tailTrace_8036363
  have hstable : (prefixWord ++ tailWord_8036363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036363).length < 2 ^ (prefixWord ++ tailWord_8036363).sum := by decide
  have hdescent : baseEnd_8036363 < baseStart_8036363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036403 : List Nat := [1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6]
def baseStart_8036403 : Nat := 118140960795 + 8036403 * 2 ^ 59
def prefixEnd_8036403 : Nat := 4983230072969 + 3 ^ 40 * 8036403 * 2
def baseEnd_8036403 : Nat := 4126537472234426270003761

theorem tailTrace_8036403 : CollatzResearch.WordTrace tailWord_8036403 prefixEnd_8036403 4126537472234426270003761 := by
  unfold tailWord_8036403
  simp only [CollatzResearch.WordTrace]
  refine ⟨293111697504491914206537863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195407798336327942804358575 293111697504491914206537863)
  ·
    refine ⟨439667546256737871309806795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293111697504491914206537863 439667546256737871309806795)
    ·
      refine ⟨659501319385106806964710193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439667546256737871309806795 659501319385106806964710193)
      ·
        refine ⟨494625989538830105223532645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659501319385106806964710193 494625989538830105223532645)
        ·
          refine ⟨92742373038530644729412371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494625989538830105223532645 92742373038530644729412371)
          ·
            refine ⟨139113559557795967094118557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92742373038530644729412371 139113559557795967094118557)
            ·
              refine ⟨52167584834173487660294459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139113559557795967094118557 52167584834173487660294459)
              ·
                refine ⟨78251377251260231490441689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52167584834173487660294459 78251377251260231490441689)
                ·
                  refine ⟨58688532938445173617831267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78251377251260231490441689 58688532938445173617831267)
                  ·
                    refine ⟨88032799407667760426746901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58688532938445173617831267 88032799407667760426746901)
                    ·
                      refine ⟨4126537472234426270003761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88032799407667760426746901 4126537472234426270003761)
                      ·
                        rfl

theorem cell23_8036403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_8036403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036403 prefixEnd_8036403 := by exact prefixLift 8036403
  have htrace : WordTrace (prefixWord ++ tailWord_8036403) baseStart_8036403 baseEnd_8036403 := by
    simpa [prefixWord, tailWord_8036403, baseEnd_8036403] using wordTrace_append hprefix tailTrace_8036403
  have hstable : (prefixWord ++ tailWord_8036403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036403).length < 2 ^ (prefixWord ++ tailWord_8036403).sum := by decide
  have hdescent : baseEnd_8036403 < baseStart_8036403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036410 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3]
def baseStart_8036410 : Nat := 118140960795 + 8036410 * 2 ^ 59
def prefixEnd_8036410 : Nat := 4983230072969 + 3 ^ 40 * 8036410 * 2
def baseEnd_8036410 : Nat := 4126541066599007742616229

theorem tailTrace_8036410 : CollatzResearch.WordTrace tailWord_8036410 prefixEnd_8036410 4126541066599007742616229 := by
  unfold tailWord_8036410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73277988203866638600510671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195407968543644369601361789 73277988203866638600510671)
  ·
    refine ⟨109916982305799957900766007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73277988203866638600510671 109916982305799957900766007)
    ·
      refine ⟨164875473458699936851149011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109916982305799957900766007 164875473458699936851149011)
      ·
        refine ⟨247313210188049905276723517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164875473458699936851149011 247313210188049905276723517)
        ·
          refine ⟨92742453820518714478771319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247313210188049905276723517 92742453820518714478771319)
          ·
            refine ⟨139113680730778071718156979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92742453820518714478771319 139113680730778071718156979)
            ·
              refine ⟨208670521096167107577235469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139113680730778071718156979 208670521096167107577235469)
              ·
                refine ⟨78251445411062665341463301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208670521096167107577235469 78251445411062665341463301)
                ·
                  refine ⟨14672146014574249751524369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78251445411062665341463301 14672146014574249751524369)
                  ·
                    refine ⟨11004109510930687313643277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14672146014574249751524369 11004109510930687313643277)
                    ·
                      refine ⟨4126541066599007742616229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004109510930687313643277 4126541066599007742616229)
                      ·
                        rfl

theorem cell23_8036410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_8036410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036410 prefixEnd_8036410 := by exact prefixLift 8036410
  have htrace : WordTrace (prefixWord ++ tailWord_8036410) baseStart_8036410 baseEnd_8036410 := by
    simpa [prefixWord, tailWord_8036410, baseEnd_8036410] using wordTrace_append hprefix tailTrace_8036410
  have hstable : (prefixWord ++ tailWord_8036410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036410).length < 2 ^ (prefixWord ++ tailWord_8036410).sum := by decide
  have hdescent : baseEnd_8036410 < baseStart_8036410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036417 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 3, 4]
def baseStart_8036417 : Nat := 118140960795 + 8036417 * 2 ^ 59
def prefixEnd_8036417 : Nat := 4983230072969 + 3 ^ 40 * 8036417 * 2
def baseEnd_8036417 : Nat := 1375514886987863071742899

theorem tailTrace_8036417 : CollatzResearch.WordTrace tailWord_8036417 prefixEnd_8036417 1375514886987863071742899 := by
  unfold tailWord_8036417
  simp only [CollatzResearch.WordTrace]
  refine ⟨293112208126441194597547505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195408138750960796398365003 293112208126441194597547505)
  ·
    refine ⟨219834156094830895948160629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293112208126441194597547505 219834156094830895948160629)
    ·
      refine ⟨20609452133890396495140059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219834156094830895948160629 20609452133890396495140059)
      ·
        refine ⟨30914178200835594742710089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20609452133890396495140059 30914178200835594742710089)
        ·
          refine ⟨23185633650626696057032567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30914178200835594742710089 23185633650626696057032567)
          ·
            refine ⟨34778450475940044085548851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23185633650626696057032567 34778450475940044085548851)
            ·
              refine ⟨52167675713910066128323277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34778450475940044085548851 52167675713910066128323277)
              ·
                refine ⟨19562878392716274798121229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52167675713910066128323277 19562878392716274798121229)
                ·
                  refine ⟨7336079397268603049295461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19562878392716274798121229 7336079397268603049295461)
                  ·
                    refine ⟨1375514886987863071742899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336079397268603049295461 1375514886987863071742899)
                    ·
                      rfl

theorem cell23_8036417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_8036417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036417 prefixEnd_8036417 := by exact prefixLift 8036417
  have htrace : WordTrace (prefixWord ++ tailWord_8036417) baseStart_8036417 baseEnd_8036417 := by
    simpa [prefixWord, tailWord_8036417, baseEnd_8036417] using wordTrace_append hprefix tailTrace_8036417
  have hstable : (prefixWord ++ tailWord_8036417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036417).length < 2 ^ (prefixWord ++ tailWord_8036417).sum := by decide
  have hdescent : baseEnd_8036417 < baseStart_8036417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036433 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_8036433 : Nat := 118140960795 + 8036433 * 2 ^ 59
def prefixEnd_8036433 : Nat := 4983230072969 + 3 ^ 40 * 8036433 * 2
def baseEnd_8036433 : Nat := 4126552876654061152628623

theorem tailTrace_8036433 : CollatzResearch.WordTrace tailWord_8036433 prefixEnd_8036433 4126552876654061152628623 := by
  unfold tailWord_8036433
  simp only [CollatzResearch.WordTrace]
  refine ⟨293112791694383229330129953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195408527796255486220086635 293112791694383229330129953)
  ·
    refine ⟨219834593770787421997597465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293112791694383229330129953 219834593770787421997597465)
    ·
      refine ⟨164875945328090566498198099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219834593770787421997597465 164875945328090566498198099)
      ·
        refine ⟨247313917992135849747297149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164875945328090566498198099 247313917992135849747297149)
        ·
          refine ⟨92742719247050943655236431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247313917992135849747297149 92742719247050943655236431)
          ·
            refine ⟨139114078870576415482854647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92742719247050943655236431 139114078870576415482854647)
            ·
              refine ⟨208671118305864623224281971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139114078870576415482854647 208671118305864623224281971)
              ·
                refine ⟨313006677458796934836422957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208671118305864623224281971 313006677458796934836422957)
                ·
                  refine ⟨117377504047048850563658609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 313006677458796934836422957 117377504047048850563658609)
                  ·
                    refine ⟨88033128035286637922743957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117377504047048850563658609 88033128035286637922743957)
                    ·
                      refine ⟨4126552876654061152628623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88033128035286637922743957 4126552876654061152628623)
                      ·
                        rfl

theorem cell23_8036433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_8036433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036433 prefixEnd_8036433 := by exact prefixLift 8036433
  have htrace : WordTrace (prefixWord ++ tailWord_8036433) baseStart_8036433 baseEnd_8036433 := by
    simpa [prefixWord, tailWord_8036433, baseEnd_8036433] using wordTrace_append hprefix tailTrace_8036433
  have hstable : (prefixWord ++ tailWord_8036433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036433).length < 2 ^ (prefixWord ++ tailWord_8036433).sum := by decide
  have hdescent : baseEnd_8036433 < baseStart_8036433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036480 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4]
def baseStart_8036480 : Nat := 118140960795 + 8036480 * 2 ^ 59
def prefixEnd_8036480 : Nat := 4983230072969 + 3 ^ 40 * 8036480 * 2
def baseEnd_8036480 : Nat := 4126577010244822468740907

theorem tailTrace_8036480 : CollatzResearch.WordTrace tailWord_8036480 prefixEnd_8036480 4126577010244822468740907 := by
  unfold tailWord_8036480
  simp only [CollatzResearch.WordTrace]
  refine ⟨146557252962606478178545447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195409670616808637571393929 146557252962606478178545447)
  ·
    refine ⟨219835879443909717267818171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146557252962606478178545447 219835879443909717267818171)
    ·
      refine ⟨329753819165864575901727257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219835879443909717267818171 329753819165864575901727257)
      ·
        refine ⟨247315364374398431926295443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329753819165864575901727257 247315364374398431926295443)
        ·
          refine ⟨370973046561597647889443165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247315364374398431926295443 370973046561597647889443165)
          ·
            refine ⟨139114892460599117958541187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 370973046561597647889443165 139114892460599117958541187)
            ·
              refine ⟨208672338690898676937811781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139114892460599117958541187 208672338690898676937811781)
              ·
                refine ⟨39126063504543501925839709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208672338690898676937811781 39126063504543501925839709)
                ·
                  refine ⟨14672273814203813222189891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39126063504543501925839709 14672273814203813222189891)
                  ·
                    refine ⟨22008410721305719833284837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14672273814203813222189891 22008410721305719833284837)
                    ·
                      refine ⟨4126577010244822468740907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22008410721305719833284837 4126577010244822468740907)
                      ·
                        rfl

theorem cell23_8036480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_8036480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036480 prefixEnd_8036480 := by exact prefixLift 8036480
  have htrace : WordTrace (prefixWord ++ tailWord_8036480) baseStart_8036480 baseEnd_8036480 := by
    simpa [prefixWord, tailWord_8036480, baseEnd_8036480] using wordTrace_append hprefix tailTrace_8036480
  have hstable : (prefixWord ++ tailWord_8036480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036480).length < 2 ^ (prefixWord ++ tailWord_8036480).sum := by decide
  have hdescent : baseEnd_8036480 < baseStart_8036480 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036481 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 6]
def baseStart_8036481 : Nat := 118140960795 + 8036481 * 2 ^ 59
def prefixEnd_8036481 : Nat := 4983230072969 + 3 ^ 40 * 8036481 * 2
def baseEnd_8036481 : Nat := 458508613747275218314267

theorem tailTrace_8036481 : CollatzResearch.WordTrace tailWord_8036481 prefixEnd_8036481 458508613747275218314267 := by
  unfold tailWord_8036481
  simp only [CollatzResearch.WordTrace]
  refine ⟨293114542398209333527877297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195409694932139555685251531 293114542398209333527877297)
  ·
    refine ⟨219835906798657000145907973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293114542398209333527877297 219835906798657000145907973)
    ·
      refine ⟨41219232524748187527357745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219835906798657000145907973 41219232524748187527357745)
      ·
        refine ⟨30914424393561140645518309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41219232524748187527357745 30914424393561140645518309)
        ·
          refine ⟨5796454573792713871034683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30914424393561140645518309 5796454573792713871034683)
          ·
            refine ⟨8694681860689070806552025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796454573792713871034683 8694681860689070806552025)
            ·
              refine ⟨6521011395516803104914019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694681860689070806552025 6521011395516803104914019)
              ·
                refine ⟨9781517093275204657371029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521011395516803104914019 9781517093275204657371029)
                ·
                  refine ⟨458508613747275218314267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9781517093275204657371029 458508613747275218314267)
                  ·
                    rfl

theorem cell23_8036481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 6].length) (baseStart_8036481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036481 prefixEnd_8036481 := by exact prefixLift 8036481
  have htrace : WordTrace (prefixWord ++ tailWord_8036481) baseStart_8036481 baseEnd_8036481 := by
    simpa [prefixWord, tailWord_8036481, baseEnd_8036481] using wordTrace_append hprefix tailTrace_8036481
  have hstable : (prefixWord ++ tailWord_8036481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036481).length < 2 ^ (prefixWord ++ tailWord_8036481).sum := by decide
  have hdescent : baseEnd_8036481 < baseStart_8036481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036525 : List Nat := [1, 5, 2, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_8036525 : Nat := 118140960795 + 8036525 * 2 ^ 59
def prefixEnd_8036525 : Nat := 4983230072969 + 3 ^ 40 * 8036525 * 2
def baseEnd_8036525 : Nat := 4126600116874274792678201

theorem tailTrace_8036525 : CollatzResearch.WordTrace tailWord_8036525 prefixEnd_8036525 4126600116874274792678201 := by
  unfold tailWord_8036525
  simp only [CollatzResearch.WordTrace]
  refine ⟨293116147210049929042479029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195410764806699952694986019 293116147210049929042479029)
  ·
    refine ⟨27479638800942180847732409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293116147210049929042479029 27479638800942180847732409)
    ·
      refine ⟨20609729100706635635799307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27479638800942180847732409 20609729100706635635799307)
      ·
        refine ⟨30914593651059953453698961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20609729100706635635799307 30914593651059953453698961)
        ·
          refine ⟨23185945238294965090274221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30914593651059953453698961 23185945238294965090274221)
          ·
            refine ⟨8694729464360611908852833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23185945238294965090274221 8694729464360611908852833)
            ·
              refine ⟨6521047098270458931639625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8694729464360611908852833 6521047098270458931639625)
              ·
                refine ⟨4890785323702844198729719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521047098270458931639625 4890785323702844198729719)
                ·
                  refine ⟨7336177985554266298094579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890785323702844198729719 7336177985554266298094579)
                  ·
                    refine ⟨11004266978331399447141869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336177985554266298094579 11004266978331399447141869)
                    ·
                      refine ⟨4126600116874274792678201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004266978331399447141869 4126600116874274792678201)
                      ·
                        rfl

theorem cell23_8036525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_8036525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036525 prefixEnd_8036525 := by exact prefixLift 8036525
  have htrace : WordTrace (prefixWord ++ tailWord_8036525) baseStart_8036525 baseEnd_8036525 := by
    simpa [prefixWord, tailWord_8036525, baseEnd_8036525] using wordTrace_append hprefix tailTrace_8036525
  have hstable : (prefixWord ++ tailWord_8036525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036525).length < 2 ^ (prefixWord ++ tailWord_8036525).sum := by decide
  have hdescent : baseEnd_8036525 < baseStart_8036525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036565 : List Nat := [1, 3, 2, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_8036565 : Nat := 118140960795 + 8036565 * 2 ^ 59
def prefixEnd_8036565 : Nat := 4983230072969 + 3 ^ 40 * 8036565 * 2
def baseEnd_8036565 : Nat := 4126620656100454636178017

theorem tailTrace_8036565 : CollatzResearch.WordTrace tailWord_8036565 prefixEnd_8036565 4126620656100454636178017 := by
  unfold tailWord_8036565
  simp only [CollatzResearch.WordTrace]
  refine ⟨293117606129905015873935149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195411737419936677249290099 293117606129905015873935149)
  ·
    refine ⟨109919102298714380952725681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293117606129905015873935149 109919102298714380952725681)
    ·
      refine ⟨82439326724035785714544261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109919102298714380952725681 82439326724035785714544261)
      ·
        refine ⟨15457373760756709821477049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82439326724035785714544261 15457373760756709821477049)
        ·
          refine ⟨11593030320567532366107787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15457373760756709821477049 11593030320567532366107787)
          ·
            refine ⟨17389545480851298549161681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593030320567532366107787 17389545480851298549161681)
            ·
              refine ⟨13042159110638473911871261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17389545480851298549161681 13042159110638473911871261)
              ·
                refine ⟨4890809666489427716951723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042159110638473911871261 4890809666489427716951723)
                ·
                  refine ⟨7336214499734141575427585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890809666489427716951723 7336214499734141575427585)
                  ·
                    refine ⟨5502160874800606181570689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336214499734141575427585 5502160874800606181570689)
                    ·
                      refine ⟨4126620656100454636178017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502160874800606181570689 4126620656100454636178017)
                      ·
                        rfl

theorem cell23_8036565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_8036565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036565 prefixEnd_8036565 := by exact prefixLift 8036565
  have htrace : WordTrace (prefixWord ++ tailWord_8036565) baseStart_8036565 baseEnd_8036565 := by
    simpa [prefixWord, tailWord_8036565, baseEnd_8036565] using wordTrace_append hprefix tailTrace_8036565
  have hstable : (prefixWord ++ tailWord_8036565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036565).length < 2 ^ (prefixWord ++ tailWord_8036565).sum := by decide
  have hdescent : baseEnd_8036565 < baseStart_8036565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036581 : List Nat := [1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_8036581 : Nat := 118140960795 + 8036581 * 2 ^ 59
def prefixEnd_8036581 : Nat := 4983230072969 + 3 ^ 40 * 8036581 * 2
def baseEnd_8036581 : Nat := 4126628871790926573577943

theorem tailTrace_8036581 : CollatzResearch.WordTrace tailWord_8036581 prefixEnd_8036581 4126628871790926573577943 := by
  unfold tailWord_8036581
  simp only [CollatzResearch.WordTrace]
  refine ⟨293118189697847050606517597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195412126465231367071011731 293118189697847050606517597)
  ·
    refine ⟨109919321136692643977444099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293118189697847050606517597 109919321136692643977444099)
    ·
      refine ⟨164878981705038965966166149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109919321136692643977444099 164878981705038965966166149)
      ·
        refine ⟨30914809069694806118656153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164878981705038965966166149 30914809069694806118656153)
        ·
          refine ⟨23186106802271104588992115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30914809069694806118656153 23186106802271104588992115)
          ·
            refine ⟨34779160203406656883488173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23186106802271104588992115 34779160203406656883488173)
            ·
              refine ⟨13042185076277496331308065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34779160203406656883488173 13042185076277496331308065)
              ·
                refine ⟨9781638807208122248481049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13042185076277496331308065 9781638807208122248481049)
                ·
                  refine ⟨7336229105406091686360787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9781638807208122248481049 7336229105406091686360787)
                  ·
                    refine ⟨11004343658109137529541181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336229105406091686360787 11004343658109137529541181)
                    ·
                      refine ⟨4126628871790926573577943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004343658109137529541181 4126628871790926573577943)
                      ·
                        rfl

theorem cell23_8036581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_8036581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036581 prefixEnd_8036581 := by exact prefixLift 8036581
  have htrace : WordTrace (prefixWord ++ tailWord_8036581) baseStart_8036581 baseEnd_8036581 := by
    simpa [prefixWord, tailWord_8036581, baseEnd_8036581] using wordTrace_append hprefix tailTrace_8036581
  have hstable : (prefixWord ++ tailWord_8036581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036581).length < 2 ^ (prefixWord ++ tailWord_8036581).sum := by decide
  have hdescent : baseEnd_8036581 < baseStart_8036581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036644 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 7]
def baseStart_8036644 : Nat := 118140960795 + 8036644 * 2 ^ 59
def prefixEnd_8036644 : Nat := 4983230072969 + 3 ^ 40 * 8036644 * 2
def baseEnd_8036644 : Nat := 458517913452462203010017

theorem tailTrace_8036644 : CollatzResearch.WordTrace tailWord_8036644 prefixEnd_8036644 458517913452462203010017 := by
  unfold tailWord_8036644
  simp only [CollatzResearch.WordTrace]
  refine ⟨146560243748309406183030493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195413658331079208244040657 146560243748309406183030493)
  ·
    refine ⟨54960091405616027318636435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146560243748309406183030493 54960091405616027318636435)
    ·
      refine ⟨82440137108424040977954653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54960091405616027318636435 82440137108424040977954653)
      ·
        refine ⟨30915051415659015366732995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82440137108424040977954653 30915051415659015366732995)
        ·
          refine ⟨46372577123488523050099493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30915051415659015366732995 46372577123488523050099493)
          ·
            refine ⟨8694858210654098071893655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46372577123488523050099493 8694858210654098071893655)
            ·
              refine ⟨13042287315981147107840483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694858210654098071893655 13042287315981147107840483)
              ·
                refine ⟨19563430973971720661760725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042287315981147107840483 19563430973971720661760725)
                ·
                  refine ⟨458517913452462203010017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19563430973971720661760725 458517913452462203010017)
                  ·
                    rfl

theorem cell23_8036644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_8036644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036644 prefixEnd_8036644 := by exact prefixLift 8036644
  have htrace : WordTrace (prefixWord ++ tailWord_8036644) baseStart_8036644 baseEnd_8036644 := by
    simpa [prefixWord, tailWord_8036644, baseEnd_8036644] using wordTrace_append hprefix tailTrace_8036644
  have hstable : (prefixWord ++ tailWord_8036644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036644).length < 2 ^ (prefixWord ++ tailWord_8036644).sum := by decide
  have hdescent : baseEnd_8036644 < baseStart_8036644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036687 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 7, 4]
def baseStart_8036687 : Nat := 118140960795 + 8036687 * 2 ^ 59
def prefixEnd_8036687 : Nat := 4983230072969 + 3 ^ 40 * 8036687 * 2
def baseEnd_8036687 : Nat := 1375561100246767719617485

theorem tailTrace_8036687 : CollatzResearch.WordTrace tailWord_8036687 prefixEnd_8036687 1375561100246767719617485 := by
  unfold tailWord_8036687
  simp only [CollatzResearch.WordTrace]
  refine ⟨293122055835463030709876315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195414703890308687139917543 293122055835463030709876315)
  ·
    refine ⟨439683083753194546064814473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293122055835463030709876315 439683083753194546064814473)
    ·
      refine ⟨329762312814895909548610855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439683083753194546064814473 329762312814895909548610855)
      ·
        refine ⟨494643469222343864322916283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329762312814895909548610855 494643469222343864322916283)
        ·
          refine ⟨741965203833515796484374425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494643469222343864322916283 741965203833515796484374425)
          ·
            refine ⟨556473902875136847363280819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741965203833515796484374425 556473902875136847363280819)
            ·
              refine ⟨834710854312705271044921229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556473902875136847363280819 834710854312705271044921229)
              ·
                refine ⟨313016570367264476641845461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834710854312705271044921229 313016570367264476641845461)
                ·
                  refine ⟨7336325867982761171293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 313016570367264476641845461 7336325867982761171293253)
                  ·
                    refine ⟨1375561100246767719617485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336325867982761171293253 1375561100246767719617485)
                    ·
                      rfl

theorem cell23_8036687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 7, 4].length) (baseStart_8036687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036687 prefixEnd_8036687 := by exact prefixLift 8036687
  have htrace : WordTrace (prefixWord ++ tailWord_8036687) baseStart_8036687 baseEnd_8036687 := by
    simpa [prefixWord, tailWord_8036687, baseEnd_8036687] using wordTrace_append hprefix tailTrace_8036687
  have hstable : (prefixWord ++ tailWord_8036687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036687).length < 2 ^ (prefixWord ++ tailWord_8036687).sum := by decide
  have hdescent : baseEnd_8036687 < baseStart_8036687 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036697 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 3]
def baseStart_8036697 : Nat := 118140960795 + 8036697 * 2 ^ 59
def prefixEnd_8036697 : Nat := 4983230072969 + 3 ^ 40 * 8036697 * 2
def baseEnd_8036697 : Nat := 4126688435546848119727409

theorem tailTrace_8036697 : CollatzResearch.WordTrace tailWord_8036697 prefixEnd_8036697 4126688435546848119727409 := by
  unfold tailWord_8036697
  simp only [CollatzResearch.WordTrace]
  refine ⟨293122420565426802417740345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195414947043617868278493563 293122420565426802417740345)
  ·
    refine ⟨219841815424070101813305259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293122420565426802417740345 219841815424070101813305259)
    ·
      refine ⟨329762723136105152719957889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219841815424070101813305259 329762723136105152719957889)
      ·
        refine ⟨247322042352078864539968417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329762723136105152719957889 247322042352078864539968417)
        ·
          refine ⟨185491531764059148404976313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247322042352078864539968417 185491531764059148404976313)
          ·
            refine ⟨139118648823044361303732235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185491531764059148404976313 139118648823044361303732235)
            ·
              refine ⟨208677973234566541955598353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139118648823044361303732235 208677973234566541955598353)
              ·
                refine ⟨156508479925924906466698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208677973234566541955598353 156508479925924906466698765)
                ·
                  refine ⟨58690679972221839925012037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156508479925924906466698765 58690679972221839925012037)
                  ·
                    refine ⟨11004502494791594985939757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58690679972221839925012037 11004502494791594985939757)
                    ·
                      refine ⟨4126688435546848119727409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004502494791594985939757 4126688435546848119727409)
                      ·
                        rfl

theorem cell23_8036697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_8036697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036697 prefixEnd_8036697 := by exact prefixLift 8036697
  have htrace : WordTrace (prefixWord ++ tailWord_8036697) baseStart_8036697 baseEnd_8036697 := by
    simpa [prefixWord, tailWord_8036697, baseEnd_8036697] using wordTrace_append hprefix tailTrace_8036697
  have hstable : (prefixWord ++ tailWord_8036697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036697).length < 2 ^ (prefixWord ++ tailWord_8036697).sum := by decide
  have hdescent : baseEnd_8036697 < baseStart_8036697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036711 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_8036711 : Nat := 118140960795 + 8036711 * 2 ^ 59
def prefixEnd_8036711 : Nat := 4983230072969 + 3 ^ 40 * 8036711 * 2
def baseEnd_8036711 : Nat := 4126695624276011064952345

theorem tailTrace_8036711 : CollatzResearch.WordTrace tailWord_8036711 prefixEnd_8036711 4126695624276011064952345 := by
  unfold tailWord_8036711
  simp only [CollatzResearch.WordTrace]
  refine ⟨293122931187376082808749987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195415287458250721872499991 293122931187376082808749987)
  ·
    refine ⟨439684396781064124213124981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293122931187376082808749987 439684396781064124213124981)
    ·
      refine ⟨41220412198224761644980467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439684396781064124213124981 41220412198224761644980467)
      ·
        refine ⟨61830618297337142467470701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41220412198224761644980467 61830618297337142467470701)
        ·
          refine ⟨23186481861501428425301513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61830618297337142467470701 23186481861501428425301513)
          ·
            refine ⟨17389861396126071318976135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23186481861501428425301513 17389861396126071318976135)
            ·
              refine ⟨26084792094189106978464203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17389861396126071318976135 26084792094189106978464203)
              ·
                refine ⟨39127188141283660467696305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26084792094189106978464203 39127188141283660467696305)
                ·
                  refine ⟨29345391105962745350772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39127188141283660467696305 29345391105962745350772229)
                  ·
                    refine ⟨5502260832368014753269793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29345391105962745350772229 5502260832368014753269793)
                    ·
                      refine ⟨4126695624276011064952345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502260832368014753269793 4126695624276011064952345)
                      ·
                        rfl

theorem cell23_8036711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_8036711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036711 prefixEnd_8036711 := by exact prefixLift 8036711
  have htrace : WordTrace (prefixWord ++ tailWord_8036711) baseStart_8036711 baseEnd_8036711 := by
    simpa [prefixWord, tailWord_8036711, baseEnd_8036711] using wordTrace_append hprefix tailTrace_8036711
  have hstable : (prefixWord ++ tailWord_8036711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036711).length < 2 ^ (prefixWord ++ tailWord_8036711).sum := by decide
  have hdescent : baseEnd_8036711 < baseStart_8036711 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036727 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3]
def baseStart_8036727 : Nat := 118140960795 + 8036727 * 2 ^ 59
def prefixEnd_8036727 : Nat := 4983230072969 + 3 ^ 40 * 8036727 * 2
def baseEnd_8036727 : Nat := 4126703839966483002352271

theorem tailTrace_8036727 : CollatzResearch.WordTrace tailWord_8036727 prefixEnd_8036727 4126703839966483002352271 := by
  unfold tailWord_8036727
  simp only [CollatzResearch.WordTrace]
  refine ⟨293123514755318117541332435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195415676503545411694221623 293123514755318117541332435)
  ·
    refine ⟨439685272132977176311998653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293123514755318117541332435 439685272132977176311998653)
    ·
      refine ⟨164881977049866441116999495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439685272132977176311998653 164881977049866441116999495)
      ·
        refine ⟨247322965574799661675499243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164881977049866441116999495 247322965574799661675499243)
        ·
          refine ⟨370984448362199492513248865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247322965574799661675499243 370984448362199492513248865)
          ·
            refine ⟨278238336271649619384936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370984448362199492513248865 278238336271649619384936649)
            ·
              refine ⟨208678752203737214538702487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278238336271649619384936649 208678752203737214538702487)
              ·
                refine ⟨313018128305605821808053731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208678752203737214538702487 313018128305605821808053731)
                ·
                  refine ⟨469527192458408732712080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313018128305605821808053731 469527192458408732712080597)
                  ·
                    refine ⟨11004543573243954672939389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 469527192458408732712080597 11004543573243954672939389)
                    ·
                      refine ⟨4126703839966483002352271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004543573243954672939389 4126703839966483002352271)
                      ·
                        rfl

theorem cell23_8036727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_8036727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036727 prefixEnd_8036727 := by exact prefixLift 8036727
  have htrace : WordTrace (prefixWord ++ tailWord_8036727) baseStart_8036727 baseEnd_8036727 := by
    simpa [prefixWord, tailWord_8036727, baseEnd_8036727] using wordTrace_append hprefix tailTrace_8036727
  have hstable : (prefixWord ++ tailWord_8036727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036727).length < 2 ^ (prefixWord ++ tailWord_8036727).sum := by decide
  have hdescent : baseEnd_8036727 < baseStart_8036727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036731 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 3]
def baseStart_8036731 : Nat := 118140960795 + 8036731 * 2 ^ 59
def prefixEnd_8036731 : Nat := 4983230072969 + 3 ^ 40 * 8036731 * 2
def baseEnd_8036731 : Nat := 4126705893889100986702253

theorem tailTrace_8036731 : CollatzResearch.WordTrace tailWord_8036731 prefixEnd_8036731 4126705893889100986702253 := by
  unfold tailWord_8036731
  simp only [CollatzResearch.WordTrace]
  refine ⟨293123660647303626224478047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195415773764869084149652031 293123660647303626224478047)
  ·
    refine ⟨439685490970955439336717071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293123660647303626224478047 439685490970955439336717071)
    ·
      refine ⟨659528236456433159005075607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439685490970955439336717071 659528236456433159005075607)
      ·
        refine ⟨989292354684649738507613411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659528236456433159005075607 989292354684649738507613411)
        ·
          refine ⟨1483938532026974607761420117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989292354684649738507613411 1483938532026974607761420117)
          ·
            refine ⟨8694952336095554342352071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1483938532026974607761420117 8694952336095554342352071)
            ·
              refine ⟨13042428504143331513528107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8694952336095554342352071 13042428504143331513528107)
              ·
                refine ⟨19563642756214997270292161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042428504143331513528107 19563642756214997270292161)
                ·
                  refine ⟨14672732067161247952719121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19563642756214997270292161 14672732067161247952719121)
                  ·
                    refine ⟨11004549050370935964539341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14672732067161247952719121 11004549050370935964539341)
                    ·
                      refine ⟨4126705893889100986702253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004549050370935964539341 4126705893889100986702253)
                      ·
                        rfl

theorem cell23_8036731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 3].length) (baseStart_8036731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036731 prefixEnd_8036731 := by exact prefixLift 8036731
  have htrace : WordTrace (prefixWord ++ tailWord_8036731) baseStart_8036731 baseEnd_8036731 := by
    simpa [prefixWord, tailWord_8036731, baseEnd_8036731] using wordTrace_append hprefix tailTrace_8036731
  have hstable : (prefixWord ++ tailWord_8036731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036731).length < 2 ^ (prefixWord ++ tailWord_8036731).sum := by decide
  have hdescent : baseEnd_8036731 < baseStart_8036731 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036761 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 3]
def baseStart_8036761 : Nat := 118140960795 + 8036761 * 2 ^ 59
def prefixEnd_8036761 : Nat := 4983230072969 + 3 ^ 40 * 8036761 * 2
def baseEnd_8036761 : Nat := 4126721298308735869327115

theorem tailTrace_8036761 : CollatzResearch.WordTrace tailWord_8036761 prefixEnd_8036761 4126721298308735869327115 := by
  unfold tailWord_8036761
  simp only [CollatzResearch.WordTrace]
  refine ⟨293124754837194941348070137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195416503224796627565380091 293124754837194941348070137)
  ·
    refine ⟨219843566127896206011052603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293124754837194941348070137 219843566127896206011052603)
    ·
      refine ⟨329765349191844309016578905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219843566127896206011052603 329765349191844309016578905)
      ·
        refine ⟨247324011893883231762434179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329765349191844309016578905 247324011893883231762434179)
        ·
          refine ⟨370986017840824847643651269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247324011893883231762434179 370986017840824847643651269)
          ·
            refine ⟨69559878345154658933184613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 370986017840824847643651269 69559878345154658933184613)
            ·
              refine ⟨13042477189716498549972115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69559878345154658933184613 13042477189716498549972115)
              ·
                refine ⟨19563715784574747824958173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042477189716498549972115 19563715784574747824958173)
                ·
                  refine ⟨7336393419215530434359315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19563715784574747824958173 7336393419215530434359315)
                  ·
                    refine ⟨11004590128823295651538973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336393419215530434359315 11004590128823295651538973)
                    ·
                      refine ⟨4126721298308735869327115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004590128823295651538973 4126721298308735869327115)
                      ·
                        rfl

theorem cell23_8036761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 3, 1, 3].length) (baseStart_8036761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036761 prefixEnd_8036761 := by exact prefixLift 8036761
  have htrace : WordTrace (prefixWord ++ tailWord_8036761) baseStart_8036761 baseEnd_8036761 := by
    simpa [prefixWord, tailWord_8036761, baseEnd_8036761] using wordTrace_append hprefix tailTrace_8036761
  have hstable : (prefixWord ++ tailWord_8036761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036761).length < 2 ^ (prefixWord ++ tailWord_8036761).sum := by decide
  have hdescent : baseEnd_8036761 < baseStart_8036761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036807 : List Nat := [1, 1, 4, 1, 1, 4, 11]
def baseStart_8036807 : Nat := 118140960795 + 8036807 * 2 ^ 59
def prefixEnd_8036807 : Nat := 4983230072969 + 3 ^ 40 * 8036807 * 2
def baseEnd_8036807 : Nat := 50947468128627687522863

theorem tailTrace_8036807 : CollatzResearch.WordTrace tailWord_8036807 prefixEnd_8036807 50947468128627687522863 := by
  unfold tailWord_8036807
  simp only [CollatzResearch.WordTrace]
  refine ⟨293126432595028291204244675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195417621730018860802829783 293126432595028291204244675)
  ·
    refine ⟨439689648892542436806367013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293126432595028291204244675 439689648892542436806367013)
    ·
      refine ⟨82441809167351706901193815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439689648892542436806367013 82441809167351706901193815)
      ·
        refine ⟨123662713751027560351790723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82441809167351706901193815 123662713751027560351790723)
        ·
          refine ⟨185494070626541340527686085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123662713751027560351790723 185494070626541340527686085)
          ·
            refine ⟨34780138242476501348941141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185494070626541340527686085 34780138242476501348941141)
            ·
              refine ⟨50947468128627687522863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 34780138242476501348941141 50947468128627687522863)
              ·
                rfl

theorem cell23_8036807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 11].length) (baseStart_8036807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036807 prefixEnd_8036807 := by exact prefixLift 8036807
  have htrace : WordTrace (prefixWord ++ tailWord_8036807) baseStart_8036807 baseEnd_8036807 := by
    simpa [prefixWord, tailWord_8036807, baseEnd_8036807] using wordTrace_append hprefix tailTrace_8036807
  have hstable : (prefixWord ++ tailWord_8036807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036807).length < 2 ^ (prefixWord ++ tailWord_8036807).sum := by decide
  have hdescent : baseEnd_8036807 < baseStart_8036807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036812 : List Nat := [2, 2, 1, 4, 3, 1, 3, 2, 1, 1, 3]
def baseStart_8036812 : Nat := 118140960795 + 8036812 * 2 ^ 59
def prefixEnd_8036812 : Nat := 4983230072969 + 3 ^ 40 * 8036812 * 2
def baseEnd_8036812 : Nat := 4126747485822115169789381

theorem tailTrace_8036812 : CollatzResearch.WordTrace tailWord_8036812 prefixEnd_8036812 4126747485822115169789381 := by
  unfold tailWord_8036812
  simp only [CollatzResearch.WordTrace]
  refine ⟨146563307480005088529088345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195417743306673451372117793 146563307480005088529088345)
  ·
    refine ⟨109922480610003816396816259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146563307480005088529088345 109922480610003816396816259)
    ·
      refine ⟨164883720915005724595224389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109922480610003816396816259 164883720915005724595224389)
      ·
        refine ⟨30915697671563573361604573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164883720915005724595224389 30915697671563573361604573)
        ·
          refine ⟨11593386626836340010601715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30915697671563573361604573 11593386626836340010601715)
          ·
            refine ⟨17390079940254510015902573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593386626836340010601715 17390079940254510015902573)
            ·
              refine ⟨6521279977595441255963465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17390079940254510015902573 6521279977595441255963465)
              ·
                refine ⟨4890959983196580941972599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521279977595441255963465 4890959983196580941972599)
                ·
                  refine ⟨7336439974794871412958899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4890959983196580941972599 7336439974794871412958899)
                  ·
                    refine ⟨11004659962192307119438349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336439974794871412958899 11004659962192307119438349)
                    ·
                      refine ⟨4126747485822115169789381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004659962192307119438349 4126747485822115169789381)
                      ·
                        rfl

theorem cell23_8036812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_8036812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036812 prefixEnd_8036812 := by exact prefixLift 8036812
  have htrace : WordTrace (prefixWord ++ tailWord_8036812) baseStart_8036812 baseEnd_8036812 := by
    simpa [prefixWord, tailWord_8036812, baseEnd_8036812] using wordTrace_append hprefix tailTrace_8036812
  have hstable : (prefixWord ++ tailWord_8036812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036812).length < 2 ^ (prefixWord ++ tailWord_8036812).sum := by decide
  have hdescent : baseEnd_8036812 < baseStart_8036812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036835 : List Nat := [1, 1, 1, 6, 4, 1, 1, 2, 1, 1, 4]
def baseStart_8036835 : Nat := 118140960795 + 8036835 * 2 ^ 59
def prefixEnd_8036835 : Nat := 4983230072969 + 3 ^ 40 * 8036835 * 2
def baseEnd_8036835 : Nat := 4126759295877168579801775

theorem tailTrace_8036835 : CollatzResearch.WordTrace tailWord_8036835 prefixEnd_8036835 4126759295877168579801775 := by
  unfold tailWord_8036835
  simp only [CollatzResearch.WordTrace]
  refine ⟨293127453838926851986263959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195418302559284567990842639 293127453838926851986263959)
  ·
    refine ⟨439691180758390277979395939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293127453838926851986263959 439691180758390277979395939)
    ·
      refine ⟨659536771137585416969093909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439691180758390277979395939 659536771137585416969093909)
      ·
        refine ⟨30915786147074316420426277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 659536771137585416969093909 30915786147074316420426277)
        ·
          refine ⟨5796709902576434328829927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30915786147074316420426277 5796709902576434328829927)
          ·
            refine ⟨8695064853864651493244891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796709902576434328829927 8695064853864651493244891)
            ·
              refine ⟨13042597280796977239867337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695064853864651493244891 13042597280796977239867337)
              ·
                refine ⟨9781947960597732929900503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13042597280796977239867337 9781947960597732929900503)
                ·
                  refine ⟨14672921940896599394850755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9781947960597732929900503 14672921940896599394850755)
                  ·
                    refine ⟨22009382911344899092276133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14672921940896599394850755 22009382911344899092276133)
                    ·
                      refine ⟨4126759295877168579801775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22009382911344899092276133 4126759295877168579801775)
                      ·
                        rfl

theorem cell23_8036835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_8036835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036835 prefixEnd_8036835 := by exact prefixLift 8036835
  have htrace : WordTrace (prefixWord ++ tailWord_8036835) baseStart_8036835 baseEnd_8036835 := by
    simpa [prefixWord, tailWord_8036835, baseEnd_8036835] using wordTrace_append hprefix tailTrace_8036835
  have hstable : (prefixWord ++ tailWord_8036835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036835).length < 2 ^ (prefixWord ++ tailWord_8036835).sum := by decide
  have hdescent : baseEnd_8036835 < baseStart_8036835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036874 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_8036874 : Nat := 118140960795 + 8036874 * 2 ^ 59
def prefixEnd_8036874 : Nat := 4983230072969 + 3 ^ 40 * 8036874 * 2
def baseEnd_8036874 : Nat := 4126779321622693927214095

theorem tailTrace_8036874 : CollatzResearch.WordTrace tailWord_8036874 prefixEnd_8036874 4126779321622693927214095 := by
  unfold tailWord_8036874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73282219071446390411733419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195419250857190374431289117 73282219071446390411733419)
  ·
    refine ⟨109923328607169585617600129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73282219071446390411733419 109923328607169585617600129)
    ·
      refine ⟨82442496455377189213200097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109923328607169585617600129 82442496455377189213200097)
      ·
        refine ⟨61831872341532891909900073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82442496455377189213200097 61831872341532891909900073)
        ·
          refine ⟨46373904256149668932425055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61831872341532891909900073 46373904256149668932425055)
          ·
            refine ⟨69560856384224503398637583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46373904256149668932425055 69560856384224503398637583)
            ·
              refine ⟨104341284576336755097956375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69560856384224503398637583 104341284576336755097956375)
              ·
                refine ⟨156511926864505132646934563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104341284576336755097956375 156511926864505132646934563)
                ·
                  refine ⟨234767890296757698970401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156511926864505132646934563 234767890296757698970401845)
                  ·
                    refine ⟨22009489715321034278475173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234767890296757698970401845 22009489715321034278475173)
                    ·
                      refine ⟨4126779321622693927214095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22009489715321034278475173 4126779321622693927214095)
                      ·
                        rfl

theorem cell23_8036874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_8036874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036874 prefixEnd_8036874 := by exact prefixLift 8036874
  have htrace : WordTrace (prefixWord ++ tailWord_8036874) baseStart_8036874 baseEnd_8036874 := by
    simpa [prefixWord, tailWord_8036874, baseEnd_8036874] using wordTrace_append hprefix tailTrace_8036874
  have hstable : (prefixWord ++ tailWord_8036874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036874).length < 2 ^ (prefixWord ++ tailWord_8036874).sum := by decide
  have hdescent : baseEnd_8036874 < baseStart_8036874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036878 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_8036878 : Nat := 118140960795 + 8036878 * 2 ^ 59
def prefixEnd_8036878 : Nat := 4983230072969 + 3 ^ 40 * 8036878 * 2
def baseEnd_8036878 : Nat := 4126781375545311911564077

theorem tailTrace_8036878 : CollatzResearch.WordTrace tailWord_8036878 prefixEnd_8036878 4126781375545311911564077 := by
  unfold tailWord_8036878
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641127772221383791259911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195419348118514046886719525 36641127772221383791259911)
  ·
    refine ⟨54961691658332075686889867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36641127772221383791259911 54961691658332075686889867)
    ·
      refine ⟨82442537487498113530334801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54961691658332075686889867 82442537487498113530334801)
      ·
        refine ⟨61831903115623585147751101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82442537487498113530334801 61831903115623585147751101)
        ·
          refine ⟨23186963668358844430406663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61831903115623585147751101 23186963668358844430406663)
          ·
            refine ⟨34780445502538266645609995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23186963668358844430406663 34780445502538266645609995)
            ·
              refine ⟨52170668253807399968414993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34780445502538266645609995 52170668253807399968414993)
              ·
                refine ⟨39128001190355549976311245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52170668253807399968414993 39128001190355549976311245)
                ·
                  refine ⟨14673000446383331241116717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39128001190355549976311245 14673000446383331241116717)
                  ·
                    refine ⟨5502375167393749215418769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14673000446383331241116717 5502375167393749215418769)
                    ·
                      refine ⟨4126781375545311911564077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502375167393749215418769 4126781375545311911564077)
                      ·
                        rfl

theorem cell23_8036878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_8036878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036878 prefixEnd_8036878 := by exact prefixLift 8036878
  have htrace : WordTrace (prefixWord ++ tailWord_8036878) baseStart_8036878 baseEnd_8036878 := by
    simpa [prefixWord, tailWord_8036878, baseEnd_8036878] using wordTrace_append hprefix tailTrace_8036878
  have hstable : (prefixWord ++ tailWord_8036878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036878).length < 2 ^ (prefixWord ++ tailWord_8036878).sum := by decide
  have hdescent : baseEnd_8036878 < baseStart_8036878 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036925 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 4, 2, 2]
def baseStart_8036925 : Nat := 118140960795 + 8036925 * 2 ^ 59
def prefixEnd_8036925 : Nat := 4983230072969 + 3 ^ 40 * 8036925 * 2
def baseEnd_8036925 : Nat := 4126805509136073227676361

theorem tailTrace_8036925 : CollatzResearch.WordTrace tailWord_8036925 prefixEnd_8036925 4126805509136073227676361 := by
  unfold tailWord_8036925
  simp only [CollatzResearch.WordTrace]
  refine ⟨293130736408600797357040229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195420490939067198238026819 293130736408600797357040229)
  ·
    refine ⟨54962013076612649504445043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293130736408600797357040229 54962013076612649504445043)
    ·
      refine ⟨82443019614918974256667565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962013076612649504445043 82443019614918974256667565)
      ·
        refine ⟨30916132355594615346250337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82443019614918974256667565 30916132355594615346250337)
        ·
          refine ⟨23187099266695961509687753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30916132355594615346250337 23187099266695961509687753)
          ·
            refine ⟨17390324450021971132265815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23187099266695961509687753 17390324450021971132265815)
            ·
              refine ⟨26085486675032956698398723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390324450021971132265815 26085486675032956698398723)
              ·
                refine ⟨39128230012549435047598085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26085486675032956698398723 39128230012549435047598085)
                ·
                  refine ⟨7336543127353019071424641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39128230012549435047598085 7336543127353019071424641)
                  ·
                    refine ⟨5502407345514764303568481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336543127353019071424641 5502407345514764303568481)
                    ·
                      refine ⟨4126805509136073227676361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502407345514764303568481 4126805509136073227676361)
                      ·
                        rfl

theorem cell23_8036925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_8036925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036925 prefixEnd_8036925 := by exact prefixLift 8036925
  have htrace : WordTrace (prefixWord ++ tailWord_8036925) baseStart_8036925 baseEnd_8036925 := by
    simpa [prefixWord, tailWord_8036925, baseEnd_8036925] using wordTrace_append hprefix tailTrace_8036925
  have hstable : (prefixWord ++ tailWord_8036925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036925).length < 2 ^ (prefixWord ++ tailWord_8036925).sum := by decide
  have hdescent : baseEnd_8036925 < baseStart_8036925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036944 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 6, 5]
def baseStart_8036944 : Nat := 118140960795 + 8036944 * 2 ^ 59
def prefixEnd_8036944 : Nat := 4983230072969 + 3 ^ 40 * 8036944 * 2
def baseEnd_8036944 : Nat := 1375605088422836217779591

theorem tailTrace_8036944 : CollatzResearch.WordTrace tailWord_8036944 prefixEnd_8036944 1375605088422836217779591 := by
  unfold tailWord_8036944
  simp only [CollatzResearch.WordTrace]
  refine ⟨146565714697765981800990943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195420952930354642401321257 146565714697765981800990943)
  ·
    refine ⟨219848572046648972701486415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146565714697765981800990943 219848572046648972701486415)
    ·
      refine ⟨329772858069973459052229623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219848572046648972701486415 329772858069973459052229623)
      ·
        refine ⟨494659287104960188578344435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329772858069973459052229623 494659287104960188578344435)
        ·
          refine ⟨741988930657440282867516653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494659287104960188578344435 741988930657440282867516653)
          ·
            refine ⟨278245848996540106075318745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 741988930657440282867516653 278245848996540106075318745)
            ·
              refine ⟨208684386747405079556489059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278245848996540106075318745 208684386747405079556489059)
              ·
                refine ⟨313026580121107619334733589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208684386747405079556489059 313026580121107619334733589)
                ·
                  refine ⟨14673120943176919656315637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313026580121107619334733589 14673120943176919656315637)
                  ·
                    refine ⟨1375605088422836217779591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14673120943176919656315637 1375605088422836217779591)
                    ·
                      rfl

theorem cell23_8036944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 6, 5].length) (baseStart_8036944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036944 prefixEnd_8036944 := by exact prefixLift 8036944
  have htrace : WordTrace (prefixWord ++ tailWord_8036944) baseStart_8036944 baseEnd_8036944 := by
    simpa [prefixWord, tailWord_8036944, baseEnd_8036944] using wordTrace_append hprefix tailTrace_8036944
  have hstable : (prefixWord ++ tailWord_8036944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036944).length < 2 ^ (prefixWord ++ tailWord_8036944).sum := by decide
  have hdescent : baseEnd_8036944 < baseStart_8036944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036954 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_8036954 : Nat := 118140960795 + 8036954 * 2 ^ 59
def prefixEnd_8036954 : Nat := 4983230072969 + 3 ^ 40 * 8036954 * 2
def baseEnd_8036954 : Nat := 4126820400075053614213727

theorem tailTrace_8036954 : CollatzResearch.WordTrace tailWord_8036954 prefixEnd_8036954 4126820400075053614213727 := by
  unfold tailWord_8036954
  simp only [CollatzResearch.WordTrace]
  refine ⟨73282948531373933827461479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195421196083663823539897277 73282948531373933827461479)
  ·
    refine ⟨109924422797060900741192219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73282948531373933827461479 109924422797060900741192219)
    ·
      refine ⟨164886634195591351111788329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109924422797060900741192219 164886634195591351111788329)
      ·
        refine ⟨123664975646693513333841247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164886634195591351111788329 123664975646693513333841247)
        ·
          refine ⟨185497463470040270000761871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123664975646693513333841247 185497463470040270000761871)
          ·
            refine ⟨278246195205060405001142807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185497463470040270000761871 278246195205060405001142807)
            ·
              refine ⟨417369292807590607501714211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278246195205060405001142807 417369292807590607501714211)
              ·
                refine ⟨626053939211385911252571317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417369292807590607501714211 626053939211385911252571317)
                ·
                  refine ⟨58692556801067429179928561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 626053939211385911252571317 58692556801067429179928561)
                  ·
                    refine ⟨44019417600800571884946421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58692556801067429179928561 44019417600800571884946421)
                    ·
                      refine ⟨4126820400075053614213727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44019417600800571884946421 4126820400075053614213727)
                      ·
                        rfl

theorem cell23_8036954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_8036954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036954 prefixEnd_8036954 := by exact prefixLift 8036954
  have htrace : WordTrace (prefixWord ++ tailWord_8036954) baseStart_8036954 baseEnd_8036954 := by
    simpa [prefixWord, tailWord_8036954, baseEnd_8036954] using wordTrace_append hprefix tailTrace_8036954
  have hstable : (prefixWord ++ tailWord_8036954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036954).length < 2 ^ (prefixWord ++ tailWord_8036954).sum := by decide
  have hdescent : baseEnd_8036954 < baseStart_8036954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036965 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 5]
def baseStart_8036965 : Nat := 118140960795 + 8036965 * 2 ^ 59
def prefixEnd_8036965 : Nat := 4983230072969 + 3 ^ 40 * 8036965 * 2
def baseEnd_8036965 : Nat := 458536227595805896797353

theorem tailTrace_8036965 : CollatzResearch.WordTrace tailWord_8036965 prefixEnd_8036965 458536227595805896797353 := by
  unfold tailWord_8036965
  simp only [CollatzResearch.WordTrace]
  refine ⟨293132195328455884188496349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195421463552303922792330899 293132195328455884188496349)
  ·
    refine ⟨109924573248170956570686131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293132195328455884188496349 109924573248170956570686131)
    ·
      refine ⟨164886859872256434856029197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109924573248170956570686131 164886859872256434856029197)
      ·
        refine ⟨61832572452096163071010949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164886859872256434856029197 61832572452096163071010949)
        ·
          refine ⟨11593607334768030575814553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61832572452096163071010949 11593607334768030575814553)
          ·
            refine ⟨8695205501076022931860915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11593607334768030575814553 8695205501076022931860915)
            ·
              refine ⟨13042808251614034397791373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695205501076022931860915 13042808251614034397791373)
              ·
                refine ⟨4891053094355262899171765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042808251614034397791373 4891053094355262899171765)
                ·
                  refine ⟨458536227595805896797353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891053094355262899171765 458536227595805896797353)
                  ·
                    rfl

theorem cell23_8036965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_8036965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036965 prefixEnd_8036965 := by exact prefixLift 8036965
  have htrace : WordTrace (prefixWord ++ tailWord_8036965) baseStart_8036965 baseEnd_8036965 := by
    simpa [prefixWord, tailWord_8036965, baseEnd_8036965] using wordTrace_append hprefix tailTrace_8036965
  have hstable : (prefixWord ++ tailWord_8036965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036965).length < 2 ^ (prefixWord ++ tailWord_8036965).sum := by decide
  have hdescent : baseEnd_8036965 < baseStart_8036965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036978 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_8036978 : Nat := 118140960795 + 8036978 * 2 ^ 59
def prefixEnd_8036978 : Nat := 4983230072969 + 3 ^ 40 * 8036978 * 2
def baseEnd_8036978 : Nat := 1375610907870253840104539

theorem tailTrace_8036978 : CollatzResearch.WordTrace tailWord_8036978 prefixEnd_8036978 1375610907870253840104539 := by
  unfold tailWord_8036978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73283167369352196852179897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195421779651605858272479725 73283167369352196852179897)
  ·
    refine ⟨54962375527014147639134923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73283167369352196852179897 54962375527014147639134923)
    ·
      refine ⟨82443563290521221458702385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54962375527014147639134923 82443563290521221458702385)
      ·
        refine ⟨61832672467890916094026789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82443563290521221458702385 61832672467890916094026789)
        ·
          refine ⟨11593626087729546767630023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61832672467890916094026789 11593626087729546767630023)
          ·
            refine ⟨17390439131594320151445035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593626087729546767630023 17390439131594320151445035)
            ·
              refine ⟨26085658697391480227167553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390439131594320151445035 26085658697391480227167553)
              ·
                refine ⟨19564244023043610170375665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26085658697391480227167553 19564244023043610170375665)
                ·
                  refine ⟨14673183017282707627781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19564244023043610170375665 14673183017282707627781749)
                  ·
                    refine ⟨1375610907870253840104539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14673183017282707627781749 1375610907870253840104539)
                    ·
                      rfl

theorem cell23_8036978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_8036978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036978 prefixEnd_8036978 := by exact prefixLift 8036978
  have htrace : WordTrace (prefixWord ++ tailWord_8036978) baseStart_8036978 baseEnd_8036978 := by
    simpa [prefixWord, tailWord_8036978, baseEnd_8036978] using wordTrace_append hprefix tailTrace_8036978
  have hstable : (prefixWord ++ tailWord_8036978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036978).length < 2 ^ (prefixWord ++ tailWord_8036978).sum := by decide
  have hdescent : baseEnd_8036978 < baseStart_8036978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036982 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_8036982 : Nat := 118140960795 + 8036982 * 2 ^ 59
def prefixEnd_8036982 : Nat := 4983230072969 + 3 ^ 40 * 8036982 * 2
def baseEnd_8036982 : Nat := 458537197503708833851511

theorem tailTrace_8036982 : CollatzResearch.WordTrace tailWord_8036982 prefixEnd_8036982 458537197503708833851511 := by
  unfold tailWord_8036982
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320800960587143505741575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195421876912929530727910133 18320800960587143505741575)
  ·
    refine ⟨27481201440880715258612363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18320800960587143505741575 27481201440880715258612363)
    ·
      refine ⟨41221802161321072887918545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27481201440880715258612363 41221802161321072887918545)
      ·
        refine ⟨30916351620990804665938909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41221802161321072887918545 30916351620990804665938909)
        ·
          refine ⟨11593631857871551749727091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30916351620990804665938909 11593631857871551749727091)
          ·
            refine ⟨17390447786807327624590637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593631857871551749727091 17390447786807327624590637)
            ·
              refine ⟨6521417920052747859221489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17390447786807327624590637 6521417920052747859221489)
              ·
                refine ⟨4891063440039560894416117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521417920052747859221489 4891063440039560894416117)
                ·
                  refine ⟨458537197503708833851511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891063440039560894416117 458537197503708833851511)
                  ·
                    rfl

theorem cell23_8036982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_8036982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036982 prefixEnd_8036982 := by exact prefixLift 8036982
  have htrace : WordTrace (prefixWord ++ tailWord_8036982) baseStart_8036982 baseEnd_8036982 := by
    simpa [prefixWord, tailWord_8036982, baseEnd_8036982] using wordTrace_append hprefix tailTrace_8036982
  have hstable : (prefixWord ++ tailWord_8036982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036982).length < 2 ^ (prefixWord ++ tailWord_8036982).sum := by decide
  have hdescent : baseEnd_8036982 < baseStart_8036982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036984 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_8036984 : Nat := 118140960795 + 8036984 * 2 ^ 59
def prefixEnd_8036984 : Nat := 4983230072969 + 3 ^ 40 * 8036984 * 2
def baseEnd_8036984 : Nat := 4126835804494688496838589

theorem tailTrace_8036984 : CollatzResearch.WordTrace tailWord_8036984 prefixEnd_8036984 4126835804494688496838589 := by
  unfold tailWord_8036984
  simp only [CollatzResearch.WordTrace]
  refine ⟨146566444157693525216719003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195421925543591366955625337 146566444157693525216719003)
  ·
    refine ⟨219849666236540287825078505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146566444157693525216719003 219849666236540287825078505)
    ·
      refine ⟨164887249677405215868808879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219849666236540287825078505 164887249677405215868808879)
      ·
        refine ⟨247330874516107823803213319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164887249677405215868808879 247330874516107823803213319)
        ·
          refine ⟨370996311774161735704819979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247330874516107823803213319 370996311774161735704819979)
          ·
            refine ⟨556494467661242603557229969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370996311774161735704819979 556494467661242603557229969)
            ·
              refine ⟨417370850745931952667922477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556494467661242603557229969 417370850745931952667922477)
              ·
                refine ⟨156514069029724482250470929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417370850745931952667922477 156514069029724482250470929)
                ·
                  refine ⟨117385551772293361687853197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156514069029724482250470929 117385551772293361687853197)
                  ·
                    refine ⟨44019581914610010632944949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117385551772293361687853197 44019581914610010632944949)
                    ·
                      refine ⟨4126835804494688496838589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44019581914610010632944949 4126835804494688496838589)
                      ·
                        rfl

theorem cell23_8036984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_8036984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036984 prefixEnd_8036984 := by exact prefixLift 8036984
  have htrace : WordTrace (prefixWord ++ tailWord_8036984) baseStart_8036984 baseEnd_8036984 := by
    simpa [prefixWord, tailWord_8036984, baseEnd_8036984] using wordTrace_append hprefix tailTrace_8036984
  have hstable : (prefixWord ++ tailWord_8036984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036984).length < 2 ^ (prefixWord ++ tailWord_8036984).sum := by decide
  have hdescent : baseEnd_8036984 < baseStart_8036984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8036991 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 3, 4]
def baseStart_8036991 : Nat := 118140960795 + 8036991 * 2 ^ 59
def prefixEnd_8036991 : Nat := 4983230072969 + 3 ^ 40 * 8036991 * 2
def baseEnd_8036991 : Nat := 1375613132953089989817019

theorem tailTrace_8036991 : CollatzResearch.WordTrace tailWord_8036991 prefixEnd_8036991 1375613132953089989817019 := by
  unfold tailWord_8036991
  simp only [CollatzResearch.WordTrace]
  refine ⟨293133143626361690628942827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195422095750907793752628551 293133143626361690628942827)
  ·
    refine ⟨439699715439542535943414241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293133143626361690628942827 439699715439542535943414241)
    ·
      refine ⟨329774786579656901957560681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439699715439542535943414241 329774786579656901957560681)
      ·
        refine ⟨247331089934742676468170511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329774786579656901957560681 247331089934742676468170511)
        ·
          refine ⟨370996634902114014702255767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247331089934742676468170511 370996634902114014702255767)
          ·
            refine ⟨556494952353171022053383651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370996634902114014702255767 556494952353171022053383651)
            ·
              refine ⟨834742428529756533080075477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556494952353171022053383651 834742428529756533080075477)
              ·
                refine ⟨19564275668666168744064269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 834742428529756533080075477 19564275668666168744064269)
                ·
                  refine ⟨7336603375749813279024101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19564275668666168744064269 7336603375749813279024101)
                  ·
                    refine ⟨1375613132953089989817019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336603375749813279024101 1375613132953089989817019)
                    ·
                      rfl

theorem cell23_8036991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 3, 4].length) (baseStart_8036991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8036991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8036991 prefixEnd_8036991 := by exact prefixLift 8036991
  have htrace : WordTrace (prefixWord ++ tailWord_8036991) baseStart_8036991 baseEnd_8036991 := by
    simpa [prefixWord, tailWord_8036991, baseEnd_8036991] using wordTrace_append hprefix tailTrace_8036991
  have hstable : (prefixWord ++ tailWord_8036991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8036991).length < 2 ^ (prefixWord ++ tailWord_8036991).sum := by decide
  have hdescent : baseEnd_8036991 < baseStart_8036991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8036991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037001 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 3]
def baseStart_8037001 : Nat := 118140960795 + 8037001 * 2 ^ 59
def prefixEnd_8037001 : Nat := 4983230072969 + 3 ^ 40 * 8037001 * 2
def baseEnd_8037001 : Nat := 4126844533665814930326011

theorem tailTrace_8037001 : CollatzResearch.WordTrace tailWord_8037001 prefixEnd_8037001 4126844533665814930326011 := by
  unfold tailWord_8037001
  simp only [CollatzResearch.WordTrace]
  refine ⟨293133508356325462336806857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195422338904216974891204571 293133508356325462336806857)
  ·
    refine ⟨219850131267244096752605143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293133508356325462336806857 219850131267244096752605143)
    ·
      refine ⟨329775196900866145128907715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219850131267244096752605143 329775196900866145128907715)
      ·
        refine ⟨494662795351299217693361573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329775196900866145128907715 494662795351299217693361573)
        ·
          refine ⟨92749274128368603317505295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494662795351299217693361573 92749274128368603317505295)
          ·
            refine ⟨139123911192552904976257943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92749274128368603317505295 139123911192552904976257943)
            ·
              refine ⟨208685866788829357464386915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139123911192552904976257943 208685866788829357464386915)
              ·
                refine ⟨313028800183244036196580373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208685866788829357464386915 313028800183244036196580373)
                ·
                  refine ⟨14673225008589564196714705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 313028800183244036196580373 14673225008589564196714705)
                  ·
                    refine ⟨11004918756442173147536029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14673225008589564196714705 11004918756442173147536029)
                    ·
                      refine ⟨4126844533665814930326011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11004918756442173147536029 4126844533665814930326011)
                      ·
                        rfl

theorem cell23_8037001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 2, 3].length) (baseStart_8037001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037001 prefixEnd_8037001 := by exact prefixLift 8037001
  have htrace : WordTrace (prefixWord ++ tailWord_8037001) baseStart_8037001 baseEnd_8037001 := by
    simpa [prefixWord, tailWord_8037001, baseEnd_8037001] using wordTrace_append hprefix tailTrace_8037001
  have hstable : (prefixWord ++ tailWord_8037001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037001).length < 2 ^ (prefixWord ++ tailWord_8037001).sum := by decide
  have hdescent : baseEnd_8037001 < baseStart_8037001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037004 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 10]
def baseStart_8037004 : Nat := 118140960795 + 8037004 * 2 ^ 59
def prefixEnd_8037004 : Nat := 4983230072969 + 3 ^ 40 * 8037004 * 2
def baseEnd_8037004 : Nat := 458538452678642046509833

theorem tailTrace_8037004 : CollatzResearch.WordTrace tailWord_8037004 prefixEnd_8037004 458538452678642046509833 := by
  unfold tailWord_8037004
  simp only [CollatzResearch.WordTrace]
  refine ⟨146566808887657296924583033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195422411850209729232777377 146566808887657296924583033)
  ·
    refine ⟨109925106665742972693437275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146566808887657296924583033 109925106665742972693437275)
    ·
      refine ⟨164887659998614459040155913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109925106665742972693437275 164887659998614459040155913)
      ·
        refine ⟨123665744998960844280116935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164887659998614459040155913 123665744998960844280116935)
        ·
          refine ⟨185498617498441266420175403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123665744998960844280116935 185498617498441266420175403)
          ·
            refine ⟨278247926247661899630263105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185498617498441266420175403 278247926247661899630263105)
            ·
              refine ⟨208685944685746424722697329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278247926247661899630263105 208685944685746424722697329)
              ·
                refine ⟨156514458514309818542022997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208685944685746424722697329 156514458514309818542022997)
                ·
                  refine ⟨458538452678642046509833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156514458514309818542022997 458538452678642046509833)
                  ·
                    rfl

theorem cell23_8037004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_8037004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037004 prefixEnd_8037004 := by exact prefixLift 8037004
  have htrace : WordTrace (prefixWord ++ tailWord_8037004) baseStart_8037004 baseEnd_8037004 := by
    simpa [prefixWord, tailWord_8037004, baseEnd_8037004] using wordTrace_append hprefix tailTrace_8037004
  have hstable : (prefixWord ++ tailWord_8037004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037004).length < 2 ^ (prefixWord ++ tailWord_8037004).sum := by decide
  have hdescent : baseEnd_8037004 < baseStart_8037004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037068 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 3, 5]
def baseStart_8037068 : Nat := 118140960795 + 8037068 * 2 ^ 59
def prefixEnd_8037068 : Nat := 4983230072969 + 3 ^ 40 * 8037068 * 2
def baseEnd_8037068 : Nat := 1375626312289888722729401

theorem tailTrace_8037068 : CollatzResearch.WordTrace tailWord_8037068 prefixEnd_8037068 1375626312289888722729401 := by
  unfold tailWord_8037068
  simp only [CollatzResearch.WordTrace]
  refine ⟨146567976023541366389747929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195423968031388488519663905 146567976023541366389747929)
  ·
    refine ⟨109925982017656024792310947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146567976023541366389747929 109925982017656024792310947)
    ·
      refine ⟨164888973026484037188466421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109925982017656024792310947 164888973026484037188466421)
      ·
        refine ⟨15458341221232878486418727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 164888973026484037188466421 15458341221232878486418727)
        ·
          refine ⟨23187511831849317729628091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458341221232878486418727 23187511831849317729628091)
          ·
            refine ⟨34781267747773976594442137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23187511831849317729628091 34781267747773976594442137)
            ·
              refine ⟨26085950810830482445831603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34781267747773976594442137 26085950810830482445831603)
              ·
                refine ⟨39128926216245723668747405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26085950810830482445831603 39128926216245723668747405)
                ·
                  refine ⟨14673347331092146375780277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39128926216245723668747405 14673347331092146375780277)
                  ·
                    refine ⟨1375626312289888722729401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14673347331092146375780277 1375626312289888722729401)
                    ·
                      rfl

theorem cell23_8037068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 3, 5].length) (baseStart_8037068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037068 prefixEnd_8037068 := by exact prefixLift 8037068
  have htrace : WordTrace (prefixWord ++ tailWord_8037068) baseStart_8037068 baseEnd_8037068 := by
    simpa [prefixWord, tailWord_8037068, baseEnd_8037068] using wordTrace_append hprefix tailTrace_8037068
  have hstable : (prefixWord ++ tailWord_8037068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037068).length < 2 ^ (prefixWord ++ tailWord_8037068).sum := by decide
  have hdescent : baseEnd_8037068 < baseStart_8037068 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037069 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_8037069 : Nat := 118140960795 + 8037069 * 2 ^ 59
def prefixEnd_8037069 : Nat := 4983230072969 + 3 ^ 40 * 8037069 * 2
def baseEnd_8037069 : Nat := 4126879450350320664275699

theorem tailTrace_8037069 : CollatzResearch.WordTrace tailWord_8037069 prefixEnd_8037069 4126879450350320664275699 := by
  unfold tailWord_8037069
  simp only [CollatzResearch.WordTrace]
  refine ⟨293135988520079109950282261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195423992346719406633521507 293135988520079109950282261)
  ·
    refine ⟨13740749461878708278919481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293135988520079109950282261 13740749461878708278919481)
    ·
      refine ⟨10305562096409031209189611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13740749461878708278919481 10305562096409031209189611)
      ·
        refine ⟨15458343144613546813784417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305562096409031209189611 15458343144613546813784417)
        ·
          refine ⟨11593757358460160110338313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15458343144613546813784417 11593757358460160110338313)
          ·
            refine ⟨8695318018845120082753735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11593757358460160110338313 8695318018845120082753735)
            ·
              refine ⟨13042977028267680124130603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695318018845120082753735 13042977028267680124130603)
              ·
                refine ⟨19564465542401520186195905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13042977028267680124130603 19564465542401520186195905)
                ·
                  refine ⟨14673349156801140139646929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19564465542401520186195905 14673349156801140139646929)
                  ·
                    refine ⟨11005011867600855104735197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14673349156801140139646929 11005011867600855104735197)
                    ·
                      refine ⟨4126879450350320664275699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005011867600855104735197 4126879450350320664275699)
                      ·
                        rfl

theorem cell23_8037069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_8037069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037069 prefixEnd_8037069 := by exact prefixLift 8037069
  have htrace : WordTrace (prefixWord ++ tailWord_8037069) baseStart_8037069 baseEnd_8037069 := by
    simpa [prefixWord, tailWord_8037069, baseEnd_8037069] using wordTrace_append hprefix tailTrace_8037069
  have hstable : (prefixWord ++ tailWord_8037069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037069).length < 2 ^ (prefixWord ++ tailWord_8037069).sum := by decide
  have hdescent : baseEnd_8037069 < baseStart_8037069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037081 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 1, 6]
def baseStart_8037081 : Nat := 118140960795 + 8037081 * 2 ^ 59
def prefixEnd_8037081 : Nat := 4983230072969 + 3 ^ 40 * 8037081 * 2
def baseEnd_8037081 : Nat := 1375628537372724872441881

theorem tailTrace_8037081 : CollatzResearch.WordTrace tailWord_8037081 prefixEnd_8037081 1375628537372724872441881 := by
  unfold tailWord_8037081
  simp only [CollatzResearch.WordTrace]
  refine ⟨293136426196035635999719097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195424284130690423999812731 293136426196035635999719097)
  ·
    refine ⟨219852319647026726999789323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293136426196035635999719097 219852319647026726999789323)
    ·
      refine ⟨329778479470540090499683985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219852319647026726999789323 329778479470540090499683985)
      ·
        refine ⟨247333859602905067874762989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329778479470540090499683985 247333859602905067874762989)
        ·
          refine ⟨92750197351089400453036121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247333859602905067874762989 92750197351089400453036121)
          ·
            refine ⟨69562648013317050339777091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92750197351089400453036121 69562648013317050339777091)
            ·
              refine ⟨104343972019975575509665637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69562648013317050339777091 104343972019975575509665637)
              ·
                refine ⟨19564494753745420408062307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104343972019975575509665637 19564494753745420408062307)
                ·
                  refine ⟨29346742130618130612093461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19564494753745420408062307 29346742130618130612093461)
                  ·
                    refine ⟨1375628537372724872441881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29346742130618130612093461 1375628537372724872441881)
                    ·
                      rfl

theorem cell23_8037081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 1, 6].length) (baseStart_8037081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037081 prefixEnd_8037081 := by exact prefixLift 8037081
  have htrace : WordTrace (prefixWord ++ tailWord_8037081) baseStart_8037081 baseEnd_8037081 := by
    simpa [prefixWord, tailWord_8037081, baseEnd_8037081] using wordTrace_append hprefix tailTrace_8037081
  have hstable : (prefixWord ++ tailWord_8037081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037081).length < 2 ^ (prefixWord ++ tailWord_8037081).sum := by decide
  have hdescent : baseEnd_8037081 < baseStart_8037081 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037082 : List Nat := [3, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3]
def baseStart_8037082 : Nat := 118140960795 + 8037082 * 2 ^ 59
def prefixEnd_8037082 : Nat := 4983230072969 + 3 ^ 40 * 8037082 * 2
def baseEnd_8037082 : Nat := 4126886125598829113413139

theorem tailTrace_8037082 : CollatzResearch.WordTrace tailWord_8037082 prefixEnd_8037082 4126886125598829113413139 := by
  unfold tailWord_8037082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284115667258003292626375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195424308446021342113670333 73284115667258003292626375)
  ·
    refine ⟨109926173500887004938939563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73284115667258003292626375 109926173500887004938939563)
    ·
      refine ⟨164889260251330507408409345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109926173500887004938939563 164889260251330507408409345)
      ·
        refine ⟨123666945188497880556307009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164889260251330507408409345 123666945188497880556307009)
        ·
          refine ⟨92750208891373410417230257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123666945188497880556307009 92750208891373410417230257)
          ·
            refine ⟨69562656668530057812922693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92750208891373410417230257 69562656668530057812922693)
            ·
              refine ⟨13042998125349385839923005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69562656668530057812922693 13042998125349385839923005)
              ·
                refine ⟨4891124297006019689971127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042998125349385839923005 4891124297006019689971127)
                ·
                  refine ⟨7336686445509029534956691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891124297006019689971127 7336686445509029534956691)
                  ·
                    refine ⟨11005029668263544302435037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336686445509029534956691 11005029668263544302435037)
                    ·
                      refine ⟨4126886125598829113413139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005029668263544302435037 4126886125598829113413139)
                      ·
                        rfl

theorem cell23_8037082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_8037082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037082 prefixEnd_8037082 := by exact prefixLift 8037082
  have htrace : WordTrace (prefixWord ++ tailWord_8037082) baseStart_8037082 baseEnd_8037082 := by
    simpa [prefixWord, tailWord_8037082, baseEnd_8037082] using wordTrace_append hprefix tailTrace_8037082
  have hstable : (prefixWord ++ tailWord_8037082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037082).length < 2 ^ (prefixWord ++ tailWord_8037082).sum := by decide
  have hdescent : baseEnd_8037082 < baseStart_8037082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037122 : List Nat := [3, 4, 1, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_8037122 : Nat := 118140960795 + 8037122 * 2 ^ 59
def prefixEnd_8037122 : Nat := 4983230072969 + 3 ^ 40 * 8037122 * 2
def baseEnd_8037122 : Nat := 4126906664825008956912955

theorem tailTrace_8037122 : CollatzResearch.WordTrace tailWord_8037122 prefixEnd_8037122 4126906664825008956912955 := by
  unfold tailWord_8037122
  simp only [CollatzResearch.WordTrace]
  refine ⟨73284480397221775000490405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195425281059258066667974413 73284480397221775000490405)
  ·
    refine ⟨13740840074479082812591951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73284480397221775000490405 13740840074479082812591951)
    ·
      refine ⟨20611260111718624218887927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13740840074479082812591951 20611260111718624218887927)
      ·
        refine ⟨30916890167577936328331891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20611260111718624218887927 30916890167577936328331891)
        ·
          refine ⟨46375335251366904492497837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30916890167577936328331891 46375335251366904492497837)
          ·
            refine ⟨17390750719262589184686689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46375335251366904492497837 17390750719262589184686689)
            ·
              refine ⟨13043063039446941888515017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17390750719262589184686689 13043063039446941888515017)
              ·
                refine ⟨9782297279585206416386263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13043063039446941888515017 9782297279585206416386263)
                ·
                  refine ⟨14673445919377809624579395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9782297279585206416386263 14673445919377809624579395)
                  ·
                    refine ⟨22010168879066714436869093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14673445919377809624579395 22010168879066714436869093)
                    ·
                      refine ⟨4126906664825008956912955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22010168879066714436869093 4126906664825008956912955)
                      ·
                        rfl

theorem cell23_8037122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_8037122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037122 prefixEnd_8037122 := by exact prefixLift 8037122
  have htrace : WordTrace (prefixWord ++ tailWord_8037122) baseStart_8037122 baseEnd_8037122 := by
    simpa [prefixWord, tailWord_8037122, baseEnd_8037122] using wordTrace_append hprefix tailTrace_8037122
  have hstable : (prefixWord ++ tailWord_8037122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037122).length < 2 ^ (prefixWord ++ tailWord_8037122).sum := by decide
  have hdescent : baseEnd_8037122 < baseStart_8037122 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037128 : List Nat := [2, 1, 3, 2, 2, 2, 4, 7]
def baseStart_8037128 : Nat := 118140960795 + 8037128 * 2 ^ 59
def prefixEnd_8037128 : Nat := 4983230072969 + 3 ^ 40 * 8037128 * 2
def baseEnd_8037128 : Nat := 152848509100330960497701

theorem tailTrace_8037128 : CollatzResearch.WordTrace tailWord_8037128 prefixEnd_8037128 152848509100330960497701 := by
  unfold tailWord_8037128
  simp only [CollatzResearch.WordTrace]
  refine ⟨146569070213432681513340019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195425426951243575351120025 146569070213432681513340019)
  ·
    refine ⟨219853605320149022270010029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146569070213432681513340019 219853605320149022270010029)
    ·
      refine ⟨82445101995055883351253761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219853605320149022270010029 82445101995055883351253761)
      ·
        refine ⟨61833826496291912513440321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82445101995055883351253761 61833826496291912513440321)
        ·
          refine ⟨46375369872218934385080241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61833826496291912513440321 46375369872218934385080241)
          ·
            refine ⟨34781527404164200788810181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46375369872218934385080241 34781527404164200788810181)
            ·
              refine ⟨6521536388280787647901909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34781527404164200788810181 6521536388280787647901909)
              ·
                refine ⟨152848509100330960497701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6521536388280787647901909 152848509100330960497701)
                ·
                  rfl

theorem cell23_8037128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 7].length) (baseStart_8037128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037128 prefixEnd_8037128 := by exact prefixLift 8037128
  have htrace : WordTrace (prefixWord ++ tailWord_8037128) baseStart_8037128 baseEnd_8037128 := by
    simpa [prefixWord, tailWord_8037128, baseEnd_8037128] using wordTrace_append hprefix tailTrace_8037128
  have hstable : (prefixWord ++ tailWord_8037128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037128).length < 2 ^ (prefixWord ++ tailWord_8037128).sum := by decide
  have hdescent : baseEnd_8037128 < baseStart_8037128 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037155 : List Nat := [1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 3]
def baseStart_8037155 : Nat := 118140960795 + 8037155 * 2 ^ 59
def prefixEnd_8037155 : Nat := 4983230072969 + 3 ^ 40 * 8037155 * 2
def baseEnd_8037155 : Nat := 4126923609686607327800303

theorem tailTrace_8037155 : CollatzResearch.WordTrace tailWord_8037155 prefixEnd_8037155 4126923609686607327800303 := by
  unfold tailWord_8037155
  simp only [CollatzResearch.WordTrace]
  refine ⟨293139125197767546637912919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195426083465178364425275279 293139125197767546637912919)
  ·
    refine ⟨439708687796651319956869379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293139125197767546637912919 439708687796651319956869379)
    ·
      refine ⟨659563031694976979935304069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439708687796651319956869379 659563031694976979935304069)
      ·
        refine ⟨123668068442808183737869513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659563031694976979935304069 123668068442808183737869513)
        ·
          refine ⟨92751051332106137803402135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123668068442808183737869513 92751051332106137803402135)
          ·
            refine ⟨139126576998159206705103203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92751051332106137803402135 139126576998159206705103203)
            ·
              refine ⟨208689865497238810057654805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139126576998159206705103203 208689865497238810057654805)
              ·
                refine ⟨9782337445183069221452569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208689865497238810057654805 9782337445183069221452569)
                ·
                  refine ⟨7336753083887301916089427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9782337445183069221452569 7336753083887301916089427)
                  ·
                    refine ⟨11005129625830952874134141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336753083887301916089427 11005129625830952874134141)
                    ·
                      refine ⟨4126923609686607327800303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005129625830952874134141 4126923609686607327800303)
                      ·
                        rfl

theorem cell23_8037155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_8037155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037155 prefixEnd_8037155 := by exact prefixLift 8037155
  have htrace : WordTrace (prefixWord ++ tailWord_8037155) baseStart_8037155 baseEnd_8037155 := by
    simpa [prefixWord, tailWord_8037155, baseEnd_8037155] using wordTrace_append hprefix tailTrace_8037155
  have hstable : (prefixWord ++ tailWord_8037155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037155).length < 2 ^ (prefixWord ++ tailWord_8037155).sum := by decide
  have hdescent : baseEnd_8037155 < baseStart_8037155 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037156 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 3, 2, 2]
def baseStart_8037156 : Nat := 118140960795 + 8037156 * 2 ^ 59
def prefixEnd_8037156 : Nat := 4983230072969 + 3 ^ 40 * 8037156 * 2
def baseEnd_8037156 : Nat := 4126924123167261823887799

theorem tailTrace_8037156 : CollatzResearch.WordTrace tailWord_8037156 prefixEnd_8037156 4126924123167261823887799 := by
  unfold tailWord_8037156
  simp only [CollatzResearch.WordTrace]
  refine ⟨146569580835381961904349661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195426107780509282539132881 146569580835381961904349661)
  ·
    refine ⟨54963592813268235714131123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146569580835381961904349661 54963592813268235714131123)
    ·
      refine ⟨82445389219902353571196685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54963592813268235714131123 82445389219902353571196685)
      ·
        refine ⟨30917020957463382589198757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82445389219902353571196685 30917020957463382589198757)
        ·
          refine ⟨5796941429524384235474767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30917020957463382589198757 5796941429524384235474767)
          ·
            refine ⟨8695412144286576353212151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5796941429524384235474767 8695412144286576353212151)
            ·
              refine ⟨13043118216429864529818227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695412144286576353212151 13043118216429864529818227)
              ·
                refine ⟨19564677324644796794727341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13043118216429864529818227 19564677324644796794727341)
                ·
                  refine ⟨7336753996741798798022753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19564677324644796794727341 7336753996741798798022753)
                  ·
                    refine ⟨5502565497556349098517065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336753996741798798022753 5502565497556349098517065)
                    ·
                      refine ⟨4126924123167261823887799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502565497556349098517065 4126924123167261823887799)
                      ·
                        rfl

theorem cell23_8037156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_8037156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037156 prefixEnd_8037156 := by exact prefixLift 8037156
  have htrace : WordTrace (prefixWord ++ tailWord_8037156) baseStart_8037156 baseEnd_8037156 := by
    simpa [prefixWord, tailWord_8037156, baseEnd_8037156] using wordTrace_append hprefix tailTrace_8037156
  have hstable : (prefixWord ++ tailWord_8037156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037156).length < 2 ^ (prefixWord ++ tailWord_8037156).sum := by decide
  have hdescent : baseEnd_8037156 < baseStart_8037156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037161 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 4]
def baseStart_8037161 : Nat := 118140960795 + 8037161 * 2 ^ 59
def prefixEnd_8037161 : Nat := 4983230072969 + 3 ^ 40 * 8037161 * 2
def baseEnd_8037161 : Nat := 4126926690570534304325275

theorem tailTrace_8037161 : CollatzResearch.WordTrace tailWord_8037161 prefixEnd_8037161 4126926690570534304325275 := by
  unfold tailWord_8037161
  simp only [CollatzResearch.WordTrace]
  refine ⟨293139344035745809662631337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195426229357163873108420891 293139344035745809662631337)
  ·
    refine ⟨219854508026809357246973503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293139344035745809662631337 219854508026809357246973503)
    ·
      refine ⟨329781762040214035870460255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219854508026809357246973503 329781762040214035870460255)
      ·
        refine ⟨494672643060321053805690383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329781762040214035870460255 494672643060321053805690383)
        ·
          refine ⟨742008964590481580708535575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494672643060321053805690383 742008964590481580708535575)
          ·
            refine ⟨1113013446885722371062803363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742008964590481580708535575 1113013446885722371062803363)
            ·
              refine ⟨1669520170328583556594205045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113013446885722371062803363 1669520170328583556594205045)
              ·
                refine ⟨156517515968304708430706723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1669520170328583556594205045 156517515968304708430706723)
                ·
                  refine ⟨234776273952457062646060085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156517515968304708430706723 234776273952457062646060085)
                  ·
                    refine ⟨22010275683042849623068133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 234776273952457062646060085 22010275683042849623068133)
                    ·
                      refine ⟨4126926690570534304325275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22010275683042849623068133 4126926690570534304325275)
                      ·
                        rfl

theorem cell23_8037161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 5, 4].length) (baseStart_8037161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037161 prefixEnd_8037161 := by exact prefixLift 8037161
  have htrace : WordTrace (prefixWord ++ tailWord_8037161) baseStart_8037161 baseEnd_8037161 := by
    simpa [prefixWord, tailWord_8037161, baseEnd_8037161] using wordTrace_append hprefix tailTrace_8037161
  have hstable : (prefixWord ++ tailWord_8037161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037161).length < 2 ^ (prefixWord ++ tailWord_8037161).sum := by decide
  have hdescent : baseEnd_8037161 < baseStart_8037161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037198 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_8037198 : Nat := 118140960795 + 8037198 * 2 ^ 59
def prefixEnd_8037198 : Nat := 4983230072969 + 3 ^ 40 * 8037198 * 2
def baseEnd_8037198 : Nat := 4126945689354750659562605

theorem tailTrace_8037198 : CollatzResearch.WordTrace tailWord_8037198 prefixEnd_8037198 4126945689354750659562605 := by
  unfold tailWord_8037198
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642586692076470622716031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195427129024407843321152165 36642586692076470622716031)
  ·
    refine ⟨54963880038114705934074047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36642586692076470622716031 54963880038114705934074047)
    ·
      refine ⟨82445820057172058901111071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54963880038114705934074047 82445820057172058901111071)
      ·
        refine ⟨123668730085758088351666607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82445820057172058901111071 123668730085758088351666607)
        ·
          refine ⟨185503095128637132527499911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123668730085758088351666607 185503095128637132527499911)
          ·
            refine ⟨278254642692955698791249867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185503095128637132527499911 278254642692955698791249867)
            ·
              refine ⟨417381964039433548186874801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278254642692955698791249867 417381964039433548186874801)
              ·
                refine ⟨313036473029575161140156101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417381964039433548186874801 313036473029575161140156101)
                ·
                  refine ⟨58694338693045342713779269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313036473029575161140156101 58694338693045342713779269)
                  ·
                    refine ⟨11005188504946001758833613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58694338693045342713779269 11005188504946001758833613)
                    ·
                      refine ⟨4126945689354750659562605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005188504946001758833613 4126945689354750659562605)
                      ·
                        rfl

theorem cell23_8037198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_8037198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037198 prefixEnd_8037198 := by exact prefixLift 8037198
  have htrace : WordTrace (prefixWord ++ tailWord_8037198) baseStart_8037198 baseEnd_8037198 := by
    simpa [prefixWord, tailWord_8037198, baseEnd_8037198] using wordTrace_append hprefix tailTrace_8037198
  have hstable : (prefixWord ++ tailWord_8037198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037198).length < 2 ^ (prefixWord ++ tailWord_8037198).sum := by decide
  have hdescent : baseEnd_8037198 < baseStart_8037198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037248 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 2, 5]
def baseStart_8037248 : Nat := 118140960795 + 8037248 * 2 ^ 59
def prefixEnd_8037248 : Nat := 4983230072969 + 3 ^ 40 * 8037248 * 2
def baseEnd_8037248 : Nat := 1375657121129158487979125

theorem tailTrace_8037248 : CollatzResearch.WordTrace tailWord_8037248 prefixEnd_8037248 1375657121129158487979125 := by
  unfold tailWord_8037248
  simp only [CollatzResearch.WordTrace]
  refine ⟨146571258593215311760524199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195428344790953749014032265 146571258593215311760524199)
  ·
    refine ⟨219856887889822967640786299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146571258593215311760524199 219856887889822967640786299)
    ·
      refine ⟨329785331834734451461179449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219856887889822967640786299 329785331834734451461179449)
      ·
        refine ⟨247338998876050838595884587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329785331834734451461179449 247338998876050838595884587)
        ·
          refine ⟨371008498314076257893826881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247338998876050838595884587 371008498314076257893826881)
          ·
            refine ⟨278256373735557193420370161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371008498314076257893826881 278256373735557193420370161)
            ·
              refine ⟨208692280301667895065277621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278256373735557193420370161 208692280301667895065277621)
              ·
                refine ⟨19564901278281365162369777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208692280301667895065277621 19564901278281365162369777)
                ·
                  refine ⟨14673675958711023871777333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19564901278281365162369777 14673675958711023871777333)
                  ·
                    refine ⟨1375657121129158487979125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14673675958711023871777333 1375657121129158487979125)
                    ·
                      rfl

theorem cell23_8037248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 2, 5].length) (baseStart_8037248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037248 prefixEnd_8037248 := by exact prefixLift 8037248
  have htrace : WordTrace (prefixWord ++ tailWord_8037248) baseStart_8037248 baseEnd_8037248 := by
    simpa [prefixWord, tailWord_8037248, baseEnd_8037248] using wordTrace_append hprefix tailTrace_8037248
  have hstable : (prefixWord ++ tailWord_8037248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037248).length < 2 ^ (prefixWord ++ tailWord_8037248).sum := by decide
  have hdescent : baseEnd_8037248 < baseStart_8037248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037250 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_8037250 : Nat := 118140960795 + 8037250 * 2 ^ 59
def prefixEnd_8037250 : Nat := 4983230072969 + 3 ^ 40 * 8037250 * 2
def baseEnd_8037250 : Nat := 4126972390348784456112367

theorem tailTrace_8037250 : CollatzResearch.WordTrace tailWord_8037250 prefixEnd_8037250 4126972390348784456112367 := by
  unfold tailWord_8037250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73285647533105844465655301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195428393421615585241747469 73285647533105844465655301)
  ·
    refine ⟨13741058912457345837310369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73285647533105844465655301 13741058912457345837310369)
    ·
      refine ⟨10305794184343009377982777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13741058912457345837310369 10305794184343009377982777)
      ·
        refine ⟨7729345638257257033487083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10305794184343009377982777 7729345638257257033487083)
        ·
          refine ⟨11594018457385885550230625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729345638257257033487083 11594018457385885550230625)
          ·
            refine ⟨8695513843039414162672969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11594018457385885550230625 8695513843039414162672969)
            ·
              refine ⟨6521635382279560622004727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8695513843039414162672969 6521635382279560622004727)
              ·
                refine ⟨9782453073419340933007091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521635382279560622004727 9782453073419340933007091)
                ·
                  refine ⟨14673679610129011399510637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9782453073419340933007091 14673679610129011399510637)
                  ·
                    refine ⟨5502629853798379274816489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14673679610129011399510637 5502629853798379274816489)
                    ·
                      refine ⟨4126972390348784456112367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502629853798379274816489 4126972390348784456112367)
                      ·
                        rfl

theorem cell23_8037250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_8037250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037250 prefixEnd_8037250 := by exact prefixLift 8037250
  have htrace : WordTrace (prefixWord ++ tailWord_8037250) baseStart_8037250 baseEnd_8037250 := by
    simpa [prefixWord, tailWord_8037250, baseEnd_8037250] using wordTrace_append hprefix tailTrace_8037250
  have hstable : (prefixWord ++ tailWord_8037250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037250).length < 2 ^ (prefixWord ++ tailWord_8037250).sum := by decide
  have hdescent : baseEnd_8037250 < baseStart_8037250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037305 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 3]
def baseStart_8037305 : Nat := 118140960795 + 8037305 * 2 ^ 59
def prefixEnd_8037305 : Nat := 4983230072969 + 3 ^ 40 * 8037305 * 2
def baseEnd_8037305 : Nat := 4127000631784781740924613

theorem tailTrace_8037305 : CollatzResearch.WordTrace tailWord_8037305 prefixEnd_8037305 4127000631784781740924613 := by
  unfold tailWord_8037305
  simp only [CollatzResearch.WordTrace]
  refine ⟨293144596147224122255873369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195429730764816081503915579 293144596147224122255873369)
  ·
    refine ⟨219858447110418091691905027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293144596147224122255873369 219858447110418091691905027)
    ·
      refine ⟨329787670665627137537857541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219858447110418091691905027 329787670665627137537857541)
      ·
        refine ⟨61835188249805088288348289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329787670665627137537857541 61835188249805088288348289)
        ·
          refine ⟨46376391187353816216261217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61835188249805088288348289 46376391187353816216261217)
          ·
            refine ⟨34782293390515362162195913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46376391187353816216261217 34782293390515362162195913)
            ·
              refine ⟨26086720042886521621646935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34782293390515362162195913 26086720042886521621646935)
              ·
                refine ⟨39130080064329782432470403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26086720042886521621646935 39130080064329782432470403)
                ·
                  refine ⟨58695120096494673648705605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39130080064329782432470403 58695120096494673648705605)
                  ·
                    refine ⟨11005335018092751309132301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58695120096494673648705605 11005335018092751309132301)
                    ·
                      refine ⟨4127000631784781740924613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005335018092751309132301 4127000631784781740924613)
                      ·
                        rfl

theorem cell23_8037305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_8037305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037305 prefixEnd_8037305 := by exact prefixLift 8037305
  have htrace : WordTrace (prefixWord ++ tailWord_8037305) baseStart_8037305 baseEnd_8037305 := by
    simpa [prefixWord, tailWord_8037305, baseEnd_8037305] using wordTrace_append hprefix tailTrace_8037305
  have hstable : (prefixWord ++ tailWord_8037305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037305).length < 2 ^ (prefixWord ++ tailWord_8037305).sum := by decide
  have hdescent : baseEnd_8037305 < baseStart_8037305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037329 : List Nat := [1, 2, 2, 1, 2, 1, 7, 2, 1, 4]
def baseStart_8037329 : Nat := 118140960795 + 8037329 * 2 ^ 59
def prefixEnd_8037329 : Nat := 4983230072969 + 3 ^ 40 * 8037329 * 2
def baseEnd_8037329 : Nat := 1375670985106829882341501

theorem tailTrace_8037329 : CollatzResearch.WordTrace tailWord_8037329 prefixEnd_8037329 1375670985106829882341501 := by
  unfold tailWord_8037329
  simp only [CollatzResearch.WordTrace]
  refine ⟨293145471499137174354747041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195430314332758116236498027 293145471499137174354747041)
  ·
    refine ⟨219859103624352880766060281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293145471499137174354747041 219859103624352880766060281)
    ·
      refine ⟨164894327718264660574545211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219859103624352880766060281 164894327718264660574545211)
      ·
        refine ⟨247341491577396990861817817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164894327718264660574545211 247341491577396990861817817)
        ·
          refine ⟨185506118683047743146363363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247341491577396990861817817 185506118683047743146363363)
          ·
            refine ⟨278259178024571614719545045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185506118683047743146363363 278259178024571614719545045)
            ·
              refine ⟨6521699484950897219989337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278259178024571614719545045 6521699484950897219989337)
              ·
                refine ⟨4891274613713172914992003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6521699484950897219989337 4891274613713172914992003)
                ·
                  refine ⟨7336911920569759372488005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891274613713172914992003 7336911920569759372488005)
                  ·
                    refine ⟨1375670985106829882341501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336911920569759372488005 1375670985106829882341501)
                    ·
                      rfl

theorem cell23_8037329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_8037329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037329 prefixEnd_8037329 := by exact prefixLift 8037329
  have htrace : WordTrace (prefixWord ++ tailWord_8037329) baseStart_8037329 baseEnd_8037329 := by
    simpa [prefixWord, tailWord_8037329, baseEnd_8037329] using wordTrace_append hprefix tailTrace_8037329
  have hstable : (prefixWord ++ tailWord_8037329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037329).length < 2 ^ (prefixWord ++ tailWord_8037329).sum := by decide
  have hdescent : baseEnd_8037329 < baseStart_8037329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037348 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_8037348 : Nat := 118140960795 + 8037348 * 2 ^ 59
def prefixEnd_8037348 : Nat := 4983230072969 + 3 ^ 40 * 8037348 * 2
def baseEnd_8037348 : Nat := 4127022711452925072686915

theorem tailTrace_8037348 : CollatzResearch.WordTrace tailWord_8037348 prefixEnd_8037348 4127022711452925072686915 := by
  unfold tailWord_8037348
  simp only [CollatzResearch.WordTrace]
  refine ⟨146573082243034170299844349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195430776324045560399792465 146573082243034170299844349)
  ·
    refine ⟨54964905841137813862441631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146573082243034170299844349 54964905841137813862441631)
    ·
      refine ⟨82447358761706720793662447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54964905841137813862441631 82447358761706720793662447)
      ·
        refine ⟨123671038142560081190493671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82447358761706720793662447 123671038142560081190493671)
        ·
          refine ⟨185506557213840121785740507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123671038142560081190493671 185506557213840121785740507)
          ·
            refine ⟨278259835820760182678610761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185506557213840121785740507 278259835820760182678610761)
            ·
              refine ⟨208694876865570137008958071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278259835820760182678610761 208694876865570137008958071)
              ·
                refine ⟨313042315298355205513437107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208694876865570137008958071 313042315298355205513437107)
                ·
                  refine ⟨469563472947532808270155661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313042315298355205513437107 469563472947532808270155661)
                  ·
                    refine ⟨176086302355324803101308373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 469563472947532808270155661 176086302355324803101308373)
                    ·
                      refine ⟨4127022711452925072686915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176086302355324803101308373 4127022711452925072686915)
                      ·
                        rfl

theorem cell23_8037348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_8037348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037348 prefixEnd_8037348 := by exact prefixLift 8037348
  have htrace : WordTrace (prefixWord ++ tailWord_8037348) baseStart_8037348 baseEnd_8037348 := by
    simpa [prefixWord, tailWord_8037348, baseEnd_8037348] using wordTrace_append hprefix tailTrace_8037348
  have hstable : (prefixWord ++ tailWord_8037348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037348).length < 2 ^ (prefixWord ++ tailWord_8037348).sum := by decide
  have hdescent : baseEnd_8037348 < baseStart_8037348 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037352 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_8037352 : Nat := 118140960795 + 8037352 * 2 ^ 59
def prefixEnd_8037352 : Nat := 4983230072969 + 3 ^ 40 * 8037352 * 2
def baseEnd_8037352 : Nat := 4127024765375543057036897

theorem tailTrace_8037352 : CollatzResearch.WordTrace tailWord_8037352 prefixEnd_8037352 4127024765375543057036897 := by
  unfold tailWord_8037352
  simp only [CollatzResearch.WordTrace]
  refine ⟨146573155189026924641417155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195430873585369232855222873 146573155189026924641417155)
  ·
    refine ⟨219859732783540386962125733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146573155189026924641417155 219859732783540386962125733)
    ·
      refine ⟨41223699896913822555398575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219859732783540386962125733 41223699896913822555398575)
      ·
        refine ⟨61835549845370733833097863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41223699896913822555398575 61835549845370733833097863)
        ·
          refine ⟨92753324768056100749646795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61835549845370733833097863 92753324768056100749646795)
          ·
            refine ⟨139129987152084151124470193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92753324768056100749646795 139129987152084151124470193)
            ·
              refine ⟨104347490364063113343352645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139129987152084151124470193 104347490364063113343352645)
              ·
                refine ⟨19565154443261833751878621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104347490364063113343352645 19565154443261833751878621)
                ·
                  refine ⟨7336932916223187656954483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19565154443261833751878621 7336932916223187656954483)
                  ·
                    refine ⟨11005399374334781485431725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336932916223187656954483 11005399374334781485431725)
                    ·
                      refine ⟨4127024765375543057036897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005399374334781485431725 4127024765375543057036897)
                      ·
                        rfl

theorem cell23_8037352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_8037352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037352 prefixEnd_8037352 := by exact prefixLift 8037352
  have htrace : WordTrace (prefixWord ++ tailWord_8037352) baseStart_8037352 baseEnd_8037352 := by
    simpa [prefixWord, tailWord_8037352, baseEnd_8037352] using wordTrace_append hprefix tailTrace_8037352
  have hstable : (prefixWord ++ tailWord_8037352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037352).length < 2 ^ (prefixWord ++ tailWord_8037352).sum := by decide
  have hdescent : baseEnd_8037352 < baseStart_8037352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037369 : List Nat := [1, 2, 1, 3, 1, 3, 2, 5, 1, 1, 3]
def baseStart_8037369 : Nat := 118140960795 + 8037369 * 2 ^ 59
def prefixEnd_8037369 : Nat := 4983230072969 + 3 ^ 40 * 8037369 * 2
def baseEnd_8037369 : Nat := 4127033494546669490524319

theorem tailTrace_8037369 : CollatzResearch.WordTrace tailWord_8037369 prefixEnd_8037369 4127033494546669490524319 := by
  unfold tailWord_8037369
  simp only [CollatzResearch.WordTrace]
  refine ⟨293146930418992261186203161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195431286945994840790802107 293146930418992261186203161)
  ·
    refine ⟨219860197814244195889652371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293146930418992261186203161 219860197814244195889652371)
    ·
      refine ⟨329790296721366293834478557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219860197814244195889652371 329790296721366293834478557)
      ·
        refine ⟨123671361270512360187929459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329790296721366293834478557 123671361270512360187929459)
        ·
          refine ⟨185507041905768540281894189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123671361270512360187929459 185507041905768540281894189)
          ·
            refine ⟨69565140714663202605710321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185507041905768540281894189 69565140714663202605710321)
            ·
              refine ⟨52173855535997401954282741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69565140714663202605710321 52173855535997401954282741)
              ·
                refine ⟨4891298956499756433214007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52173855535997401954282741 4891298956499756433214007)
                ·
                  refine ⟨7336948434749634649821011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891298956499756433214007 7336948434749634649821011)
                  ·
                    refine ⟨11005422652124451974731517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336948434749634649821011 11005422652124451974731517)
                    ·
                      refine ⟨4127033494546669490524319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005422652124451974731517 4127033494546669490524319)
                      ·
                        rfl

theorem cell23_8037369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 5, 1, 1, 3].length) (baseStart_8037369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037369 prefixEnd_8037369 := by exact prefixLift 8037369
  have htrace : WordTrace (prefixWord ++ tailWord_8037369) baseStart_8037369 baseEnd_8037369 := by
    simpa [prefixWord, tailWord_8037369, baseEnd_8037369] using wordTrace_append hprefix tailTrace_8037369
  have hstable : (prefixWord ++ tailWord_8037369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037369).length < 2 ^ (prefixWord ++ tailWord_8037369).sum := by decide
  have hdescent : baseEnd_8037369 < baseStart_8037369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037385 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 4, 4]
def baseStart_8037385 : Nat := 118140960795 + 8037385 * 2 ^ 59
def prefixEnd_8037385 : Nat := 4983230072969 + 3 ^ 40 * 8037385 * 2
def baseEnd_8037385 : Nat := 1375680570079047142641415

theorem tailTrace_8037385 : CollatzResearch.WordTrace tailWord_8037385 prefixEnd_8037385 1375680570079047142641415 := by
  unfold tailWord_8037385
  simp only [CollatzResearch.WordTrace]
  refine ⟨293147513986934295918785609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195431675991289530612523739 293147513986934295918785609)
  ·
    refine ⟨219860635490200721939089207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293147513986934295918785609 219860635490200721939089207)
    ·
      refine ⟨329790953235301082908633811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219860635490200721939089207 329790953235301082908633811)
      ·
        refine ⟨494686429852951624362950717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329790953235301082908633811 494686429852951624362950717)
        ·
          refine ⟨185507411194856859136106519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494686429852951624362950717 185507411194856859136106519)
          ·
            refine ⟨278261116792285288704159779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185507411194856859136106519 278261116792285288704159779)
            ·
              refine ⟨417391675188427933056239669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278261116792285288704159779 417391675188427933056239669)
              ·
                refine ⟨39130469548915118724022469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417391675188427933056239669 39130469548915118724022469)
                ·
                  refine ⟨7336963040421584760754213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39130469548915118724022469 7336963040421584760754213)
                  ·
                    refine ⟨1375680570079047142641415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336963040421584760754213 1375680570079047142641415)
                    ·
                      rfl

theorem cell23_8037385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 4, 4].length) (baseStart_8037385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037385 prefixEnd_8037385 := by exact prefixLift 8037385
  have htrace : WordTrace (prefixWord ++ tailWord_8037385) baseStart_8037385 baseEnd_8037385 := by
    simpa [prefixWord, tailWord_8037385, baseEnd_8037385] using wordTrace_append hprefix tailTrace_8037385
  have hstable : (prefixWord ++ tailWord_8037385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037385).length < 2 ^ (prefixWord ++ tailWord_8037385).sum := by decide
  have hdescent : baseEnd_8037385 < baseStart_8037385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037386 : List Nat := [3, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_8037386 : Nat := 118140960795 + 8037386 * 2 ^ 59
def prefixEnd_8037386 : Nat := 4983230072969 + 3 ^ 40 * 8037386 * 2
def baseEnd_8037386 : Nat := 4127042223717795924011741

theorem tailTrace_8037386 : CollatzResearch.WordTrace tailWord_8037386 prefixEnd_8037386 4127042223717795924011741 := by
  unfold tailWord_8037386
  simp only [CollatzResearch.WordTrace]
  refine ⟨73286887614982668272393003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195431700306620448726381341 73286887614982668272393003)
  ·
    refine ⟨109930331422474002408589505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73286887614982668272393003 109930331422474002408589505)
    ·
      refine ⟨82447748566855501806442129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109930331422474002408589505 82447748566855501806442129)
      ·
        refine ⟨61835811425141626354831597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82447748566855501806442129 61835811425141626354831597)
        ·
          refine ⟨23188429284428109883061849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61835811425141626354831597 23188429284428109883061849)
          ·
            refine ⟨17391321963321082412296387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23188429284428109883061849 17391321963321082412296387)
            ·
              refine ⟨26086982944981623618444581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391321963321082412296387 26086982944981623618444581)
              ·
                refine ⟨4891309302184054428458359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26086982944981623618444581 4891309302184054428458359)
                ·
                  refine ⟨7336963953276081642687539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891309302184054428458359 7336963953276081642687539)
                  ·
                    refine ⟨11005445929914122464031309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7336963953276081642687539 11005445929914122464031309)
                    ·
                      refine ⟨4127042223717795924011741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005445929914122464031309 4127042223717795924011741)
                      ·
                        rfl

theorem cell23_8037386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_8037386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037386 prefixEnd_8037386 := by exact prefixLift 8037386
  have htrace : WordTrace (prefixWord ++ tailWord_8037386) baseStart_8037386 baseEnd_8037386 := by
    simpa [prefixWord, tailWord_8037386, baseEnd_8037386] using wordTrace_append hprefix tailTrace_8037386
  have hstable : (prefixWord ++ tailWord_8037386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037386).length < 2 ^ (prefixWord ++ tailWord_8037386).sum := by decide
  have hdescent : baseEnd_8037386 < baseStart_8037386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037402 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_8037402 : Nat := 118140960795 + 8037402 * 2 ^ 59
def prefixEnd_8037402 : Nat := 4983230072969 + 3 ^ 40 * 8037402 * 2
def baseEnd_8037402 : Nat := 1375683479802755953803889

theorem tailTrace_8037402 : CollatzResearch.WordTrace tailWord_8037402 prefixEnd_8037402 1375683479802755953803889 := by
  unfold tailWord_8037402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73287033506968176955538615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195432089351915138548102973 73287033506968176955538615)
  ·
    refine ⟨109930550260452265433307923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73287033506968176955538615 109930550260452265433307923)
    ·
      refine ⟨164895825390678398149961885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109930550260452265433307923 164895825390678398149961885)
      ·
        refine ⟨61835934521504399306235707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164895825390678398149961885 61835934521504399306235707)
        ·
          refine ⟨92753901782256598959353561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61835934521504399306235707 92753901782256598959353561)
          ·
            refine ⟨69565426336692449219515171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92753901782256598959353561 69565426336692449219515171)
            ·
              refine ⟨104348139505038673829272757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69565426336692449219515171 104348139505038673829272757)
              ·
                refine ⟨9782638078597375671494321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104348139505038673829272757 9782638078597375671494321)
                ·
                  refine ⟨7336978558948031753620741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9782638078597375671494321 7336978558948031753620741)
                  ·
                    refine ⟨1375683479802755953803889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7336978558948031753620741 1375683479802755953803889)
                    ·
                      rfl

theorem cell23_8037402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_8037402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037402 prefixEnd_8037402 := by exact prefixLift 8037402
  have htrace : WordTrace (prefixWord ++ tailWord_8037402) baseStart_8037402 baseEnd_8037402 := by
    simpa [prefixWord, tailWord_8037402, baseEnd_8037402] using wordTrace_append hprefix tailTrace_8037402
  have hstable : (prefixWord ++ tailWord_8037402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037402).length < 2 ^ (prefixWord ++ tailWord_8037402).sum := by decide
  have hdescent : baseEnd_8037402 < baseStart_8037402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037409 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 5, 2, 2]
def baseStart_8037409 : Nat := 118140960795 + 8037409 * 2 ^ 59
def prefixEnd_8037409 : Nat := 4983230072969 + 3 ^ 40 * 8037409 * 2
def baseEnd_8037409 : Nat := 4127054033772849334024135

theorem tailTrace_8037409 : CollatzResearch.WordTrace tailWord_8037409 prefixEnd_8037409 4127054033772849334024135 := by
  unfold tailWord_8037409
  simp only [CollatzResearch.WordTrace]
  refine ⟨293148389338847348017659281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195432259559231565345106187 293148389338847348017659281)
  ·
    refine ⟨219861292004135511013244461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293148389338847348017659281 219861292004135511013244461)
    ·
      refine ⟨82447984501550816629966673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219861292004135511013244461 82447984501550816629966673)
      ·
        refine ⟨61835988376163112472475005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82447984501550816629966673 61835988376163112472475005)
        ·
          refine ⟨23188495641061167177178127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61835988376163112472475005 23188495641061167177178127)
          ·
            refine ⟨34782743461591750765767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23188495641061167177178127 34782743461591750765767191)
            ·
              refine ⟨52174115192387626148650787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34782743461591750765767191 52174115192387626148650787)
              ·
                refine ⟨78261172788581439222976181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52174115192387626148650787 78261172788581439222976181)
                ·
                  refine ⟨7336984948929509927154017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78261172788581439222976181 7336984948929509927154017)
                  ·
                    refine ⟨5502738711697132445365513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336984948929509927154017 5502738711697132445365513)
                    ·
                      refine ⟨4127054033772849334024135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502738711697132445365513 4127054033772849334024135)
                      ·
                        rfl

theorem cell23_8037409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_8037409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037409 prefixEnd_8037409 := by exact prefixLift 8037409
  have htrace : WordTrace (prefixWord ++ tailWord_8037409) baseStart_8037409 baseEnd_8037409 := by
    simpa [prefixWord, tailWord_8037409, baseEnd_8037409] using wordTrace_append hprefix tailTrace_8037409
  have hstable : (prefixWord ++ tailWord_8037409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037409).length < 2 ^ (prefixWord ++ tailWord_8037409).sum := by decide
  have hdescent : baseEnd_8037409 < baseStart_8037409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037422 : List Nat := [4, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_8037422 : Nat := 118140960795 + 8037422 * 2 ^ 59
def prefixEnd_8037422 : Nat := 4983230072969 + 3 ^ 40 * 8037422 * 2
def baseEnd_8037422 : Nat := 4127060709021357783161575

theorem tailTrace_8037422 : CollatzResearch.WordTrace tailWord_8037422 prefixEnd_8037422 4127060709021357783161575 := by
  unfold tailWord_8037422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643607935975031404735315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195432575658533500825255013 36643607935975031404735315)
  ·
    refine ⟨54965411903962547107102973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643607935975031404735315 54965411903962547107102973)
    ·
      refine ⟨20612029463985955165163615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54965411903962547107102973 20612029463985955165163615)
      ·
        refine ⟨30918044195978932747745423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20612029463985955165163615 30918044195978932747745423)
        ·
          refine ⟨46377066293968399121618135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30918044195978932747745423 46377066293968399121618135)
          ·
            refine ⟨69565599440952598682427203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46377066293968399121618135 69565599440952598682427203)
            ·
              refine ⟨104348399161428898023640805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69565599440952598682427203 104348399161428898023640805)
              ·
                refine ⟨19565324842767918379432651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104348399161428898023640805 19565324842767918379432651)
                ·
                  refine ⟨29347987264151877569148977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19565324842767918379432651 29347987264151877569148977)
                  ·
                    refine ⟨22010990448113908176861733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29347987264151877569148977 22010990448113908176861733)
                    ·
                      refine ⟨4127060709021357783161575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22010990448113908176861733 4127060709021357783161575)
                      ·
                        rfl

theorem cell23_8037422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_8037422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037422 prefixEnd_8037422 := by exact prefixLift 8037422
  have htrace : WordTrace (prefixWord ++ tailWord_8037422) baseStart_8037422 baseEnd_8037422 := by
    simpa [prefixWord, tailWord_8037422, baseEnd_8037422] using wordTrace_append hprefix tailTrace_8037422
  have hstable : (prefixWord ++ tailWord_8037422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037422).length < 2 ^ (prefixWord ++ tailWord_8037422).sum := by decide
  have hdescent : baseEnd_8037422 < baseStart_8037422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037486 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_8037486 : Nat := 118140960795 + 8037486 * 2 ^ 59
def prefixEnd_8037486 : Nat := 4983230072969 + 3 ^ 40 * 8037486 * 2
def baseEnd_8037486 : Nat := 4127093571783245532761281

theorem tailTrace_8037486 : CollatzResearch.WordTrace tailWord_8037486 prefixEnd_8037486 4127093571783245532761281 := by
  unfold tailWord_8037486
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643899719946048771026539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195434131839712260112141541 36643899719946048771026539)
  ·
    refine ⟨54965849579919073156539809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36643899719946048771026539 54965849579919073156539809)
    ·
      refine ⟨41224387184939304867404857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54965849579919073156539809 41224387184939304867404857)
      ·
        refine ⟨30918290388704478650553643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41224387184939304867404857 30918290388704478650553643)
        ·
          refine ⟨46377435583056717975830465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30918290388704478650553643 46377435583056717975830465)
          ·
            refine ⟨34783076687292538481872849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46377435583056717975830465 34783076687292538481872849)
            ·
              refine ⟨26087307515469403861404637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34783076687292538481872849 26087307515469403861404637)
              ·
                refine ⟨9782740318301026448026739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26087307515469403861404637 9782740318301026448026739)
                ·
                  refine ⟨14674110477451539672040109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9782740318301026448026739 14674110477451539672040109)
                  ·
                    refine ⟨5502791429044327377015041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14674110477451539672040109 5502791429044327377015041)
                    ·
                      refine ⟨4127093571783245532761281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502791429044327377015041 4127093571783245532761281)
                      ·
                        rfl

theorem cell23_8037486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_8037486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037486 prefixEnd_8037486 := by exact prefixLift 8037486
  have htrace : WordTrace (prefixWord ++ tailWord_8037486) baseStart_8037486 baseEnd_8037486 := by
    simpa [prefixWord, tailWord_8037486, baseEnd_8037486] using wordTrace_append hprefix tailTrace_8037486
  have hstable : (prefixWord ++ tailWord_8037486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037486).length < 2 ^ (prefixWord ++ tailWord_8037486).sum := by decide
  have hdescent : baseEnd_8037486 < baseStart_8037486 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037589 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_8037589 : Nat := 118140960795 + 8037589 * 2 ^ 59
def prefixEnd_8037589 : Nat := 4983230072969 + 3 ^ 40 * 8037589 * 2
def baseEnd_8037589 : Nat := 4127146460290658629773307

theorem tailTrace_8037589 : CollatzResearch.WordTrace tailWord_8037589 prefixEnd_8037589 4127146460290658629773307 := by
  unfold tailWord_8037589
  simp only [CollatzResearch.WordTrace]
  refine ⟨293154954478195238759211821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195436636318796825839474547 293154954478195238759211821)
  ·
    refine ⟨109933107929323214534704433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293154954478195238759211821 109933107929323214534704433)
    ·
      refine ⟨82449830946992410901028325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109933107929323214534704433 82449830946992410901028325)
      ·
        refine ⟨15459343302561077043942811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82449830946992410901028325 15459343302561077043942811)
        ·
          refine ⟨23189014953841615565914217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15459343302561077043942811 23189014953841615565914217)
          ·
            refine ⟨17391761215381211674435663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23189014953841615565914217 17391761215381211674435663)
            ·
              refine ⟨26087641823071817511653495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391761215381211674435663 26087641823071817511653495)
              ·
                refine ⟨39131462734607726267480243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26087641823071817511653495 39131462734607726267480243)
                ·
                  refine ⟨58697194101911589401220365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39131462734607726267480243 58697194101911589401220365)
                  ·
                    refine ⟨22011447788216846025457637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58697194101911589401220365 22011447788216846025457637)
                    ·
                      refine ⟨4127146460290658629773307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22011447788216846025457637 4127146460290658629773307)
                      ·
                        rfl

theorem cell23_8037589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_8037589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037589 prefixEnd_8037589 := by exact prefixLift 8037589
  have htrace : WordTrace (prefixWord ++ tailWord_8037589) baseStart_8037589 baseEnd_8037589 := by
    simpa [prefixWord, tailWord_8037589, baseEnd_8037589] using wordTrace_append hprefix tailTrace_8037589
  have hstable : (prefixWord ++ tailWord_8037589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037589).length < 2 ^ (prefixWord ++ tailWord_8037589).sum := by decide
  have hdescent : baseEnd_8037589 < baseStart_8037589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037612 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 8]
def baseStart_8037612 : Nat := 118140960795 + 8037612 * 2 ^ 59
def prefixEnd_8037612 : Nat := 4983230072969 + 3 ^ 40 * 8037612 * 2
def baseEnd_8037612 : Nat := 458573141149523559976189

theorem tailTrace_8037612 : CollatzResearch.WordTrace tailWord_8037612 prefixEnd_8037612 458573141149523559976189 := by
  unfold tailWord_8037612
  simp only [CollatzResearch.WordTrace]
  refine ⟨146577896678555956843649545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195437195571407942458199393 146577896678555956843649545)
  ·
    refine ⟨109933422508916967632737159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146577896678555956843649545 109933422508916967632737159)
    ·
      refine ⟨164900133763375451449105739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109933422508916967632737159 164900133763375451449105739)
      ·
        refine ⟨247350200645063177173658609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164900133763375451449105739 247350200645063177173658609)
        ·
          refine ⟨185512650483797382880243957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247350200645063177173658609 185512650483797382880243957)
          ·
            refine ⟨17391810982856004645022871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185512650483797382880243957 17391810982856004645022871)
            ·
              refine ⟨26087716474284006967534307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391810982856004645022871 26087716474284006967534307)
              ·
                refine ⟨39131574711426010451301461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26087716474284006967534307 39131574711426010451301461)
                ·
                  refine ⟨458573141149523559976189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39131574711426010451301461 458573141149523559976189)
                  ·
                    rfl

theorem cell23_8037612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_8037612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037612 prefixEnd_8037612 := by exact prefixLift 8037612
  have htrace : WordTrace (prefixWord ++ tailWord_8037612) baseStart_8037612 baseEnd_8037612 := by
    simpa [prefixWord, tailWord_8037612, baseEnd_8037612] using wordTrace_append hprefix tailTrace_8037612
  have hstable : (prefixWord ++ tailWord_8037612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037612).length < 2 ^ (prefixWord ++ tailWord_8037612).sum := by decide
  have hdescent : baseEnd_8037612 < baseStart_8037612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037649 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 1, 5, 2]
def baseStart_8037649 : Nat := 118140960795 + 8037649 * 2 ^ 59
def prefixEnd_8037649 : Nat := 4983230072969 + 3 ^ 40 * 8037649 * 2
def baseEnd_8037649 : Nat := 4127177269129928395023031

theorem tailTrace_8037649 : CollatzResearch.WordTrace tailWord_8037649 prefixEnd_8037649 4127177269129928395023031 := by
  unfold tailWord_8037649
  simp only [CollatzResearch.WordTrace]
  refine ⟨293157142857977869006396001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195438095238651912670930667 293157142857977869006396001)
  ·
    refine ⟨219867857143483401754797001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293157142857977869006396001 219867857143483401754797001)
    ·
      refine ⟨164900892857612551316097751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219867857143483401754797001 164900892857612551316097751)
      ·
        refine ⟨247351339286418826974146627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164900892857612551316097751 247351339286418826974146627)
        ·
          refine ⟨371027008929628240461219941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247351339286418826974146627 371027008929628240461219941)
          ·
            refine ⟨69567564174305295086478739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371027008929628240461219941 69567564174305295086478739)
            ·
              refine ⟨104351346261457942629718109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69567564174305295086478739 104351346261457942629718109)
              ·
                refine ⟨39131754848046728486144291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104351346261457942629718109 39131754848046728486144291)
                ·
                  refine ⟨58697632272070092729216437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39131754848046728486144291 58697632272070092729216437)
                  ·
                    refine ⟨5502903025506571193364041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58697632272070092729216437 5502903025506571193364041)
                    ·
                      refine ⟨4127177269129928395023031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502903025506571193364041 4127177269129928395023031)
                      ·
                        rfl

theorem cell23_8037649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 5, 2].length) (baseStart_8037649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037649 prefixEnd_8037649 := by exact prefixLift 8037649
  have htrace : WordTrace (prefixWord ++ tailWord_8037649) baseStart_8037649 baseEnd_8037649 := by
    simpa [prefixWord, tailWord_8037649, baseEnd_8037649] using wordTrace_append hprefix tailTrace_8037649
  have hstable : (prefixWord ++ tailWord_8037649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037649).length < 2 ^ (prefixWord ++ tailWord_8037649).sum := by decide
  have hdescent : baseEnd_8037649 < baseStart_8037649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037696 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2]
def baseStart_8037696 : Nat := 118140960795 + 8037696 * 2 ^ 59
def prefixEnd_8037696 : Nat := 4983230072969 + 3 ^ 40 * 8037696 * 2
def baseEnd_8037696 : Nat := 4127201402720689711135315

theorem tailTrace_8037696 : CollatzResearch.WordTrace tailWord_8037696 prefixEnd_8037696 4127201402720689711135315 := by
  unfold tailWord_8037696
  simp only [CollatzResearch.WordTrace]
  refine ⟨146579428544403798016678471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195439238059205064022237961 146579428544403798016678471)
  ·
    refine ⟨219869142816605697025017707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146579428544403798016678471 219869142816605697025017707)
    ·
      refine ⟨329803714224908545537526561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219869142816605697025017707 329803714224908545537526561)
      ·
        refine ⟨247352785668681409153144921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329803714224908545537526561 247352785668681409153144921)
        ·
          refine ⟨185514589251511056864858691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247352785668681409153144921 185514589251511056864858691)
          ·
            refine ⟨278271883877266585297288037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185514589251511056864858691 278271883877266585297288037)
            ·
              refine ⟨52175978226987484743241507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278271883877266585297288037 52175978226987484743241507)
              ·
                refine ⟨78263967340481227114862261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52175978226987484743241507 78263967340481227114862261)
                ·
                  refine ⟨7337246938170115042018337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78263967340481227114862261 7337246938170115042018337)
                  ·
                    refine ⟨5502935203627586281513753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337246938170115042018337 5502935203627586281513753)
                    ·
                      refine ⟨4127201402720689711135315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502935203627586281513753 4127201402720689711135315)
                      ·
                        rfl

theorem cell23_8037696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_8037696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037696 prefixEnd_8037696 := by exact prefixLift 8037696
  have htrace : WordTrace (prefixWord ++ tailWord_8037696) baseStart_8037696 baseEnd_8037696 := by
    simpa [prefixWord, tailWord_8037696, baseEnd_8037696] using wordTrace_append hprefix tailTrace_8037696
  have hstable : (prefixWord ++ tailWord_8037696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037696).length < 2 ^ (prefixWord ++ tailWord_8037696).sum := by decide
  have hdescent : baseEnd_8037696 < baseStart_8037696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037700 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_8037700 : Nat := 118140960795 + 8037700 * 2 ^ 59
def prefixEnd_8037700 : Nat := 4983230072969 + 3 ^ 40 * 8037700 * 2
def baseEnd_8037700 : Nat := 4127203456643307695485297

theorem tailTrace_8037700 : CollatzResearch.WordTrace tailWord_8037700 prefixEnd_8037700 4127203456643307695485297 := by
  unfold tailWord_8037700
  simp only [CollatzResearch.WordTrace]
  refine ⟨146579501490396552358251277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195439335320528736477668369 146579501490396552358251277)
  ·
    refine ⟨54967313058898707134344229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146579501490396552358251277 54967313058898707134344229)
    ·
      refine ⟨10306371198543507587689543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54967313058898707134344229 10306371198543507587689543)
      ·
        refine ⟨15459556797815261381534315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306371198543507587689543 15459556797815261381534315)
        ·
          refine ⟨23189335196722892072301473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15459556797815261381534315 23189335196722892072301473)
          ·
            refine ⟨17392001397542169054226105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23189335196722892072301473 17392001397542169054226105)
            ·
              refine ⟨13044001048156626790669579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17392001397542169054226105 13044001048156626790669579)
              ·
                refine ⟨19566001572234940186004369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13044001048156626790669579 19566001572234940186004369)
                ·
                  refine ⟨14674501179176205139503277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19566001572234940186004369 14674501179176205139503277)
                  ·
                    refine ⟨5502937942191076927313729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14674501179176205139503277 5502937942191076927313729)
                    ·
                      refine ⟨4127203456643307695485297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502937942191076927313729 4127203456643307695485297)
                      ·
                        rfl

theorem cell23_8037700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_8037700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037700 prefixEnd_8037700 := by exact prefixLift 8037700
  have htrace : WordTrace (prefixWord ++ tailWord_8037700) baseStart_8037700 baseEnd_8037700 := by
    simpa [prefixWord, tailWord_8037700, baseEnd_8037700] using wordTrace_append hprefix tailTrace_8037700
  have hstable : (prefixWord ++ tailWord_8037700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037700).length < 2 ^ (prefixWord ++ tailWord_8037700).sum := by decide
  have hdescent : baseEnd_8037700 < baseStart_8037700 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037718 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_8037718 : Nat := 118140960795 + 8037718 * 2 ^ 59
def prefixEnd_8037718 : Nat := 4983230072969 + 3 ^ 40 * 8037718 * 2
def baseEnd_8037718 : Nat := 1375737566431696208353405

theorem tailTrace_8037718 : CollatzResearch.WordTrace tailWord_8037718 prefixEnd_8037718 1375737566431696208353405 := by
  unfold tailWord_8037718
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322478718420493361916113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195439772996485262527105205 18322478718420493361916113)
  ·
    refine ⟨13741859038815370021437085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18322478718420493361916113 13741859038815370021437085)
    ·
      refine ⟨5153197139555763758038907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13741859038815370021437085 5153197139555763758038907)
      ·
        refine ⟨7729795709333645637058361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5153197139555763758038907 7729795709333645637058361)
        ·
          refine ⟨5797346782000234227793771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7729795709333645637058361 5797346782000234227793771)
          ·
            refine ⟨8696020173000351341690657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797346782000234227793771 8696020173000351341690657)
            ·
              refine ⟨6522015129750263506267993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8696020173000351341690657 6522015129750263506267993)
              ·
                refine ⟨4891511347312697629700995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6522015129750263506267993 4891511347312697629700995)
                ·
                  refine ⟨7337267020969046444551493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891511347312697629700995 7337267020969046444551493)
                  ·
                    refine ⟨1375737566431696208353405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337267020969046444551493 1375737566431696208353405)
                    ·
                      rfl

theorem cell23_8037718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_8037718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037718 prefixEnd_8037718 := by exact prefixLift 8037718
  have htrace : WordTrace (prefixWord ++ tailWord_8037718) baseStart_8037718 baseEnd_8037718 := by
    simpa [prefixWord, tailWord_8037718, baseEnd_8037718] using wordTrace_append hprefix tailTrace_8037718
  have hstable : (prefixWord ++ tailWord_8037718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037718).length < 2 ^ (prefixWord ++ tailWord_8037718).sum := by decide
  have hdescent : baseEnd_8037718 < baseStart_8037718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037736 : List Nat := [2, 1, 4, 2, 3, 2, 1, 8]
def baseStart_8037736 : Nat := 118140960795 + 8037736 * 2 ^ 59
def prefixEnd_8037736 : Nat := 4983230072969 + 3 ^ 40 * 8037736 * 2
def baseEnd_8037736 : Nat := 152860071923958131653153

theorem tailTrace_8037736 : CollatzResearch.WordTrace tailWord_8037736 prefixEnd_8037736 152860071923958131653153 := by
  unfold tailWord_8037736
  simp only [CollatzResearch.WordTrace]
  refine ⟨146580158004331341432406531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195440210672441788576542041 146580158004331341432406531)
  ·
    refine ⟨219870237006497012148609797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146580158004331341432406531 219870237006497012148609797)
    ·
      refine ⟨41225669438718189777864337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219870237006497012148609797 41225669438718189777864337)
      ·
        refine ⟨30919252079038642333398253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41225669438718189777864337 30919252079038642333398253)
        ·
          refine ⟨11594719529639490875024345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30919252079038642333398253 11594719529639490875024345)
          ·
            refine ⟨8696039647229618156268259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11594719529639490875024345 8696039647229618156268259)
            ·
              refine ⟨13044059470844427234402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696039647229618156268259 13044059470844427234402389)
              ·
                refine ⟨152860071923958131653153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13044059470844427234402389 152860071923958131653153)
                ·
                  rfl

theorem cell23_8037736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 8].length) (baseStart_8037736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037736 prefixEnd_8037736 := by exact prefixLift 8037736
  have htrace : WordTrace (prefixWord ++ tailWord_8037736) baseStart_8037736 baseEnd_8037736 := by
    simpa [prefixWord, tailWord_8037736, baseEnd_8037736] using wordTrace_append hprefix tailTrace_8037736
  have hstable : (prefixWord ++ tailWord_8037736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037736).length < 2 ^ (prefixWord ++ tailWord_8037736).sum := by decide
  have hdescent : baseEnd_8037736 < baseStart_8037736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037739 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 1, 9, 2]
def baseStart_8037739 : Nat := 118140960795 + 8037739 * 2 ^ 59
def prefixEnd_8037739 : Nat := 4983230072969 + 3 ^ 40 * 8037739 * 2
def baseEnd_8037739 : Nat := 4127223482388833042897617

theorem tailTrace_8037739 : CollatzResearch.WordTrace tailWord_8037739 prefixEnd_8037739 4127223482388833042897617 := by
  unfold tailWord_8037739
  simp only [CollatzResearch.WordTrace]
  refine ⟨293160425427651814377172271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195440283618434542918114847 293160425427651814377172271)
  ·
    refine ⟨439740638141477721565758407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293160425427651814377172271 439740638141477721565758407)
    ·
      refine ⟨659610957212216582348637611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439740638141477721565758407 659610957212216582348637611)
      ·
        refine ⟨989416435818324873522956417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659610957212216582348637611 989416435818324873522956417)
        ·
          refine ⟨742062326863743655142217313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989416435818324873522956417 742062326863743655142217313)
          ·
            refine ⟨556546745147807741356662985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742062326863743655142217313 556546745147807741356662985)
            ·
              refine ⟨417410058860855806017497239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556546745147807741356662985 417410058860855806017497239)
              ·
                refine ⟨626115088291283709026245859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417410058860855806017497239 626115088291283709026245859)
                ·
                  refine ⟨939172632436925563539368789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626115088291283709026245859 939172632436925563539368789)
                  ·
                    refine ⟨5502964643185110723863489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 939172632436925563539368789 5502964643185110723863489)
                    ·
                      refine ⟨4127223482388833042897617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502964643185110723863489 4127223482388833042897617)
                      ·
                        rfl

theorem cell23_8037739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 9, 2].length) (baseStart_8037739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037739 prefixEnd_8037739 := by exact prefixLift 8037739
  have htrace : WordTrace (prefixWord ++ tailWord_8037739) baseStart_8037739 baseEnd_8037739 := by
    simpa [prefixWord, tailWord_8037739, baseEnd_8037739] using wordTrace_append hprefix tailTrace_8037739
  have hstable : (prefixWord ++ tailWord_8037739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037739).length < 2 ^ (prefixWord ++ tailWord_8037739).sum := by decide
  have hdescent : baseEnd_8037739 < baseStart_8037739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037746 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 1, 3, 3]
def baseStart_8037746 : Nat := 118140960795 + 8037746 * 2 ^ 59
def prefixEnd_8037746 : Nat := 4983230072969 + 3 ^ 40 * 8037746 * 2
def baseEnd_8037746 : Nat := 4127227076753414515510085

theorem tailTrace_8037746 : CollatzResearch.WordTrace tailWord_8037746 prefixEnd_8037746 4127227076753414515510085 := by
  unfold tailWord_8037746
  simp only [CollatzResearch.WordTrace]
  refine ⟨73290170184656613643169273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195440453825750969715118061 73290170184656613643169273)
  ·
    refine ⟨54967627638492460232376955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73290170184656613643169273 54967627638492460232376955)
    ·
      refine ⟨82451441457738690348565433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54967627638492460232376955 82451441457738690348565433)
      ·
        refine ⟨61838581093304017761424075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82451441457738690348565433 61838581093304017761424075)
        ·
          refine ⟨92757871639956026642136113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61838581093304017761424075 92757871639956026642136113)
          ·
            refine ⟨69568403729967019981602085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92757871639956026642136113 69568403729967019981602085)
            ·
              refine ⟨13044075699368816246550391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69568403729967019981602085 13044075699368816246550391)
              ·
                refine ⟨19566113549053224369825587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13044075699368816246550391 19566113549053224369825587)
                ·
                  refine ⟨29349170323579836554738381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19566113549053224369825587 29349170323579836554738381)
                  ·
                    refine ⟨11005938871342438708026893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29349170323579836554738381 11005938871342438708026893)
                    ·
                      refine ⟨4127227076753414515510085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005938871342438708026893 4127227076753414515510085)
                      ·
                        rfl

theorem cell23_8037746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_8037746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037746 prefixEnd_8037746 := by exact prefixLift 8037746
  have htrace : WordTrace (prefixWord ++ tailWord_8037746) baseStart_8037746 baseEnd_8037746 := by
    simpa [prefixWord, tailWord_8037746, baseEnd_8037746] using wordTrace_append hprefix tailTrace_8037746
  have hstable : (prefixWord ++ tailWord_8037746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037746).length < 2 ^ (prefixWord ++ tailWord_8037746).sum := by decide
  have hdescent : baseEnd_8037746 < baseStart_8037746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037756 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_8037756 : Nat := 118140960795 + 8037756 * 2 ^ 59
def prefixEnd_8037756 : Nat := 4983230072969 + 3 ^ 40 * 8037756 * 2
def baseEnd_8037756 : Nat := 4127232211559959476385039

theorem tailTrace_8037756 : CollatzResearch.WordTrace tailWord_8037756 prefixEnd_8037756 4127232211559959476385039 := by
  unfold tailWord_8037756
  simp only [CollatzResearch.WordTrace]
  refine ⟨146580522734295113140270561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195440696979060150853694081 146580522734295113140270561)
  ·
    refine ⟨109935392050721334855202921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146580522734295113140270561 109935392050721334855202921)
    ·
      refine ⟨82451544038041001141402191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109935392050721334855202921 82451544038041001141402191)
      ·
        refine ⟨123677316057061501712103287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82451544038041001141402191 123677316057061501712103287)
        ·
          refine ⟨185515974085592252568154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123677316057061501712103287 185515974085592252568154931)
          ·
            refine ⟨278273961128388378852232397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185515974085592252568154931 278273961128388378852232397)
            ·
              refine ⟨104352735423145642069587149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278273961128388378852232397 104352735423145642069587149)
              ·
                refine ⟨39132275783679615776095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104352735423145642069587149 39132275783679615776095181)
                ·
                  refine ⟨14674603418879855916035693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39132275783679615776095181 14674603418879855916035693)
                  ·
                    refine ⟨5502976282079945968513385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14674603418879855916035693 5502976282079945968513385)
                    ·
                      refine ⟨4127232211559959476385039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5502976282079945968513385 4127232211559959476385039)
                      ·
                        rfl

theorem cell23_8037756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_8037756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037756 prefixEnd_8037756 := by exact prefixLift 8037756
  have htrace : WordTrace (prefixWord ++ tailWord_8037756) baseStart_8037756 baseEnd_8037756 := by
    simpa [prefixWord, tailWord_8037756, baseEnd_8037756] using wordTrace_append hprefix tailTrace_8037756
  have hstable : (prefixWord ++ tailWord_8037756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037756).length < 2 ^ (prefixWord ++ tailWord_8037756).sum := by decide
  have hdescent : baseEnd_8037756 < baseStart_8037756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037780 : List Nat := [2, 4, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_8037780 : Nat := 118140960795 + 8037780 * 2 ^ 59
def prefixEnd_8037780 : Nat := 4983230072969 + 3 ^ 40 * 8037780 * 2
def baseEnd_8037780 : Nat := 4127244535095667382484929

theorem tailTrace_8037780 : CollatzResearch.WordTrace tailWord_8037780 prefixEnd_8037780 4127244535095667382484929 := by
  unfold tailWord_8037780
  simp only [CollatzResearch.WordTrace]
  refine ⟨146580960410251639189707397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195441280547002185586276529 146580960410251639189707397)
  ·
    refine ⟨27483930076922182348070137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146580960410251639189707397 27483930076922182348070137)
    ·
      refine ⟨20612947557691636761052603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27483930076922182348070137 20612947557691636761052603)
      ·
        refine ⟨30919421336537455141578905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20612947557691636761052603 30919421336537455141578905)
        ·
          refine ⟨23189566002403091356184179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30919421336537455141578905 23189566002403091356184179)
          ·
            refine ⟨34784349003604637034276269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23189566002403091356184179 34784349003604637034276269)
            ·
              refine ⟨13044130876351738887853601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34784349003604637034276269 13044130876351738887853601)
              ·
                refine ⟨9783098157263804165890201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044130876351738887853601 9783098157263804165890201)
                ·
                  refine ⟨7337323617947853124417651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783098157263804165890201 7337323617947853124417651)
                  ·
                    refine ⟨11005985426921779686626477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337323617947853124417651 11005985426921779686626477)
                    ·
                      refine ⟨4127244535095667382484929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11005985426921779686626477 4127244535095667382484929)
                      ·
                        rfl

theorem cell23_8037780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_8037780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037780 prefixEnd_8037780 := by exact prefixLift 8037780
  have htrace : WordTrace (prefixWord ++ tailWord_8037780) baseStart_8037780 baseEnd_8037780 := by
    simpa [prefixWord, tailWord_8037780, baseEnd_8037780] using wordTrace_append hprefix tailTrace_8037780
  have hstable : (prefixWord ++ tailWord_8037780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037780).length < 2 ^ (prefixWord ++ tailWord_8037780).sum := by decide
  have hdescent : baseEnd_8037780 < baseStart_8037780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037809 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 7]
def baseStart_8037809 : Nat := 118140960795 + 8037809 * 2 ^ 59
def prefixEnd_8037809 : Nat := 4983230072969 + 3 ^ 40 * 8037809 * 2
def baseEnd_8037809 : Nat := 458584380670516418780255

theorem tailTrace_8037809 : CollatzResearch.WordTrace tailWord_8037809 prefixEnd_8037809 458584380670516418780255 := by
  unfold tailWord_8037809
  simp only [CollatzResearch.WordTrace]
  refine ⟨293162978537398216332220481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195441985691598810888146987 293162978537398216332220481)
  ·
    refine ⟨219872233903048662249165361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293162978537398216332220481 219872233903048662249165361)
    ·
      refine ⟨164904175427286496686874021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219872233903048662249165361 164904175427286496686874021)
      ·
        refine ⟨30919532892616218128788879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164904175427286496686874021 30919532892616218128788879)
        ·
          refine ⟨46379299338924327193183319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30919532892616218128788879 46379299338924327193183319)
          ·
            refine ⟨69568949008386490789774979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46379299338924327193183319 69568949008386490789774979)
            ·
              refine ⟨104353423512579736184662469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69568949008386490789774979 104353423512579736184662469)
              ·
                refine ⟨19566266908608700534624213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104353423512579736184662469 19566266908608700534624213)
                ·
                  refine ⟨458584380670516418780255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19566266908608700534624213 458584380670516418780255)
                  ·
                    rfl

theorem cell23_8037809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 7].length) (baseStart_8037809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037809 prefixEnd_8037809 := by exact prefixLift 8037809
  have htrace : WordTrace (prefixWord ++ tailWord_8037809) baseStart_8037809 baseEnd_8037809 := by
    simpa [prefixWord, tailWord_8037809, baseEnd_8037809] using wordTrace_append hprefix tailTrace_8037809
  have hstable : (prefixWord ++ tailWord_8037809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037809).length < 2 ^ (prefixWord ++ tailWord_8037809).sum := by decide
  have hdescent : baseEnd_8037809 < baseStart_8037809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037839 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 4, 5]
def baseStart_8037839 : Nat := 118140960795 + 8037839 * 2 ^ 59
def prefixEnd_8037839 : Nat := 4983230072969 + 3 ^ 40 * 8037839 * 2
def baseEnd_8037839 : Nat := 1375758276818094217215719

theorem tailTrace_8037839 : CollatzResearch.WordTrace tailWord_8037839 prefixEnd_8037839 1375758276818094217215719 := by
  unfold tailWord_8037839
  simp only [CollatzResearch.WordTrace]
  refine ⟨293164072727289531455812571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195442715151526354303875047 293164072727289531455812571)
  ·
    refine ⟨439746109090934297183718857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293164072727289531455812571 439746109090934297183718857)
    ·
      refine ⟨329809581818200722887789143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439746109090934297183718857 329809581818200722887789143)
      ·
        refine ⟨494714372727301084331683715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329809581818200722887789143 494714372727301084331683715)
        ·
          refine ⟨742071559090951626497525573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494714372727301084331683715 742071559090951626497525573)
          ·
            refine ⟨139138417329553429968286045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 742071559090951626497525573 139138417329553429968286045)
            ·
              refine ⟨52176906498582536238107267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139138417329553429968286045 52176906498582536238107267)
              ·
                refine ⟨78265359747873804357160901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52176906498582536238107267 78265359747873804357160901)
                ·
                  refine ⟨14674754952726338316967669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78265359747873804357160901 14674754952726338316967669)
                  ·
                    refine ⟨1375758276818094217215719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14674754952726338316967669 1375758276818094217215719)
                    ·
                      rfl

theorem cell23_8037839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 5].length) (baseStart_8037839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037839 prefixEnd_8037839 := by exact prefixLift 8037839
  have htrace : WordTrace (prefixWord ++ tailWord_8037839) baseStart_8037839 baseEnd_8037839 := by
    simpa [prefixWord, tailWord_8037839, baseEnd_8037839] using wordTrace_append hprefix tailTrace_8037839
  have hstable : (prefixWord ++ tailWord_8037839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037839).length < 2 ^ (prefixWord ++ tailWord_8037839).sum := by decide
  have hdescent : baseEnd_8037839 < baseStart_8037839 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037849 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 7]
def baseStart_8037849 : Nat := 118140960795 + 8037849 * 2 ^ 59
def prefixEnd_8037849 : Nat := 4983230072969 + 3 ^ 40 * 8037849 * 2
def baseEnd_8037849 : Nat := 4127279965260827612522111

theorem tailTrace_8037849 : CollatzResearch.WordTrace tailWord_8037849 prefixEnd_8037849 4127279965260827612522111 := by
  unfold tailWord_8037849
  simp only [CollatzResearch.WordTrace]
  refine ⟨293164437457253303163676601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195442958304835535442451067 293164437457253303163676601)
  ·
    refine ⟨219873328092939977372757451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293164437457253303163676601 219873328092939977372757451)
    ·
      refine ⟨329809992139409966059136177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219873328092939977372757451 329809992139409966059136177)
      ·
        refine ⟨247357494104557474544352133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329809992139409966059136177 247357494104557474544352133)
        ·
          refine ⟨46379530144604526477066025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247357494104557474544352133 46379530144604526477066025)
          ·
            refine ⟨34784647608453394857799519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46379530144604526477066025 34784647608453394857799519)
            ·
              refine ⟨52176971412680092286699279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34784647608453394857799519 52176971412680092286699279)
              ·
                refine ⟨78265457119020138430048919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52176971412680092286699279 78265457119020138430048919)
                ·
                  refine ⟨117398185678530207645073379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78265457119020138430048919 117398185678530207645073379)
                  ·
                    refine ⟨176097278517795311467610069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117398185678530207645073379 176097278517795311467610069)
                    ·
                      refine ⟨4127279965260827612522111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176097278517795311467610069 4127279965260827612522111)
                      ·
                        rfl

theorem cell23_8037849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_8037849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037849 prefixEnd_8037849 := by exact prefixLift 8037849
  have htrace : WordTrace (prefixWord ++ tailWord_8037849) baseStart_8037849 baseEnd_8037849 := by
    simpa [prefixWord, tailWord_8037849, baseEnd_8037849] using wordTrace_append hprefix tailTrace_8037849
  have hstable : (prefixWord ++ tailWord_8037849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037849).length < 2 ^ (prefixWord ++ tailWord_8037849).sum := by decide
  have hdescent : baseEnd_8037849 < baseStart_8037849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037894 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_8037894 : Nat := 118140960795 + 8037894 * 2 ^ 59
def prefixEnd_8037894 : Nat := 4983230072969 + 3 ^ 40 * 8037894 * 2
def baseEnd_8037894 : Nat := 458589230210031104051045

theorem tailTrace_8037894 : CollatzResearch.WordTrace tailWord_8037894 prefixEnd_8037894 458589230210031104051045 := by
  unfold tailWord_8037894
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161439960690321120283273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195444052494726850566043157 9161439960690321120283273)
  ·
    refine ⟨6871079970517740840212455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9161439960690321120283273 6871079970517740840212455)
    ·
      refine ⟨10306619955776611260318683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871079970517740840212455 10306619955776611260318683)
      ·
        refine ⟨15459929933664916890478025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306619955776611260318683 15459929933664916890478025)
        ·
          refine ⟨11594947450248687667858519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15459929933664916890478025 11594947450248687667858519)
          ·
            refine ⟨17392421175373031501787779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11594947450248687667858519 17392421175373031501787779)
            ·
              refine ⟨26088631763059547252681669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17392421175373031501787779 26088631763059547252681669)
              ·
                refine ⟨4891618455573665109877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26088631763059547252681669 4891618455573665109877813)
                ·
                  refine ⟨458589230210031104051045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891618455573665109877813 458589230210031104051045)
                  ·
                    rfl

theorem cell23_8037894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_8037894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037894 prefixEnd_8037894 := by exact prefixLift 8037894
  have htrace : WordTrace (prefixWord ++ tailWord_8037894) baseStart_8037894 baseEnd_8037894 := by
    simpa [prefixWord, tailWord_8037894, baseEnd_8037894] using wordTrace_append hprefix tailTrace_8037894
  have hstable : (prefixWord ++ tailWord_8037894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037894).length < 2 ^ (prefixWord ++ tailWord_8037894).sum := by decide
  have hdescent : baseEnd_8037894 < baseStart_8037894 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037916 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 6]
def baseStart_8037916 : Nat := 118140960795 + 8037916 * 2 ^ 59
def prefixEnd_8037916 : Nat := 4983230072969 + 3 ^ 40 * 8037916 * 2
def baseEnd_8037916 : Nat := 458590485384964316709367

theorem tailTrace_8037916 : CollatzResearch.WordTrace tailWord_8037916 prefixEnd_8037916 458590485384964316709367 := by
  unfold tailWord_8037916
  simp only [CollatzResearch.WordTrace]
  refine ⟨146583440574005286803182801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195444587432007049070910401 146583440574005286803182801)
  ·
    refine ⟨109937580430503965102387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146583440574005286803182801 109937580430503965102387101)
    ·
      refine ⟨41226592661438986913395163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109937580430503965102387101 41226592661438986913395163)
      ·
        refine ⟨61839888992158480370092745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41226592661438986913395163 61839888992158480370092745)
        ·
          refine ⟨46379916744118860277569559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61839888992158480370092745 46379916744118860277569559)
          ·
            refine ⟨69569875116178290416354339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46379916744118860277569559 69569875116178290416354339)
            ·
              refine ⟨104354812674267435624531509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69569875116178290416354339 104354812674267435624531509)
              ·
                refine ⟨9783263688212572089799829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104354812674267435624531509 9783263688212572089799829)
                ·
                  refine ⟨458590485384964316709367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9783263688212572089799829 458590485384964316709367)
                  ·
                    rfl

theorem cell23_8037916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_8037916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037916 prefixEnd_8037916 := by exact prefixLift 8037916
  have htrace : WordTrace (prefixWord ++ tailWord_8037916) baseStart_8037916 baseEnd_8037916 := by
    simpa [prefixWord, tailWord_8037916, baseEnd_8037916] using wordTrace_append hprefix tailTrace_8037916
  have hstable : (prefixWord ++ tailWord_8037916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037916).length < 2 ^ (prefixWord ++ tailWord_8037916).sum := by decide
  have hdescent : baseEnd_8037916 < baseStart_8037916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037980 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_8037980 : Nat := 118140960795 + 8037980 * 2 ^ 59
def prefixEnd_8037980 : Nat := 4983230072969 + 3 ^ 40 * 8037980 * 2
def baseEnd_8037980 : Nat := 1375782410408855533328003

theorem tailTrace_8037980 : CollatzResearch.WordTrace tailWord_8037980 prefixEnd_8037980 1375782410408855533328003 := by
  unfold tailWord_8037980
  simp only [CollatzResearch.WordTrace]
  refine ⟨146584607709889356268347697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195446143613185808357796929 146584607709889356268347697)
  ·
    refine ⟨109938455782417017201260773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146584607709889356268347697 109938455782417017201260773)
    ·
      refine ⟨20613460459203190725236395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109938455782417017201260773 20613460459203190725236395)
      ·
        refine ⟨30920190688804786087854593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20613460459203190725236395 30920190688804786087854593)
        ·
          refine ⟨23190143016603589565890945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30920190688804786087854593 23190143016603589565890945)
          ·
            refine ⟨17392607262452692174418209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23190143016603589565890945 17392607262452692174418209)
            ·
              refine ⟨13044455446839519130813657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17392607262452692174418209 13044455446839519130813657)
              ·
                refine ⟨9783341585129639348110243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044455446839519130813657 9783341585129639348110243)
                ·
                  refine ⟨14675012377694459022165365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783341585129639348110243 14675012377694459022165365)
                  ·
                    refine ⟨1375782410408855533328003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14675012377694459022165365 1375782410408855533328003)
                    ·
                      rfl

theorem cell23_8037980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_8037980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037980 prefixEnd_8037980 := by exact prefixLift 8037980
  have htrace : WordTrace (prefixWord ++ tailWord_8037980) baseStart_8037980 baseEnd_8037980 := by
    simpa [prefixWord, tailWord_8037980, baseEnd_8037980] using wordTrace_append hprefix tailTrace_8037980
  have hstable : (prefixWord ++ tailWord_8037980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037980).length < 2 ^ (prefixWord ++ tailWord_8037980).sum := by decide
  have hdescent : baseEnd_8037980 < baseStart_8037980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037994 : List Nat := [3, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3]
def baseStart_8037994 : Nat := 118140960795 + 8037994 * 2 ^ 59
def prefixEnd_8037994 : Nat := 4983230072969 + 3 ^ 40 * 8037994 * 2
def baseEnd_8037994 : Nat := 4127354419955729545208945

theorem tailTrace_8037994 : CollatzResearch.WordTrace tailWord_8037994 prefixEnd_8037994 4127354419955729545208945 := by
  unfold tailWord_8037994
  simp only [CollatzResearch.WordTrace]
  refine ⟨73292431510431998231926259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195446484027818661951803357 73292431510431998231926259)
  ·
    refine ⟨109938647265647997347889389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73292431510431998231926259 109938647265647997347889389)
    ·
      refine ⟨41226992724617999005458521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109938647265647997347889389 41226992724617999005458521)
      ·
        refine ⟨30920244543463499254093891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41226992724617999005458521 30920244543463499254093891)
        ·
          refine ⟨46380366815195248881140837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30920244543463499254093891 46380366815195248881140837)
          ·
            refine ⟨8696318777849109165213907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46380366815195248881140837 8696318777849109165213907)
            ·
              refine ⟨13044478166773663747820861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696318777849109165213907 13044478166773663747820861)
              ·
                refine ⟨4891679312540123905432823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13044478166773663747820861 4891679312540123905432823)
                ·
                  refine ⟨7337518968810185858149235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891679312540123905432823 7337518968810185858149235)
                  ·
                    refine ⟨11006278453215278787223853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337518968810185858149235 11006278453215278787223853)
                    ·
                      refine ⟨4127354419955729545208945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006278453215278787223853 4127354419955729545208945)
                      ·
                        rfl

theorem cell23_8037994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_8037994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037994 prefixEnd_8037994 := by exact prefixLift 8037994
  have htrace : WordTrace (prefixWord ++ tailWord_8037994) baseStart_8037994 baseEnd_8037994 := by
    simpa [prefixWord, tailWord_8037994, baseEnd_8037994] using wordTrace_append hprefix tailTrace_8037994
  have hstable : (prefixWord ++ tailWord_8037994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037994).length < 2 ^ (prefixWord ++ tailWord_8037994).sum := by decide
  have hdescent : baseEnd_8037994 < baseStart_8037994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8037996 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_8037996 : Nat := 118140960795 + 8037996 * 2 ^ 59
def prefixEnd_8037996 : Nat := 4983230072969 + 3 ^ 40 * 8037996 * 2
def baseEnd_8037996 : Nat := 4127355446917038537383935

theorem tailTrace_8037996 : CollatzResearch.WordTrace tailWord_8037996 prefixEnd_8037996 4127355446917038537383935 := by
  unfold tailWord_8037996
  simp only [CollatzResearch.WordTrace]
  refine ⟨146584899493860373634638921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195446532658480498179518561 146584899493860373634638921)
  ·
    refine ⟨109938674620395280225979191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146584899493860373634638921 109938674620395280225979191)
    ·
      refine ⟨164908011930592920338968787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109938674620395280225979191 164908011930592920338968787)
      ·
        refine ⟨247362017895889380508453181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164908011930592920338968787 247362017895889380508453181)
        ·
          refine ⟨92760756710958517690669943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247362017895889380508453181 92760756710958517690669943)
          ·
            refine ⟨139141135066437776536004915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92760756710958517690669943 139141135066437776536004915)
            ·
              refine ⟨208711702599656664804007373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139141135066437776536004915 208711702599656664804007373)
              ·
                refine ⟨78266888474871249301502765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208711702599656664804007373 78266888474871249301502765)
                ·
                  refine ⟨29350083178076718488063537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78266888474871249301502765 29350083178076718488063537)
                  ·
                    refine ⟨22012562383557538866047653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29350083178076718488063537 22012562383557538866047653)
                    ·
                      refine ⟨4127355446917038537383935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22012562383557538866047653 4127355446917038537383935)
                      ·
                        rfl

theorem cell23_8037996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_8037996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8037996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8037996 prefixEnd_8037996 := by exact prefixLift 8037996
  have htrace : WordTrace (prefixWord ++ tailWord_8037996) baseStart_8037996 baseEnd_8037996 := by
    simpa [prefixWord, tailWord_8037996, baseEnd_8037996] using wordTrace_append hprefix tailTrace_8037996
  have hstable : (prefixWord ++ tailWord_8037996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8037996).length < 2 ^ (prefixWord ++ tailWord_8037996).sum := by decide
  have hdescent : baseEnd_8037996 < baseStart_8037996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8037996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038017 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 3, 2, 2]
def baseStart_8038017 : Nat := 118140960795 + 8038017 * 2 ^ 59
def prefixEnd_8038017 : Nat := 4983230072969 + 3 ^ 40 * 8038017 * 2
def baseEnd_8038017 : Nat := 4127366230010782955221339

theorem tailTrace_8038017 : CollatzResearch.WordTrace tailWord_8038017 prefixEnd_8038017 4127366230010782955221339 := by
  unfold tailWord_8038017
  simp only [CollatzResearch.WordTrace]
  refine ⟨293170564920644667855792305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195447043280429778570528203 293170564920644667855792305)
  ·
    refine ⟨219877923690483500891844229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293170564920644667855792305 219877923690483500891844229)
    ·
      refine ⟨41227110691965656417220793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219877923690483500891844229 41227110691965656417220793)
      ·
        refine ⟨30920333018974242312915595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41227110691965656417220793 30920333018974242312915595)
        ·
          refine ⟨46380499528461363469373393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30920333018974242312915595 46380499528461363469373393)
          ·
            refine ⟨34785374646346022602030045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46380499528461363469373393 34785374646346022602030045)
            ·
              refine ⟨13044515492379758475761267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34785374646346022602030045 13044515492379758475761267)
              ·
                refine ⟨19566773238569637713641901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13044515492379758475761267 19566773238569637713641901)
                ·
                  refine ⟨7337539964463614142615713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19566773238569637713641901 7337539964463614142615713)
                  ·
                    refine ⟨5503154973347710606961785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337539964463614142615713 5503154973347710606961785)
                    ·
                      refine ⟨4127366230010782955221339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503154973347710606961785 4127366230010782955221339)
                      ·
                        rfl

theorem cell23_8038017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_8038017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038017 prefixEnd_8038017 := by exact prefixLift 8038017
  have htrace : WordTrace (prefixWord ++ tailWord_8038017) baseStart_8038017 baseEnd_8038017 := by
    simpa [prefixWord, tailWord_8038017, baseEnd_8038017] using wordTrace_append hprefix tailTrace_8038017
  have hstable : (prefixWord ++ tailWord_8038017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038017).length < 2 ^ (prefixWord ++ tailWord_8038017).sum := by decide
  have hdescent : baseEnd_8038017 < baseStart_8038017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038033 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_8038033 : Nat := 118140960795 + 8038033 * 2 ^ 59
def prefixEnd_8038033 : Nat := 4983230072969 + 3 ^ 40 * 8038033 * 2
def baseEnd_8038033 : Nat := 4127374445701254892621265

theorem tailTrace_8038033 : CollatzResearch.WordTrace tailWord_8038033 prefixEnd_8038033 4127374445701254892621265 := by
  unfold tailWord_8038033
  simp only [CollatzResearch.WordTrace]
  refine ⟨293171148488586702588374753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195447432325724468392249835 293171148488586702588374753)
  ·
    refine ⟨219878361366440026941281065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293171148488586702588374753 219878361366440026941281065)
    ·
      refine ⟨164908771024830020205960799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219878361366440026941281065 164908771024830020205960799)
      ·
        refine ⟨247363156537245030308941199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164908771024830020205960799 247363156537245030308941199)
        ·
          refine ⟨371044734805867545463411799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247363156537245030308941199 371044734805867545463411799)
          ·
            refine ⟨556567102208801318195117699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371044734805867545463411799 556567102208801318195117699)
            ·
              refine ⟨834850653313201977292676549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556567102208801318195117699 834850653313201977292676549)
              ·
                refine ⟨156534497496225370742376853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 834850653313201977292676549 156534497496225370742376853)
                ·
                  refine ⟨7337554570135564253548915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156534497496225370742376853 7337554570135564253548915)
                  ·
                    refine ⟨11006331855203346380323373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337554570135564253548915 11006331855203346380323373)
                    ·
                      refine ⟨4127374445701254892621265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006331855203346380323373 4127374445701254892621265)
                      ·
                        rfl

theorem cell23_8038033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_8038033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038033 prefixEnd_8038033 := by exact prefixLift 8038033
  have htrace : WordTrace (prefixWord ++ tailWord_8038033) baseStart_8038033 baseEnd_8038033 := by
    simpa [prefixWord, tailWord_8038033, baseEnd_8038033] using wordTrace_append hprefix tailTrace_8038033
  have hstable : (prefixWord ++ tailWord_8038033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038033).length < 2 ^ (prefixWord ++ tailWord_8038033).sum := by decide
  have hdescent : baseEnd_8038033 < baseStart_8038033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038034 : List Nat := [3, 2, 3, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_8038034 : Nat := 118140960795 + 8038034 * 2 ^ 59
def prefixEnd_8038034 : Nat := 4983230072969 + 3 ^ 40 * 8038034 * 2
def baseEnd_8038034 : Nat := 4127374959181909388708761

theorem tailTrace_8038034 : CollatzResearch.WordTrace tailWord_8038034 prefixEnd_8038034 4127374959181909388708761 := by
  unfold tailWord_8038034
  simp only [CollatzResearch.WordTrace]
  refine ⟨73292796240395769939790289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195447456641055386506107437 73292796240395769939790289)
  ·
    refine ⟨54969597180296827454842717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73292796240395769939790289 54969597180296827454842717)
    ·
      refine ⟨20613598942611310295566019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54969597180296827454842717 20613598942611310295566019)
      ·
        refine ⟨30920398413916965443349029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20613598942611310295566019 30920398413916965443349029)
        ·
          refine ⟨5797574702609431020627943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30920398413916965443349029 5797574702609431020627943)
          ·
            refine ⟨8696362053914146530941915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797574702609431020627943 8696362053914146530941915)
            ·
              refine ⟨13044543080871219796412873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696362053914146530941915 13044543080871219796412873)
              ·
                refine ⟨9783407310653414847309655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044543080871219796412873 9783407310653414847309655)
                ·
                  refine ⟨14675110965980122270964483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783407310653414847309655 14675110965980122270964483)
                  ·
                    refine ⟨22012666448970183406446725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14675110965980122270964483 22012666448970183406446725)
                    ·
                      refine ⟨4127374959181909388708761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22012666448970183406446725 4127374959181909388708761)
                      ·
                        rfl

theorem cell23_8038034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_8038034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038034 prefixEnd_8038034 := by exact prefixLift 8038034
  have htrace : WordTrace (prefixWord ++ tailWord_8038034) baseStart_8038034 baseEnd_8038034 := by
    simpa [prefixWord, tailWord_8038034, baseEnd_8038034] using wordTrace_append hprefix tailTrace_8038034
  have hstable : (prefixWord ++ tailWord_8038034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038034).length < 2 ^ (prefixWord ++ tailWord_8038034).sum := by decide
  have hdescent : baseEnd_8038034 < baseStart_8038034 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038070 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_8038070 : Nat := 118140960795 + 8038070 * 2 ^ 59
def prefixEnd_8038070 : Nat := 4983230072969 + 3 ^ 40 * 8038070 * 2
def baseEnd_8038070 : Nat := 1375797814828490415952865

theorem tailTrace_8038070 : CollatzResearch.WordTrace tailWord_8038070 prefixEnd_8038070 1375797814828490415952865 := by
  unfold tailWord_8038070
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323281124340791119216979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195448331992968438604981109 18323281124340791119216979)
  ·
    refine ⟨27484921686511186678825469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323281124340791119216979 27484921686511186678825469)
    ·
      refine ⟨10306845632441695004559551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27484921686511186678825469 10306845632441695004559551)
      ·
        refine ⟨15460268448662542506839327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306845632441695004559551 15460268448662542506839327)
        ·
          refine ⟨23190402672993813760258991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460268448662542506839327 23190402672993813760258991)
          ·
            refine ⟨34785604009490720640388487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23190402672993813760258991 34785604009490720640388487)
            ·
              refine ⟨52178406014236080960582731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34785604009490720640388487 52178406014236080960582731)
              ·
                refine ⟨78267609021354121440874097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52178406014236080960582731 78267609021354121440874097)
                ·
                  refine ⟨58700706766015591080655573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78267609021354121440874097 58700706766015591080655573)
                  ·
                    refine ⟨1375797814828490415952865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58700706766015591080655573 1375797814828490415952865)
                    ·
                      rfl

theorem cell23_8038070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_8038070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038070 prefixEnd_8038070 := by exact prefixLift 8038070
  have htrace : WordTrace (prefixWord ++ tailWord_8038070) baseStart_8038070 baseEnd_8038070 := by
    simpa [prefixWord, tailWord_8038070, baseEnd_8038070] using wordTrace_append hprefix tailTrace_8038070
  have hstable : (prefixWord ++ tailWord_8038070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038070).length < 2 ^ (prefixWord ++ tailWord_8038070).sum := by decide
  have hdescent : baseEnd_8038070 < baseStart_8038070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038123 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3]
def baseStart_8038123 : Nat := 118140960795 + 8038123 * 2 ^ 59
def prefixEnd_8038123 : Nat := 4983230072969 + 3 ^ 40 * 8038123 * 2
def baseEnd_8038123 : Nat := 4127420658960159540495851

theorem tailTrace_8038123 : CollatzResearch.WordTrace tailWord_8038123 prefixEnd_8038123 4127420658960159540495851 := by
  unfold tailWord_8038123
  simp only [CollatzResearch.WordTrace]
  refine ⟨293174431058260647959151023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195449620705507098639434015 293174431058260647959151023)
  ·
    refine ⟨439761646587390971938726535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293174431058260647959151023 439761646587390971938726535)
    ·
      refine ⟨659642469881086457908089803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439761646587390971938726535 659642469881086457908089803)
      ·
        refine ⟨989463704821629686862134705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659642469881086457908089803 989463704821629686862134705)
        ·
          refine ⟨742097778616222265146601029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989463704821629686862134705 742097778616222265146601029)
          ·
            refine ⟨139143333490541674714987693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 742097778616222265146601029 139143333490541674714987693)
            ·
              refine ⟨52178750058953128018120385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139143333490541674714987693 52178750058953128018120385)
              ·
                refine ⟨39134062544214846013590289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52178750058953128018120385 39134062544214846013590289)
                ·
                  refine ⟨29350546908161134510192717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39134062544214846013590289 29350546908161134510192717)
                  ·
                    refine ⟨11006455090560425441322269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29350546908161134510192717 11006455090560425441322269)
                    ·
                      refine ⟨4127420658960159540495851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006455090560425441322269 4127420658960159540495851)
                      ·
                        rfl

theorem cell23_8038123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 2, 3, 3].length) (baseStart_8038123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038123 prefixEnd_8038123 := by exact prefixLift 8038123
  have htrace : WordTrace (prefixWord ++ tailWord_8038123) baseStart_8038123 baseEnd_8038123 := by
    simpa [prefixWord, tailWord_8038123, baseEnd_8038123] using wordTrace_append hprefix tailTrace_8038123
  have hstable : (prefixWord ++ tailWord_8038123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038123).length < 2 ^ (prefixWord ++ tailWord_8038123).sum := by decide
  have hdescent : baseEnd_8038123 < baseStart_8038123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038130 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_8038130 : Nat := 118140960795 + 8038130 * 2 ^ 59
def prefixEnd_8038130 : Nat := 4983230072969 + 3 ^ 40 * 8038130 * 2
def baseEnd_8038130 : Nat := 458602694813860112567591

theorem tailTrace_8038130 : CollatzResearch.WordTrace tailWord_8038130 prefixEnd_8038130 458602694813860112567591 := by
  unfold tailWord_8038130
  simp only [CollatzResearch.WordTrace]
  refine ⟨73293671592308822038663961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195449790912823525436437229 73293671592308822038663961)
  ·
    refine ⟨54970253694231616528997971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73293671592308822038663961 54970253694231616528997971)
    ·
      refine ⟨82455380541347424793496957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54970253694231616528997971 82455380541347424793496957)
      ·
        refine ⟨30920767703005284297561359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82455380541347424793496957 30920767703005284297561359)
        ·
          refine ⟨46381151554507926446342039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30920767703005284297561359 46381151554507926446342039)
          ·
            refine ⟨69571727331761889669513059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46381151554507926446342039 69571727331761889669513059)
            ·
              refine ⟨104357590997642834504269589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69571727331761889669513059 104357590997642834504269589)
              ·
                refine ⟨4891762078014507867387637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104357590997642834504269589 4891762078014507867387637)
                ·
                  refine ⟨458602694813860112567591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891762078014507867387637 458602694813860112567591)
                  ·
                    rfl

theorem cell23_8038130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_8038130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038130 prefixEnd_8038130 := by exact prefixLift 8038130
  have htrace : WordTrace (prefixWord ++ tailWord_8038130) baseStart_8038130 baseEnd_8038130 := by
    simpa [prefixWord, tailWord_8038130, baseEnd_8038130] using wordTrace_append hprefix tailTrace_8038130
  have hstable : (prefixWord ++ tailWord_8038130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038130).length < 2 ^ (prefixWord ++ tailWord_8038130).sum := by decide
  have hdescent : baseEnd_8038130 < baseStart_8038130 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038180 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_8038180 : Nat := 118140960795 + 8038180 * 2 ^ 59
def prefixEnd_8038180 : Nat := 4983230072969 + 3 ^ 40 * 8038180 * 2
def baseEnd_8038180 : Nat := 4127449927357465817483089

theorem tailTrace_8038180 : CollatzResearch.WordTrace tailWord_8038180 prefixEnd_8038180 4127449927357465817483089 := by
  unfold tailWord_8038180
  simp only [CollatzResearch.WordTrace]
  refine ⟨146588255009527073346987997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195451006679369431129317329 146588255009527073346987997)
  ·
    refine ⟨54970595628572652505120499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146588255009527073346987997 54970595628572652505120499)
    ·
      refine ⟨82455893442858978757680749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54970595628572652505120499 82455893442858978757680749)
      ·
        refine ⟨30920960041072117034130281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82455893442858978757680749 30920960041072117034130281)
        ·
          refine ⟨23190720030804087775597711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30920960041072117034130281 23190720030804087775597711)
          ·
            refine ⟨34786080046206131663396567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23190720030804087775597711 34786080046206131663396567)
            ·
              refine ⟨52179120069309197495094851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34786080046206131663396567 52179120069309197495094851)
              ·
                refine ⟨78268680103963796242642277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52179120069309197495094851 78268680103963796242642277)
                ·
                  refine ⟨14675377519493211795495427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78268680103963796242642277 14675377519493211795495427)
                  ·
                    refine ⟨22013066279239817693243141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14675377519493211795495427 22013066279239817693243141)
                    ·
                      refine ⟨4127449927357465817483089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22013066279239817693243141 4127449927357465817483089)
                      ·
                        rfl

theorem cell23_8038180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_8038180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038180 prefixEnd_8038180 := by exact prefixLift 8038180
  have htrace : WordTrace (prefixWord ++ tailWord_8038180) baseStart_8038180 baseEnd_8038180 := by
    simpa [prefixWord, tailWord_8038180, baseEnd_8038180] using wordTrace_append hprefix tailTrace_8038180
  have hstable : (prefixWord ++ tailWord_8038180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038180).length < 2 ^ (prefixWord ++ tailWord_8038180).sum := by decide
  have hdescent : baseEnd_8038180 < baseStart_8038180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038214 : List Nat := [6, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_8038214 : Nat := 118140960795 + 8038214 * 2 ^ 59
def prefixEnd_8038214 : Nat := 4983230072969 + 3 ^ 40 * 8038214 * 2
def baseEnd_8038214 : Nat := 4127467385699718684457933

theorem tailTrace_8038214 : CollatzResearch.WordTrace tailWord_8038214 prefixEnd_8038214 4127467385699718684457933 := by
  unfold tailWord_8038214
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161804690654092828147303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195451833400620647000475797 9161804690654092828147303)
  ·
    refine ⟨13742707035981139242220955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9161804690654092828147303 13742707035981139242220955)
    ·
      refine ⟨20614060553971708863331433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13742707035981139242220955 20614060553971708863331433)
      ·
        refine ⟨15460545415478781647498575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20614060553971708863331433 15460545415478781647498575)
        ·
          refine ⟨23190818123218172471247863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460545415478781647498575 23190818123218172471247863)
          ·
            refine ⟨34786227184827258706871795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23190818123218172471247863 34786227184827258706871795)
            ·
              refine ⟨52179340777240888060307693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34786227184827258706871795 52179340777240888060307693)
              ·
                refine ⟨19567252791465333022615385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52179340777240888060307693 19567252791465333022615385)
                ·
                  refine ⟨14675439593598999766961539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19567252791465333022615385 14675439593598999766961539)
                  ·
                    refine ⟨22013159390398499650442309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14675439593598999766961539 22013159390398499650442309)
                    ·
                      refine ⟨4127467385699718684457933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22013159390398499650442309 4127467385699718684457933)
                      ·
                        rfl

theorem cell23_8038214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_8038214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038214 prefixEnd_8038214 := by exact prefixLift 8038214
  have htrace : WordTrace (prefixWord ++ tailWord_8038214) baseStart_8038214 baseEnd_8038214 := by
    simpa [prefixWord, tailWord_8038214, baseEnd_8038214] using wordTrace_append hprefix tailTrace_8038214
  have hstable : (prefixWord ++ tailWord_8038214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038214).length < 2 ^ (prefixWord ++ tailWord_8038214).sum := by decide
  have hdescent : baseEnd_8038214 < baseStart_8038214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038247 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_8038247 : Nat := 118140960795 + 8038247 * 2 ^ 59
def prefixEnd_8038247 : Nat := 4983230072969 + 3 ^ 40 * 8038247 * 2
def baseEnd_8038247 : Nat := 4127484330561317055345281

theorem tailTrace_8038247 : CollatzResearch.WordTrace tailWord_8038247 prefixEnd_8038247 4127484330561317055345281 := by
  unfold tailWord_8038247
  simp only [CollatzResearch.WordTrace]
  refine ⟨293178953709811417136664995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195452635806540944757776663 293178953709811417136664995)
  ·
    refine ⟨439768430564717125704997493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293178953709811417136664995 439768430564717125704997493)
    ·
      refine ⟨41228290365442230534843515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 439768430564717125704997493 41228290365442230534843515)
      ·
        refine ⟨61842435548163345802265273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41228290365442230534843515 61842435548163345802265273)
        ·
          refine ⟨46381826661122509351698955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61842435548163345802265273 46381826661122509351698955)
          ·
            refine ⟨69572739991683764027548433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46381826661122509351698955 69572739991683764027548433)
            ·
              refine ⟨52179554993762823020661325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69572739991683764027548433 52179554993762823020661325)
              ·
                refine ⟨19567333122661058632747997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52179554993762823020661325 19567333122661058632747997)
                ·
                  refine ⟨7337749920997896987280499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19567333122661058632747997 7337749920997896987280499)
                  ·
                    refine ⟨11006624881496845480920749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337749920997896987280499 11006624881496845480920749)
                    ·
                      refine ⟨4127484330561317055345281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006624881496845480920749 4127484330561317055345281)
                      ·
                        rfl

theorem cell23_8038247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_8038247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038247 prefixEnd_8038247 := by exact prefixLift 8038247
  have htrace : WordTrace (prefixWord ++ tailWord_8038247) baseStart_8038247 baseEnd_8038247 := by
    simpa [prefixWord, tailWord_8038247, baseEnd_8038247] using wordTrace_append hprefix tailTrace_8038247
  have hstable : (prefixWord ++ tailWord_8038247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038247).length < 2 ^ (prefixWord ++ tailWord_8038247).sum := by decide
  have hdescent : baseEnd_8038247 < baseStart_8038247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038283 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6]
def baseStart_8038283 : Nat := 118140960795 + 8038283 * 2 ^ 59
def prefixEnd_8038283 : Nat := 4983230072969 + 3 ^ 40 * 8038283 * 2
def baseEnd_8038283 : Nat := 4127502815864878914495115

theorem tailTrace_8038283 : CollatzResearch.WordTrace tailWord_8038283 prefixEnd_8038283 4127502815864878914495115 := by
  unfold tailWord_8038283
  simp only [CollatzResearch.WordTrace]
  refine ⟨293180266737680995284975503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195453511158453996856650335 293180266737680995284975503)
  ·
    refine ⟨439770400106521492927463255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293180266737680995284975503 439770400106521492927463255)
    ·
      refine ⟨659655600159782239391194883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439770400106521492927463255 659655600159782239391194883)
      ·
        refine ⟨989483400239673359086792325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659655600159782239391194883 989483400239673359086792325)
        ·
          refine ⟨185528137544938754828773561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 989483400239673359086792325 185528137544938754828773561)
          ·
            refine ⟨139146103158704066121580171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185528137544938754828773561 139146103158704066121580171)
            ·
              refine ⟨208719154738056099182370257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139146103158704066121580171 208719154738056099182370257)
              ·
                refine ⟨156539366053542074386777693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208719154738056099182370257 156539366053542074386777693)
                ·
                  refine ⟨58702262270078277895041635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156539366053542074386777693 58702262270078277895041635)
                  ·
                    refine ⟨88053393405117416842562453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58702262270078277895041635 88053393405117416842562453)
                    ·
                      refine ⟨4127502815864878914495115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88053393405117416842562453 4127502815864878914495115)
                      ·
                        rfl

theorem cell23_8038283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 6].length) (baseStart_8038283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038283 prefixEnd_8038283 := by exact prefixLift 8038283
  have htrace : WordTrace (prefixWord ++ tailWord_8038283) baseStart_8038283 baseEnd_8038283 := by
    simpa [prefixWord, tailWord_8038283, baseEnd_8038283] using wordTrace_append hprefix tailTrace_8038283
  have hstable : (prefixWord ++ tailWord_8038283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038283).length < 2 ^ (prefixWord ++ tailWord_8038283).sum := by decide
  have hdescent : baseEnd_8038283 < baseStart_8038283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038293 : List Nat := [1, 3, 2, 1, 1, 3, 12]
def baseStart_8038293 : Nat := 118140960795 + 8038293 * 2 ^ 59
def prefixEnd_8038293 : Nat := 4983230072969 + 3 ^ 40 * 8038293 * 2
def baseEnd_8038293 : Nat := 50956888279894121918149

theorem tailTrace_8038293 : CollatzResearch.WordTrace tailWord_8038293 prefixEnd_8038293 50956888279894121918149 := by
  unfold tailWord_8038293
  simp only [CollatzResearch.WordTrace]
  refine ⟨293180631467644766992839533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195453754311763177995226355 293180631467644766992839533)
  ·
    refine ⟨109942736800366787622314825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293180631467644766992839533 109942736800366787622314825)
    ·
      refine ⟨82457052600275090716736119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109942736800366787622314825 82457052600275090716736119)
      ·
        refine ⟨123685578900412636075104179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82457052600275090716736119 123685578900412636075104179)
        ·
          refine ⟨185528368350618954112656269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123685578900412636075104179 185528368350618954112656269)
          ·
            refine ⟨69573138131482107792246101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185528368350618954112656269 69573138131482107792246101)
            ·
              refine ⟨50956888279894121918149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69573138131482107792246101 50956888279894121918149)
              ·
                rfl

theorem cell23_8038293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 12].length) (baseStart_8038293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038293 prefixEnd_8038293 := by exact prefixLift 8038293
  have htrace : WordTrace (prefixWord ++ tailWord_8038293) baseStart_8038293 baseEnd_8038293 := by
    simpa [prefixWord, tailWord_8038293, baseEnd_8038293] using wordTrace_append hprefix tailTrace_8038293
  have hstable : (prefixWord ++ tailWord_8038293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038293).length < 2 ^ (prefixWord ++ tailWord_8038293).sum := by decide
  have hdescent : baseEnd_8038293 < baseStart_8038293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038297 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 2, 4]
def baseStart_8038297 : Nat := 118140960795 + 8038297 * 2 ^ 59
def prefixEnd_8038297 : Nat := 4983230072969 + 3 ^ 40 * 8038297 * 2
def baseEnd_8038297 : Nat := 1375836668198013953240017

theorem tailTrace_8038297 : CollatzResearch.WordTrace tailWord_8038297 prefixEnd_8038297 1375836668198013953240017 := by
  unfold tailWord_8038297
  simp only [CollatzResearch.WordTrace]
  refine ⟨293180777359630275675985145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195453851573086850450656763 293180777359630275675985145)
  ·
    refine ⟨219885583019722706756988859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293180777359630275675985145 219885583019722706756988859)
    ·
      refine ⟨329828374529584060135483289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219885583019722706756988859 329828374529584060135483289)
      ·
        refine ⟨247371280897188045101612467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329828374529584060135483289 247371280897188045101612467)
        ·
          refine ⟨371056921345782067652418701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247371280897188045101612467 371056921345782067652418701)
          ·
            refine ⟨139146345504668275369657013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371056921345782067652418701 139146345504668275369657013)
            ·
              refine ⟨13044969891062650815905345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139146345504668275369657013 13044969891062650815905345)
              ·
                refine ⟨9783727418296988111929009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13044969891062650815905345 9783727418296988111929009)
                ·
                  refine ⟨7337795563722741083946757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783727418296988111929009 7337795563722741083946757)
                  ·
                    refine ⟨1375836668198013953240017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337795563722741083946757 1375836668198013953240017)
                    ·
                      rfl

theorem cell23_8038297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 4].length) (baseStart_8038297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038297 prefixEnd_8038297 := by exact prefixLift 8038297
  have htrace : WordTrace (prefixWord ++ tailWord_8038297) baseStart_8038297 baseEnd_8038297 := by
    simpa [prefixWord, tailWord_8038297, baseEnd_8038297] using wordTrace_append hprefix tailTrace_8038297
  have hstable : (prefixWord ++ tailWord_8038297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038297).length < 2 ^ (prefixWord ++ tailWord_8038297).sum := by decide
  have hdescent : baseEnd_8038297 < baseStart_8038297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 6]
def baseStart_8038313 : Nat := 118140960795 + 8038313 * 2 ^ 59
def prefixEnd_8038313 : Nat := 4983230072969 + 3 ^ 40 * 8038313 * 2
def baseEnd_8038313 : Nat := 4127518220284513797119977

theorem tailTrace_8038313 : CollatzResearch.WordTrace tailWord_8038313 prefixEnd_8038313 4127518220284513797119977 := by
  unfold tailWord_8038313
  simp only [CollatzResearch.WordTrace]
  refine ⟨293181360927572310408567593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195454240618381540272378395 293181360927572310408567593)
  ·
    refine ⟨219886020695679232806425695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293181360927572310408567593 219886020695679232806425695)
    ·
      refine ⟨329829031043518849209638543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219886020695679232806425695 329829031043518849209638543)
      ·
        refine ⟨494743546565278273814457815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329829031043518849209638543 494743546565278273814457815)
        ·
          refine ⟨742115319847917410721686723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494743546565278273814457815 742115319847917410721686723)
          ·
            refine ⟨1113172979771876116082530085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742115319847917410721686723 1113172979771876116082530085)
            ·
              refine ⟨208719933707226771765474391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1113172979771876116082530085 208719933707226771765474391)
              ·
                refine ⟨313079900560840157648211587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208719933707226771765474391 313079900560840157648211587)
                ·
                  refine ⟨469619850841260236472317381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313079900560840157648211587 469619850841260236472317381)
                  ·
                    refine ⟨88053722032736294338559509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469619850841260236472317381 88053722032736294338559509)
                    ·
                      refine ⟨4127518220284513797119977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88053722032736294338559509 4127518220284513797119977)
                      ·
                        rfl

theorem cell23_8038313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_8038313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038313 prefixEnd_8038313 := by exact prefixLift 8038313
  have htrace : WordTrace (prefixWord ++ tailWord_8038313) baseStart_8038313 baseEnd_8038313 := by
    simpa [prefixWord, tailWord_8038313, baseEnd_8038313] using wordTrace_append hprefix tailTrace_8038313
  have hstable : (prefixWord ++ tailWord_8038313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038313).length < 2 ^ (prefixWord ++ tailWord_8038313).sum := by decide
  have hdescent : baseEnd_8038313 < baseStart_8038313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038318 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8038318 : Nat := 118140960795 + 8038318 * 2 ^ 59
def prefixEnd_8038318 : Nat := 4983230072969 + 3 ^ 40 * 8038318 * 2
def baseEnd_8038318 : Nat := 1375840262562595425852485

theorem tailTrace_8038318 : CollatzResearch.WordTrace tailWord_8038318 prefixEnd_8038318 1375840262562595425852485 := by
  unfold tailWord_8038318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647692911569274532812451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195454362195036130841666405 36647692911569274532812451)
  ·
    refine ⟨54971539367353911799218677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36647692911569274532812451 54971539367353911799218677)
    ·
      refine ⟨5153581815689429231176751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54971539367353911799218677 5153581815689429231176751)
      ·
        refine ⟨7730372723534143846765127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5153581815689429231176751 7730372723534143846765127)
        ·
          refine ⟨11595559085301215770147691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730372723534143846765127 11595559085301215770147691)
          ·
            refine ⟨17393338627951823655221537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11595559085301215770147691 17393338627951823655221537)
            ·
              refine ⟨13045003970963867741416153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17393338627951823655221537 13045003970963867741416153)
              ·
                refine ⟨9783752978222900806062115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045003970963867741416153 9783752978222900806062115)
                ·
                  refine ⟨14675629467334351209093173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783752978222900806062115 14675629467334351209093173)
                  ·
                    refine ⟨1375840262562595425852485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14675629467334351209093173 1375840262562595425852485)
                    ·
                      rfl

theorem cell23_8038318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8038318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038318 prefixEnd_8038318 := by exact prefixLift 8038318
  have htrace : WordTrace (prefixWord ++ tailWord_8038318) baseStart_8038318 baseEnd_8038318 := by
    simpa [prefixWord, tailWord_8038318, baseEnd_8038318] using wordTrace_append hprefix tailTrace_8038318
  have hstable : (prefixWord ++ tailWord_8038318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038318).length < 2 ^ (prefixWord ++ tailWord_8038318).sum := by decide
  have hdescent : baseEnd_8038318 < baseStart_8038318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038350 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_8038350 : Nat := 118140960795 + 8038350 * 2 ^ 59
def prefixEnd_8038350 : Nat := 4983230072969 + 3 ^ 40 * 8038350 * 2
def baseEnd_8038350 : Nat := 4127537219068730152357307

theorem tailTrace_8038350 : CollatzResearch.WordTrace tailWord_8038350 prefixEnd_8038350 4127537219068730152357307 := by
  unfold tailWord_8038350
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647838803554783215958063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195455140285625510485109669 36647838803554783215958063)
  ·
    refine ⟨54971758205332174823937095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36647838803554783215958063 54971758205332174823937095)
    ·
      refine ⟨82457637307998262235905643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54971758205332174823937095 82457637307998262235905643)
      ·
        refine ⟨123686455961997393353858465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82457637307998262235905643 123686455961997393353858465)
        ·
          refine ⟨92764841971498045015393849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123686455961997393353858465 92764841971498045015393849)
          ·
            refine ⟨69573631478623533761545387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92764841971498045015393849 69573631478623533761545387)
            ·
              refine ⟨104360447217935300642318081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69573631478623533761545387 104360447217935300642318081)
              ·
                refine ⟨78270335413451475481738561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104360447217935300642318081 78270335413451475481738561)
                ·
                  refine ⟨58702751560088606611303921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78270335413451475481738561 58702751560088606611303921)
                  ·
                    refine ⟨44027063670066454958477941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58702751560088606611303921 44027063670066454958477941)
                    ·
                      refine ⟨4127537219068730152357307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44027063670066454958477941 4127537219068730152357307)
                      ·
                        rfl

theorem cell23_8038350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_8038350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038350 prefixEnd_8038350 := by exact prefixLift 8038350
  have htrace : WordTrace (prefixWord ++ tailWord_8038350) baseStart_8038350 baseEnd_8038350 := by
    simpa [prefixWord, tailWord_8038350, baseEnd_8038350] using wordTrace_append hprefix tailTrace_8038350
  have hstable : (prefixWord ++ tailWord_8038350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038350).length < 2 ^ (prefixWord ++ tailWord_8038350).sum := by decide
  have hdescent : baseEnd_8038350 < baseStart_8038350 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038360 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_8038360 : Nat := 118140960795 + 8038360 * 2 ^ 59
def prefixEnd_8038360 : Nat := 4983230072969 + 3 ^ 40 * 8038360 * 2
def baseEnd_8038360 : Nat := 4127542353875275113232261

theorem tailTrace_8038360 : CollatzResearch.WordTrace tailWord_8038360 prefixEnd_8038360 4127542353875275113232261 := by
  unfold tailWord_8038360
  simp only [CollatzResearch.WordTrace]
  refine ⟨146591537579201018717764267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195455383438934691623685689 146591537579201018717764267)
  ·
    refine ⟨219887306368801528076646401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146591537579201018717764267 219887306368801528076646401)
    ·
      refine ⟨164915479776601146057484801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219887306368801528076646401 164915479776601146057484801)
      ·
        refine ⟨123686609832450859543113601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164915479776601146057484801 123686609832450859543113601)
        ·
          refine ⟨92764957374338144657335201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123686609832450859543113601 92764957374338144657335201)
          ·
            refine ⟨69573718030753608493001401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92764957374338144657335201 69573718030753608493001401)
            ·
              refine ⟨52180288523065206369751051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69573718030753608493001401 52180288523065206369751051)
              ·
                refine ⟨78270432784597809554626577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52180288523065206369751051 78270432784597809554626577)
                ·
                  refine ⟨58702824588448357165969933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78270432784597809554626577 58702824588448357165969933)
                  ·
                    refine ⟨22013559220668133937238725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58702824588448357165969933 22013559220668133937238725)
                    ·
                      refine ⟨4127542353875275113232261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22013559220668133937238725 4127542353875275113232261)
                      ·
                        rfl

theorem cell23_8038360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_8038360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038360 prefixEnd_8038360 := by exact prefixLift 8038360
  have htrace : WordTrace (prefixWord ++ tailWord_8038360) baseStart_8038360 baseEnd_8038360 := by
    simpa [prefixWord, tailWord_8038360, baseEnd_8038360] using wordTrace_append hprefix tailTrace_8038360
  have hstable : (prefixWord ++ tailWord_8038360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038360).length < 2 ^ (prefixWord ++ tailWord_8038360).sum := by decide
  have hdescent : baseEnd_8038360 < baseStart_8038360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038371 : List Nat := [1, 1, 1, 6, 1, 2, 4, 1, 2, 1, 3]
def baseStart_8038371 : Nat := 118140960795 + 8038371 * 2 ^ 59
def prefixEnd_8038371 : Nat := 4983230072969 + 3 ^ 40 * 8038371 * 2
def baseEnd_8038371 : Nat := 4127548002162474570194711

theorem tailTrace_8038371 : CollatzResearch.WordTrace tailWord_8038371 prefixEnd_8038371 4127548002162474570194711 := by
  unfold tailWord_8038371
  simp only [CollatzResearch.WordTrace]
  refine ⟨293183476361362186314178967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195455650907574790876119311 293183476361362186314178967)
  ·
    refine ⟨439775214542043279471268451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293183476361362186314178967 439775214542043279471268451)
    ·
      refine ⟨659662821813064919206902677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439775214542043279471268451 659662821813064919206902677)
      ·
        refine ⟨30921694772487418087823563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 659662821813064919206902677 30921694772487418087823563)
        ·
          refine ⟨46382542158731127131735345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30921694772487418087823563 46382542158731127131735345)
          ·
            refine ⟨34786906619048345348801509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46382542158731127131735345 34786906619048345348801509)
            ·
              refine ⟨6522544991071564752900283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34786906619048345348801509 6522544991071564752900283)
              ·
                refine ⟨9783817486607347129350425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522544991071564752900283 9783817486607347129350425)
                ·
                  refine ⟨7337863114955510347012819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783817486607347129350425 7337863114955510347012819)
                  ·
                    refine ⟨11006794672433265520519229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7337863114955510347012819 11006794672433265520519229)
                    ·
                      refine ⟨4127548002162474570194711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006794672433265520519229 4127548002162474570194711)
                      ·
                        rfl

theorem cell23_8038371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_8038371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038371 prefixEnd_8038371 := by exact prefixLift 8038371
  have htrace : WordTrace (prefixWord ++ tailWord_8038371) baseStart_8038371 baseEnd_8038371 := by
    simpa [prefixWord, tailWord_8038371, baseEnd_8038371] using wordTrace_append hprefix tailTrace_8038371
  have hstable : (prefixWord ++ tailWord_8038371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038371).length < 2 ^ (prefixWord ++ tailWord_8038371).sum := by decide
  have hdescent : baseEnd_8038371 < baseStart_8038371 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038411 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 2, 2, 2]
def baseStart_8038411 : Nat := 118140960795 + 8038411 * 2 ^ 59
def prefixEnd_8038411 : Nat := 4983230072969 + 3 ^ 40 * 8038411 * 2
def baseEnd_8038411 : Nat := 4127568541388654413694527

theorem tailTrace_8038411 : CollatzResearch.WordTrace tailWord_8038411 prefixEnd_8038411 4127568541388654413694527 := by
  unfold tailWord_8038411
  simp only [CollatzResearch.WordTrace]
  refine ⟨293184935281217273145635087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195456623520811515430423391 293184935281217273145635087)
  ·
    refine ⟨439777402921825909718452631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293184935281217273145635087 439777402921825909718452631)
    ·
      refine ⟨659666104382738864577678947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439777402921825909718452631 659666104382738864577678947)
      ·
        refine ⟨989499156574108296866518421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659666104382738864577678947 989499156574108296866518421)
        ·
          refine ⟨46382772964411326415618051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 989499156574108296866518421 46382772964411326415618051)
          ·
            refine ⟨69574159446616989623427077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46382772964411326415618051 69574159446616989623427077)
            ·
              refine ⟨13045154896240685554392577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69574159446616989623427077 13045154896240685554392577)
              ·
                refine ⟨9783866172180514165794433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045154896240685554392577 9783866172180514165794433)
                ·
                  refine ⟨7337899629135385624345825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783866172180514165794433 7337899629135385624345825)
                  ·
                    refine ⟨5503424721851539218259369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337899629135385624345825 5503424721851539218259369)
                    ·
                      refine ⟨4127568541388654413694527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503424721851539218259369 4127568541388654413694527)
                      ·
                        rfl

theorem cell23_8038411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 2, 2].length) (baseStart_8038411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038411 prefixEnd_8038411 := by exact prefixLift 8038411
  have htrace : WordTrace (prefixWord ++ tailWord_8038411) baseStart_8038411 baseEnd_8038411 := by
    simpa [prefixWord, tailWord_8038411, baseEnd_8038411] using wordTrace_append hprefix tailTrace_8038411
  have hstable : (prefixWord ++ tailWord_8038411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038411).length < 2 ^ (prefixWord ++ tailWord_8038411).sum := by decide
  have hdescent : baseEnd_8038411 < baseStart_8038411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038462 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_8038462 : Nat := 118140960795 + 8038462 * 2 ^ 59
def prefixEnd_8038462 : Nat := 4983230072969 + 3 ^ 40 * 8038462 * 2
def baseEnd_8038462 : Nat := 4127594728902033714156793

theorem tailTrace_8038462 : CollatzResearch.WordTrace tailWord_8038462 prefixEnd_8038462 4127594728902033714156793 := by
  unfold tailWord_8038462
  simp only [CollatzResearch.WordTrace]
  refine ⟨36648349425504063606967705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195457863602688339237161093 36648349425504063606967705)
  ·
    refine ⟨27486262069128047705225779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36648349425504063606967705 27486262069128047705225779)
    ·
      refine ⟨41229393103692071557838669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27486262069128047705225779 41229393103692071557838669)
      ·
        refine ⟨15461022413884526834189501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41229393103692071557838669 15461022413884526834189501)
        ·
          refine ⟨5797883405206697562821063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15461022413884526834189501 5797883405206697562821063)
          ·
            refine ⟨8696825107810046344231595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797883405206697562821063 8696825107810046344231595)
            ·
              refine ⟨13045237661715069516347393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696825107810046344231595 13045237661715069516347393)
              ·
                refine ⟨9783928246286302137260545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045237661715069516347393 9783928246286302137260545)
                ·
                  refine ⟨7337946184714726602945409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9783928246286302137260545 7337946184714726602945409)
                  ·
                    refine ⟨5503459638536044952209057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7337946184714726602945409 5503459638536044952209057)
                    ·
                      refine ⟨4127594728902033714156793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503459638536044952209057 4127594728902033714156793)
                      ·
                        rfl

theorem cell23_8038462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_8038462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038462 prefixEnd_8038462 := by exact prefixLift 8038462
  have htrace : WordTrace (prefixWord ++ tailWord_8038462) baseStart_8038462 baseEnd_8038462 := by
    simpa [prefixWord, tailWord_8038462, baseEnd_8038462] using wordTrace_append hprefix tailTrace_8038462
  have hstable : (prefixWord ++ tailWord_8038462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038462).length < 2 ^ (prefixWord ++ tailWord_8038462).sum := by decide
  have hdescent : baseEnd_8038462 < baseStart_8038462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038487 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3]
def baseStart_8038487 : Nat := 118140960795 + 8038487 * 2 ^ 59
def prefixEnd_8038487 : Nat := 4983230072969 + 3 ^ 40 * 8038487 * 2
def baseEnd_8038487 : Nat := 4127607565918396116344177

theorem tailTrace_8038487 : CollatzResearch.WordTrace tailWord_8038487 prefixEnd_8038487 4127607565918396116344177 := by
  unfold tailWord_8038487
  simp only [CollatzResearch.WordTrace]
  refine ⟨293187707228941938125401715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195458471485961292083601143 293187707228941938125401715)
  ·
    refine ⟨439781560843412907188102573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293187707228941938125401715 439781560843412907188102573)
    ·
      refine ⟨164918085316279840195538465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439781560843412907188102573 164918085316279840195538465)
      ·
        refine ⟨123688563987209880146653849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164918085316279840195538465 123688563987209880146653849)
        ·
          refine ⟨92766422990407410109990387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123688563987209880146653849 92766422990407410109990387)
          ·
            refine ⟨139149634485611115164985581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92766422990407410109990387 139149634485611115164985581)
            ·
              refine ⟨52181112932104168186869593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139149634485611115164985581 52181112932104168186869593)
              ·
                refine ⟨39135834699078126140152195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52181112932104168186869593 39135834699078126140152195)
                ·
                  refine ⟨58703752048617189210228293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39135834699078126140152195 58703752048617189210228293)
                  ·
                    refine ⟨11006953509115722976917805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58703752048617189210228293 11006953509115722976917805)
                    ·
                      refine ⟨4127607565918396116344177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11006953509115722976917805 4127607565918396116344177)
                      ·
                        rfl

theorem cell23_8038487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_8038487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038487 prefixEnd_8038487 := by exact prefixLift 8038487
  have htrace : WordTrace (prefixWord ++ tailWord_8038487) baseStart_8038487 baseEnd_8038487 := by
    simpa [prefixWord, tailWord_8038487, baseEnd_8038487] using wordTrace_append hprefix tailTrace_8038487
  have hstable : (prefixWord ++ tailWord_8038487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038487).length < 2 ^ (prefixWord ++ tailWord_8038487).sum := by decide
  have hdescent : baseEnd_8038487 < baseStart_8038487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038511 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 1, 4]
def baseStart_8038511 : Nat := 118140960795 + 8038511 * 2 ^ 59
def prefixEnd_8038511 : Nat := 4983230072969 + 3 ^ 40 * 8038511 * 2
def baseEnd_8038511 : Nat := 1375873296484701340814689

theorem tailTrace_8038511 : CollatzResearch.WordTrace tailWord_8038511 prefixEnd_8038511 1375873296484701340814689 := by
  unfold tailWord_8038511
  simp only [CollatzResearch.WordTrace]
  refine ⟨293188582580854990224275387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195459055053903326816183591 293188582580854990224275387)
  ·
    refine ⟨439782873871282485336413081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293188582580854990224275387 439782873871282485336413081)
    ·
      refine ⟨329837155403461864002309811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439782873871282485336413081 329837155403461864002309811)
      ·
        refine ⟨494755733105192796003464717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329837155403461864002309811 494755733105192796003464717)
        ·
          refine ⟨185533399914447298501299269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494755733105192796003464717 185533399914447298501299269)
          ·
            refine ⟨34787512483958868468993613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185533399914447298501299269 34787512483958868468993613)
            ·
              refine ⟨13045317181484575675872605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34787512483958868468993613 13045317181484575675872605)
              ·
                refine ⟨4891993943056715878452227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13045317181484575675872605 4891993943056715878452227)
                ·
                  refine ⟨7337990914585073817678341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4891993943056715878452227 7337990914585073817678341)
                  ·
                    refine ⟨1375873296484701340814689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7337990914585073817678341 1375873296484701340814689)
                    ·
                      rfl

theorem cell23_8038511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 4].length) (baseStart_8038511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038511 prefixEnd_8038511 := by exact prefixLift 8038511
  have htrace : WordTrace (prefixWord ++ tailWord_8038511) baseStart_8038511 baseEnd_8038511 := by
    simpa [prefixWord, tailWord_8038511, baseEnd_8038511] using wordTrace_append hprefix tailTrace_8038511
  have hstable : (prefixWord ++ tailWord_8038511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038511).length < 2 ^ (prefixWord ++ tailWord_8038511).sum := by decide
  have hdescent : baseEnd_8038511 < baseStart_8038511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038537 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 3, 5]
def baseStart_8038537 : Nat := 118140960795 + 8038537 * 2 ^ 59
def prefixEnd_8038537 : Nat := 4983230072969 + 3 ^ 40 * 8038537 * 2
def baseEnd_8038537 : Nat := 1375877746650373640239649

theorem tailTrace_8038537 : CollatzResearch.WordTrace tailWord_8038537 prefixEnd_8038537 1375877746650373640239649 := by
  unfold tailWord_8038537
  simp only [CollatzResearch.WordTrace]
  refine ⟨293189530878760796664721865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195459687252507197776481243 293189530878760796664721865)
  ·
    refine ⟨219892148159070597498541399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293189530878760796664721865 219892148159070597498541399)
    ·
      refine ⟨329838222238605896247812099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219892148159070597498541399 329838222238605896247812099)
      ·
        refine ⟨494757333357908844371718149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329838222238605896247812099 494757333357908844371718149)
        ·
          refine ⟨92767000004607908319697153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494757333357908844371718149 92767000004607908319697153)
          ·
            refine ⟨69575250003455931239772865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92767000004607908319697153 69575250003455931239772865)
            ·
              refine ⟨52181437502591948429829649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69575250003455931239772865 52181437502591948429829649)
              ·
                refine ⟨39136078126943961322372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52181437502591948429829649 39136078126943961322372237)
                ·
                  refine ⟨14676029297603985495889589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39136078126943961322372237 14676029297603985495889589)
                  ·
                    refine ⟨1375877746650373640239649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14676029297603985495889589 1375877746650373640239649)
                    ·
                      rfl

theorem cell23_8038537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 5].length) (baseStart_8038537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038537 prefixEnd_8038537 := by exact prefixLift 8038537
  have htrace : WordTrace (prefixWord ++ tailWord_8038537) baseStart_8038537 baseEnd_8038537 := by
    simpa [prefixWord, tailWord_8038537, baseEnd_8038537] using wordTrace_append hprefix tailTrace_8038537
  have hstable : (prefixWord ++ tailWord_8038537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038537).length < 2 ^ (prefixWord ++ tailWord_8038537).sum := by decide
  have hdescent : baseEnd_8038537 < baseStart_8038537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038544 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2]
def baseStart_8038544 : Nat := 118140960795 + 8038544 * 2 ^ 59
def prefixEnd_8038544 : Nat := 4983230072969 + 3 ^ 40 * 8038544 * 2
def baseEnd_8038544 : Nat := 4127636834315702393331415

theorem tailTrace_8038544 : CollatzResearch.WordTrace tailWord_8038544 prefixEnd_8038544 4127636834315702393331415 := by
  unfold tailWord_8038544
  simp only [CollatzResearch.WordTrace]
  refine ⟨146594893094867718430113343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195459857459823624573484457 146594893094867718430113343)
  ·
    refine ⟨219892339642301577645170015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146594893094867718430113343 219892339642301577645170015)
    ·
      refine ⟨329838509463452366467755023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219892339642301577645170015 329838509463452366467755023)
      ·
        refine ⟨494757764195178549701632535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329838509463452366467755023 494757764195178549701632535)
        ·
          refine ⟨742136646292767824552448803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494757764195178549701632535 742136646292767824552448803)
          ·
            refine ⟨1113204969439151736828673205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742136646292767824552448803 1113204969439151736828673205)
            ·
              refine ⟨104362965884920475327688113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1113204969439151736828673205 104362965884920475327688113)
              ·
                refine ⟨78272224413690356495766085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104362965884920475327688113 78272224413690356495766085)
                ·
                  refine ⟨14676042077566941842956141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78272224413690356495766085 14676042077566941842956141)
                  ·
                    refine ⟨5503515779087603191108553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676042077566941842956141 5503515779087603191108553)
                    ·
                      refine ⟨4127636834315702393331415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503515779087603191108553 4127636834315702393331415)
                      ·
                        rfl

theorem cell23_8038544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 3, 2].length) (baseStart_8038544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038544 prefixEnd_8038544 := by exact prefixLift 8038544
  have htrace : WordTrace (prefixWord ++ tailWord_8038544) baseStart_8038544 baseEnd_8038544 := by
    simpa [prefixWord, tailWord_8038544, baseEnd_8038544] using wordTrace_append hprefix tailTrace_8038544
  have hstable : (prefixWord ++ tailWord_8038544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038544).length < 2 ^ (prefixWord ++ tailWord_8038544).sum := by decide
  have hdescent : baseEnd_8038544 < baseStart_8038544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038561 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 2, 3, 2]
def baseStart_8038561 : Nat := 118140960795 + 8038561 * 2 ^ 59
def prefixEnd_8038561 : Nat := 4983230072969 + 3 ^ 40 * 8038561 * 2
def baseEnd_8038561 : Nat := 4127645563486828826818837

theorem tailTrace_8038561 : CollatzResearch.WordTrace tailWord_8038561 prefixEnd_8038561 4127645563486828826818837 := by
  unfold tailWord_8038561
  simp only [CollatzResearch.WordTrace]
  refine ⟨293190406230673848763595537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195460270820449232509063691 293190406230673848763595537)
  ·
    refine ⟨219892804673005386572696653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293190406230673848763595537 219892804673005386572696653)
    ·
      refine ⟨82459801752377019964761245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219892804673005386572696653 82459801752377019964761245)
      ·
        refine ⟨30922425657141382486785467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82459801752377019964761245 30922425657141382486785467)
        ·
          refine ⟨46383638485712073730178201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30922425657141382486785467 46383638485712073730178201)
          ·
            refine ⟨34787728864284055297633651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46383638485712073730178201 34787728864284055297633651)
            ·
              refine ⟨52181593296426082946450477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34787728864284055297633651 52181593296426082946450477)
              ·
                refine ⟨19568097486159781104918929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52181593296426082946450477 19568097486159781104918929)
                ·
                  refine ⟨14676073114619835828689197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19568097486159781104918929 14676073114619835828689197)
                  ·
                    refine ⟨5503527417982438435758449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676073114619835828689197 5503527417982438435758449)
                    ·
                      refine ⟨4127645563486828826818837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503527417982438435758449 4127645563486828826818837)
                      ·
                        rfl

theorem cell23_8038561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_8038561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038561 prefixEnd_8038561 := by exact prefixLift 8038561
  have htrace : WordTrace (prefixWord ++ tailWord_8038561) baseStart_8038561 baseEnd_8038561 := by
    simpa [prefixWord, tailWord_8038561, baseEnd_8038561] using wordTrace_append hprefix tailTrace_8038561
  have hstable : (prefixWord ++ tailWord_8038561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038561).length < 2 ^ (prefixWord ++ tailWord_8038561).sum := by decide
  have hdescent : baseEnd_8038561 < baseStart_8038561 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038587 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4]
def baseStart_8038587 : Nat := 118140960795 + 8038587 * 2 ^ 59
def prefixEnd_8038587 : Nat := 4983230072969 + 3 ^ 40 * 8038587 * 2
def baseEnd_8038587 : Nat := 4127658913983845725093717

theorem tailTrace_8038587 : CollatzResearch.WordTrace tailWord_8038587 prefixEnd_8038587 4127658913983845725093717 := by
  unfold tailWord_8038587
  simp only [CollatzResearch.WordTrace]
  refine ⟨293191354528579655204042015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195460903019053103469361343 293191354528579655204042015)
  ·
    refine ⟨439787031792869482806063023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293191354528579655204042015 439787031792869482806063023)
    ·
      refine ⟨659680547689304224209094535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439787031792869482806063023 659680547689304224209094535)
      ·
        refine ⟨989520821533956336313641803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659680547689304224209094535 989520821533956336313641803)
        ·
          refine ⟨1484281232300934504470462705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989520821533956336313641803 1484281232300934504470462705)
          ·
            refine ⟨1113210924225700878352847029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484281232300934504470462705 1113210924225700878352847029)
            ·
              refine ⟨104363524146159457345579409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1113210924225700878352847029 104363524146159457345579409)
              ·
                refine ⟨78272643109619593009184557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104363524146159457345579409 78272643109619593009184557)
                ·
                  refine ⟨29352241166107347378444209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78272643109619593009184557 29352241166107347378444209)
                  ·
                    refine ⟨22014180874580510533833157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29352241166107347378444209 22014180874580510533833157)
                    ·
                      refine ⟨4127658913983845725093717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22014180874580510533833157 4127658913983845725093717)
                      ·
                        rfl

theorem cell23_8038587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 4].length) (baseStart_8038587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038587 prefixEnd_8038587 := by exact prefixLift 8038587
  have htrace : WordTrace (prefixWord ++ tailWord_8038587) baseStart_8038587 baseEnd_8038587 := by
    simpa [prefixWord, tailWord_8038587, baseEnd_8038587] using wordTrace_append hprefix tailTrace_8038587
  have hstable : (prefixWord ++ tailWord_8038587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038587).length < 2 ^ (prefixWord ++ tailWord_8038587).sum := by decide
  have hdescent : baseEnd_8038587 < baseStart_8038587 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038591 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 3, 2, 2]
def baseStart_8038591 : Nat := 118140960795 + 8038591 * 2 ^ 59
def prefixEnd_8038591 : Nat := 4983230072969 + 3 ^ 40 * 8038591 * 2
def baseEnd_8038591 : Nat := 4127660967906463709443699

theorem tailTrace_8038591 : CollatzResearch.WordTrace tailWord_8038591 prefixEnd_8038591 4127660967906463709443699 := by
  unfold tailWord_8038591
  simp only [CollatzResearch.WordTrace]
  refine ⟨293191500420565163887187627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195461000280376775924791751 293191500420565163887187627)
  ·
    refine ⟨439787250630847745830781441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293191500420565163887187627 439787250630847745830781441)
    ·
      refine ⟨329840437973135809373086081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439787250630847745830781441 329840437973135809373086081)
      ·
        refine ⟨247380328479851857029814561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329840437973135809373086081 247380328479851857029814561)
        ·
          refine ⟨185535246359888892772360921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247380328479851857029814561 185535246359888892772360921)
          ·
            refine ⟨139151434769916669579270691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185535246359888892772360921 139151434769916669579270691)
            ·
              refine ⟨208727152154875004368906037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139151434769916669579270691 208727152154875004368906037)
              ·
                refine ⟨19568170514519531659584941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208727152154875004368906037 19568170514519531659584941)
                ·
                  refine ⟨7338063942944824372344353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19568170514519531659584941 7338063942944824372344353)
                  ·
                    refine ⟨5503547957208618279258265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7338063942944824372344353 5503547957208618279258265)
                    ·
                      refine ⟨4127660967906463709443699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503547957208618279258265 4127660967906463709443699)
                      ·
                        rfl

theorem cell23_8038591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 2, 2].length) (baseStart_8038591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038591 prefixEnd_8038591 := by exact prefixLift 8038591
  have htrace : WordTrace (prefixWord ++ tailWord_8038591) baseStart_8038591 baseEnd_8038591 := by
    simpa [prefixWord, tailWord_8038591, baseEnd_8038591] using wordTrace_append hprefix tailTrace_8038591
  have hstable : (prefixWord ++ tailWord_8038591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038591).length < 2 ^ (prefixWord ++ tailWord_8038591).sum := by decide
  have hdescent : baseEnd_8038591 < baseStart_8038591 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038597 : List Nat := [1, 3, 1, 1, 1, 1, 7, 8]
def baseStart_8038597 : Nat := 118140960795 + 8038597 * 2 ^ 59
def prefixEnd_8038597 : Nat := 4983230072969 + 3 ^ 40 * 8038597 * 2
def baseEnd_8038597 : Nat := 152876446251495951332173

theorem tailTrace_8038597 : CollatzResearch.WordTrace tailWord_8038597 prefixEnd_8038597 152876446251495951332173 := by
  unfold tailWord_8038597
  simp only [CollatzResearch.WordTrace]
  refine ⟨293191719258543426911906045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195461146172362284607937363 293191719258543426911906045)
  ·
    refine ⟨109946894721953785091964767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293191719258543426911906045 109946894721953785091964767)
    ·
      refine ⟨164920342082930677637947151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109946894721953785091964767 164920342082930677637947151)
      ·
        refine ⟨247380513124396016456920727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164920342082930677637947151 247380513124396016456920727)
        ·
          refine ⟨371070769686594024685381091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247380513124396016456920727 371070769686594024685381091)
          ·
            refine ⟨556606154529891037028071637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371070769686594024685381091 556606154529891037028071637)
            ·
              refine ⟨13045456746794321180345429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 556606154529891037028071637 13045456746794321180345429)
              ·
                refine ⟨152876446251495951332173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13045456746794321180345429 152876446251495951332173)
                ·
                  rfl

theorem cell23_8038597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 8].length) (baseStart_8038597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038597 prefixEnd_8038597 := by exact prefixLift 8038597
  have htrace : WordTrace (prefixWord ++ tailWord_8038597) baseStart_8038597 baseEnd_8038597 := by
    simpa [prefixWord, tailWord_8038597, baseEnd_8038597] using wordTrace_append hprefix tailTrace_8038597
  have hstable : (prefixWord ++ tailWord_8038597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038597).length < 2 ^ (prefixWord ++ tailWord_8038597).sum := by decide
  have hdescent : baseEnd_8038597 < baseStart_8038597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038621 : List Nat := [1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_8038621 : Nat := 118140960795 + 8038621 * 2 ^ 59
def prefixEnd_8038621 : Nat := 4983230072969 + 3 ^ 40 * 8038621 * 2
def baseEnd_8038621 : Nat := 4127676372326098592068561

theorem tailTrace_8038621 : CollatzResearch.WordTrace tailWord_8038621 prefixEnd_8038621 4127676372326098592068561 := by
  unfold tailWord_8038621
  simp only [CollatzResearch.WordTrace]
  refine ⟨293192594610456479010779717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195461729740304319340519811 293192594610456479010779717)
  ·
    refine ⟨54973611489460589814521197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293192594610456479010779717 54973611489460589814521197)
    ·
      refine ⟨20615104308547721180445449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54973611489460589814521197 20615104308547721180445449)
      ·
        refine ⟨15461328231410790885334087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20615104308547721180445449 15461328231410790885334087)
        ·
          refine ⟨23191992347116186328001131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15461328231410790885334087 23191992347116186328001131)
          ·
            refine ⟨34787988520674279492001697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23191992347116186328001131 34787988520674279492001697)
            ·
              refine ⟨26090991390505709619001273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34787988520674279492001697 26090991390505709619001273)
              ·
                refine ⟨19568243542879282214250955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26090991390505709619001273 19568243542879282214250955)
                ·
                  refine ⟨29352365314318923321376433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19568243542879282214250955 29352365314318923321376433)
                  ·
                    refine ⟨22014273985739192491032325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29352365314318923321376433 22014273985739192491032325)
                    ·
                      refine ⟨4127676372326098592068561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22014273985739192491032325 4127676372326098592068561)
                      ·
                        rfl

theorem cell23_8038621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_8038621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038621 prefixEnd_8038621 := by exact prefixLift 8038621
  have htrace : WordTrace (prefixWord ++ tailWord_8038621) baseStart_8038621 baseEnd_8038621 := by
    simpa [prefixWord, tailWord_8038621, baseEnd_8038621] using wordTrace_append hprefix tailTrace_8038621
  have hstable : (prefixWord ++ tailWord_8038621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038621).length < 2 ^ (prefixWord ++ tailWord_8038621).sum := by decide
  have hdescent : baseEnd_8038621 < baseStart_8038621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038624 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_8038624 : Nat := 118140960795 + 8038624 * 2 ^ 59
def prefixEnd_8038624 : Nat := 4983230072969 + 3 ^ 40 * 8038624 * 2
def baseEnd_8038624 : Nat := 4127677912768062080331047

theorem tailTrace_8038624 : CollatzResearch.WordTrace tailWord_8038624 prefixEnd_8038624 4127677912768062080331047 := by
  unfold tailWord_8038624
  simp only [CollatzResearch.WordTrace]
  refine ⟨146596352014722805261569463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195461802686297073682092617 146596352014722805261569463)
  ·
    refine ⟨219894528022084207892354195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146596352014722805261569463 219894528022084207892354195)
    ·
      refine ⟨329841792033126311838531293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219894528022084207892354195 329841792033126311838531293)
      ·
        refine ⟨123690672012422366939449235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329841792033126311838531293 123690672012422366939449235)
        ·
          refine ⟨185536008018633550409173853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123690672012422366939449235 185536008018633550409173853)
          ·
            refine ⟨69576003006987581403440195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185536008018633550409173853 69576003006987581403440195)
            ·
              refine ⟨104364004510481372105160293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69576003006987581403440195 104364004510481372105160293)
              ·
                refine ⟨19568250845715257269717555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104364004510481372105160293 19568250845715257269717555)
                ·
                  refine ⟨29352376268572885904576333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19568250845715257269717555 29352376268572885904576333)
                  ·
                    refine ⟨11007141100714832214216125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29352376268572885904576333 11007141100714832214216125)
                    ·
                      refine ⟨4127677912768062080331047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007141100714832214216125 4127677912768062080331047)
                      ·
                        rfl

theorem cell23_8038624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_8038624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038624 prefixEnd_8038624 := by exact prefixLift 8038624
  have htrace : WordTrace (prefixWord ++ tailWord_8038624) baseStart_8038624 baseEnd_8038624 := by
    simpa [prefixWord, tailWord_8038624, baseEnd_8038624] using wordTrace_append hprefix tailTrace_8038624
  have hstable : (prefixWord ++ tailWord_8038624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038624).length < 2 ^ (prefixWord ++ tailWord_8038624).sum := by decide
  have hdescent : baseEnd_8038624 < baseStart_8038624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038625 : List Nat := [1, 2, 3, 1, 3, 1, 4, 3, 1, 2, 2]
def baseStart_8038625 : Nat := 118140960795 + 8038625 * 2 ^ 59
def prefixEnd_8038625 : Nat := 4983230072969 + 3 ^ 40 * 8038625 * 2
def baseEnd_8038625 : Nat := 4127678426248716576418543

theorem tailTrace_8038625 : CollatzResearch.WordTrace tailWord_8038625 prefixEnd_8038625 4127678426248716576418543 := by
  unfold tailWord_8038625
  simp only [CollatzResearch.WordTrace]
  refine ⟨293192740502441987693925329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195461827001627991795950219 293192740502441987693925329)
  ·
    refine ⟨219894555376831490770443997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293192740502441987693925329 219894555376831490770443997)
    ·
      refine ⟨82460458266311809038916499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219894555376831490770443997 82460458266311809038916499)
      ·
        refine ⟨123690687399467713558374749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82460458266311809038916499 123690687399467713558374749)
        ·
          refine ⟨46384007774800392584390531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123690687399467713558374749 46384007774800392584390531)
          ·
            refine ⟨69576011662200588876585797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46384007774800392584390531 69576011662200588876585797)
            ·
              refine ⟨13045502186662610414359837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69576011662200588876585797 13045502186662610414359837)
              ·
                refine ⟨4892063319998478905384939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13045502186662610414359837 4892063319998478905384939)
                ·
                  refine ⟨7338094979997718358077409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892063319998478905384939 7338094979997718358077409)
                  ·
                    refine ⟨5503571234998288768558057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7338094979997718358077409 5503571234998288768558057)
                    ·
                      refine ⟨4127678426248716576418543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503571234998288768558057 4127678426248716576418543)
                      ·
                        rfl

theorem cell23_8038625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 2, 2].length) (baseStart_8038625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038625 prefixEnd_8038625 := by exact prefixLift 8038625
  have htrace : WordTrace (prefixWord ++ tailWord_8038625) baseStart_8038625 baseEnd_8038625 := by
    simpa [prefixWord, tailWord_8038625, baseEnd_8038625] using wordTrace_append hprefix tailTrace_8038625
  have hstable : (prefixWord ++ tailWord_8038625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038625).length < 2 ^ (prefixWord ++ tailWord_8038625).sum := by decide
  have hdescent : baseEnd_8038625 < baseStart_8038625 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038658 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_8038658 : Nat := 118140960795 + 8038658 * 2 ^ 59
def prefixEnd_8038658 : Nat := 4983230072969 + 3 ^ 40 * 8038658 * 2
def baseEnd_8038658 : Nat := 4127695371110314947305891

theorem tailTrace_8038658 : CollatzResearch.WordTrace tailWord_8038658 prefixEnd_8038658 4127695371110314947305891 := by
  unfold tailWord_8038658
  simp only [CollatzResearch.WordTrace]
  refine ⟨73298486027830608582469157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195462629407548289553251085 73298486027830608582469157)
  ·
    refine ⟨13743466130218239109212967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73298486027830608582469157 13743466130218239109212967)
    ·
      refine ⟨20615199195327358663819451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13743466130218239109212967 20615199195327358663819451)
      ·
        refine ⟨30922798792991037995729177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20615199195327358663819451 30922798792991037995729177)
        ·
          refine ⟨23192099094743278496796883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30922798792991037995729177 23192099094743278496796883)
          ·
            refine ⟨34788148642114917745195325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23192099094743278496796883 34788148642114917745195325)
            ·
              refine ⟨13045555740793094154448247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34788148642114917745195325 13045555740793094154448247)
              ·
                refine ⟨19568333611189641231672371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13045555740793094154448247 19568333611189641231672371)
                ·
                  refine ⟨29352500416784461847508557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19568333611189641231672371 29352500416784461847508557)
                  ·
                    refine ⟨11007187656294173192815709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29352500416784461847508557 11007187656294173192815709)
                    ·
                      refine ⟨4127695371110314947305891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007187656294173192815709 4127695371110314947305891)
                      ·
                        rfl

theorem cell23_8038658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_8038658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038658 prefixEnd_8038658 := by exact prefixLift 8038658
  have htrace : WordTrace (prefixWord ++ tailWord_8038658) baseStart_8038658 baseEnd_8038658 := by
    simpa [prefixWord, tailWord_8038658, baseEnd_8038658] using wordTrace_append hprefix tailTrace_8038658
  have hstable : (prefixWord ++ tailWord_8038658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038658).length < 2 ^ (prefixWord ++ tailWord_8038658).sum := by decide
  have hdescent : baseEnd_8038658 < baseStart_8038658 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038668 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_8038668 : Nat := 118140960795 + 8038668 * 2 ^ 59
def prefixEnd_8038668 : Nat := 4983230072969 + 3 ^ 40 * 8038668 * 2
def baseEnd_8038668 : Nat := 4127700505916859908180845

theorem tailTrace_8038668 : CollatzResearch.WordTrace tailWord_8038668 prefixEnd_8038668 4127700505916859908180845 := by
  unfold tailWord_8038668
  simp only [CollatzResearch.WordTrace]
  refine ⟨146597154420643103018870329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195462872560857470691827105 146597154420643103018870329)
  ·
    refine ⟨109947865815482327264152747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146597154420643103018870329 109947865815482327264152747)
    ·
      refine ⟨164921798723223490896229121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109947865815482327264152747 164921798723223490896229121)
      ·
        refine ⟨123691349042417618172171841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164921798723223490896229121 123691349042417618172171841)
        ·
          refine ⟨92768511781813213629128881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123691349042417618172171841 92768511781813213629128881)
          ·
            refine ⟨69576383836359910221846661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92768511781813213629128881 69576383836359910221846661)
            ·
              refine ⟨13045571969317483166596249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69576383836359910221846661 13045571969317483166596249)
              ·
                refine ⟨9784178976988112374947187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045571969317483166596249 9784178976988112374947187)
                ·
                  refine ⟨14676268465482168562420781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784178976988112374947187 14676268465482168562420781)
                  ·
                    refine ⟨5503600674555813210907793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676268465482168562420781 5503600674555813210907793)
                    ·
                      refine ⟨4127700505916859908180845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503600674555813210907793 4127700505916859908180845)
                      ·
                        rfl

theorem cell23_8038668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_8038668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038668 prefixEnd_8038668 := by exact prefixLift 8038668
  have htrace : WordTrace (prefixWord ++ tailWord_8038668) baseStart_8038668 baseEnd_8038668 := by
    simpa [prefixWord, tailWord_8038668, baseEnd_8038668] using wordTrace_append hprefix tailTrace_8038668
  have hstable : (prefixWord ++ tailWord_8038668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038668).length < 2 ^ (prefixWord ++ tailWord_8038668).sum := by decide
  have hdescent : baseEnd_8038668 < baseStart_8038668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038684 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_8038684 : Nat := 118140960795 + 8038684 * 2 ^ 59
def prefixEnd_8038684 : Nat := 4983230072969 + 3 ^ 40 * 8038684 * 2
def baseEnd_8038684 : Nat := 4127708721607331845580771

theorem tailTrace_8038684 : CollatzResearch.WordTrace tailWord_8038684 prefixEnd_8038684 4127708721607331845580771 := by
  unfold tailWord_8038684
  simp only [CollatzResearch.WordTrace]
  refine ⟨146597446204614120385161553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195463261606152160513548737 146597446204614120385161553)
  ·
    refine ⟨109948084653460590288871165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146597446204614120385161553 109948084653460590288871165)
    ·
      refine ⟨41230531745047721358326687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109948084653460590288871165 41230531745047721358326687)
      ·
        refine ⟨61845797617571582037490031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41230531745047721358326687 61845797617571582037490031)
        ·
          refine ⟨92768696426357373056235047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61845797617571582037490031 92768696426357373056235047)
          ·
            refine ⟨139153044639536059584352571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92768696426357373056235047 139153044639536059584352571)
            ·
              refine ⟨208729566959304089376528857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139153044639536059584352571 208729566959304089376528857)
              ·
                refine ⟨156547175219478067032396643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208729566959304089376528857 156547175219478067032396643)
                ·
                  refine ⟨234820762829217100548594965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156547175219478067032396643 234820762829217100548594965)
                  ·
                    refine ⟨11007223257619551588215389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 234820762829217100548594965 11007223257619551588215389)
                    ·
                      refine ⟨4127708721607331845580771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007223257619551588215389 4127708721607331845580771)
                      ·
                        rfl

theorem cell23_8038684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_8038684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038684 prefixEnd_8038684 := by exact prefixLift 8038684
  have htrace : WordTrace (prefixWord ++ tailWord_8038684) baseStart_8038684 baseEnd_8038684 := by
    simpa [prefixWord, tailWord_8038684, baseEnd_8038684] using wordTrace_append hprefix tailTrace_8038684
  have hstable : (prefixWord ++ tailWord_8038684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038684).length < 2 ^ (prefixWord ++ tailWord_8038684).sum := by decide
  have hdescent : baseEnd_8038684 < baseStart_8038684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038771 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 2, 4, 2]
def baseStart_8038771 : Nat := 118140960795 + 8038771 * 2 ^ 59
def prefixEnd_8038771 : Nat := 4983230072969 + 3 ^ 40 * 8038771 * 2
def baseEnd_8038771 : Nat := 4127753394424273005192871

theorem tailTrace_8038771 : CollatzResearch.WordTrace tailWord_8038771 prefixEnd_8038771 4127753394424273005192871 := by
  unfold tailWord_8038771
  simp only [CollatzResearch.WordTrace]
  refine ⟨293198065559913054628740167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195465377039942036419160111 293198065559913054628740167)
  ·
    refine ⟨439797098339869581943110251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293198065559913054628740167 439797098339869581943110251)
    ·
      refine ⟨659695647509804372914665377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439797098339869581943110251 659695647509804372914665377)
      ·
        refine ⟨494771735632353279685999033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659695647509804372914665377 494771735632353279685999033)
        ·
          refine ⟨371078801724264959764499275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494771735632353279685999033 371078801724264959764499275)
          ·
            refine ⟨556618202586397439646748913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371078801724264959764499275 556618202586397439646748913)
            ·
              refine ⟨417463651939798079735061685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556618202586397439646748913 417463651939798079735061685)
              ·
                refine ⟨39137217369356069975162033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417463651939798079735061685 39137217369356069975162033)
                ·
                  refine ⟨29352913027017052481371525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39137217369356069975162033 29352913027017052481371525)
                  ·
                    refine ⟨5503671192565697340257161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29352913027017052481371525 5503671192565697340257161)
                    ·
                      refine ⟨4127753394424273005192871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503671192565697340257161 4127753394424273005192871)
                      ·
                        rfl

theorem cell23_8038771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 4, 2].length) (baseStart_8038771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038771 prefixEnd_8038771 := by exact prefixLift 8038771
  have htrace : WordTrace (prefixWord ++ tailWord_8038771) baseStart_8038771 baseEnd_8038771 := by
    simpa [prefixWord, tailWord_8038771, baseEnd_8038771] using wordTrace_append hprefix tailTrace_8038771
  have hstable : (prefixWord ++ tailWord_8038771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038771).length < 2 ^ (prefixWord ++ tailWord_8038771).sum := by decide
  have hdescent : baseEnd_8038771 < baseStart_8038771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038781 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_8038781 : Nat := 118140960795 + 8038781 * 2 ^ 59
def prefixEnd_8038781 : Nat := 4983230072969 + 3 ^ 40 * 8038781 * 2
def baseEnd_8038781 : Nat := 1375919509743605988689275

theorem tailTrace_8038781 : CollatzResearch.WordTrace tailWord_8038781 prefixEnd_8038781 1375919509743605988689275 := by
  unfold tailWord_8038781
  simp only [CollatzResearch.WordTrace]
  refine ⟨293198430289876826336604197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195465620193251217557736131 293198430289876826336604197)
  ·
    refine ⟨54974705679351904938113287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293198430289876826336604197 54974705679351904938113287)
    ·
      refine ⟨82462058519027857407169931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54974705679351904938113287 82462058519027857407169931)
      ·
        refine ⟨123693087778541786110754897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82462058519027857407169931 123693087778541786110754897)
        ·
          refine ⟨92769815833906339583066173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123693087778541786110754897 92769815833906339583066173)
          ·
            refine ⟨34788680937714877343649815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92769815833906339583066173 34788680937714877343649815)
            ·
              refine ⟨52183021406572316015474723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34788680937714877343649815 52183021406572316015474723)
              ·
                refine ⟨78274532109858474023212085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52183021406572316015474723 78274532109858474023212085)
                ·
                  refine ⟨7338237385299231939676133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78274532109858474023212085 7338237385299231939676133)
                  ·
                    refine ⟨1375919509743605988689275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7338237385299231939676133 1375919509743605988689275)
                    ·
                      rfl

theorem cell23_8038781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_8038781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038781 prefixEnd_8038781 := by exact prefixLift 8038781
  have htrace : WordTrace (prefixWord ++ tailWord_8038781) baseStart_8038781 baseEnd_8038781 := by
    simpa [prefixWord, tailWord_8038781, baseEnd_8038781] using wordTrace_append hprefix tailTrace_8038781
  have hstable : (prefixWord ++ tailWord_8038781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038781).length < 2 ^ (prefixWord ++ tailWord_8038781).sum := by decide
  have hdescent : baseEnd_8038781 < baseStart_8038781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038791 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_8038791 : Nat := 118140960795 + 8038791 * 2 ^ 59
def prefixEnd_8038791 : Nat := 4983230072969 + 3 ^ 40 * 8038791 * 2
def baseEnd_8038791 : Nat := 4127763664037362926942779

theorem tailTrace_8038791 : CollatzResearch.WordTrace tailWord_8038791 prefixEnd_8038791 4127763664037362926942779 := by
  unfold tailWord_8038791
  simp only [CollatzResearch.WordTrace]
  refine ⟨293198795019840598044468227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195465863346560398696312151 293198795019840598044468227)
  ·
    refine ⟨439798192529760897066702341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293198795019840598044468227 439798192529760897066702341)
    ·
      refine ⟨82462161099330168200006689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439798192529760897066702341 82462161099330168200006689)
      ·
        refine ⟨61846620824497626150005017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82462161099330168200006689 61846620824497626150005017)
        ·
          refine ⟨46384965618373219612503763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61846620824497626150005017 46384965618373219612503763)
          ·
            refine ⟨69577448427559829418755645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46384965618373219612503763 69577448427559829418755645)
            ·
              refine ⟨26091543160334936032033367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69577448427559829418755645 26091543160334936032033367)
              ·
                refine ⟨39137314740502404048050051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26091543160334936032033367 39137314740502404048050051)
                ·
                  refine ⟨58705972110753606072075077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39137314740502404048050051 58705972110753606072075077)
                  ·
                    refine ⟨11007369770766301138514077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58705972110753606072075077 11007369770766301138514077)
                    ·
                      refine ⟨4127763664037362926942779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007369770766301138514077 4127763664037362926942779)
                      ·
                        rfl

theorem cell23_8038791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_8038791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038791 prefixEnd_8038791 := by exact prefixLift 8038791
  have htrace : WordTrace (prefixWord ++ tailWord_8038791) baseStart_8038791 baseEnd_8038791 := by
    simpa [prefixWord, tailWord_8038791, baseEnd_8038791] using wordTrace_append hprefix tailTrace_8038791
  have hstable : (prefixWord ++ tailWord_8038791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038791).length < 2 ^ (prefixWord ++ tailWord_8038791).sum := by decide
  have hdescent : baseEnd_8038791 < baseStart_8038791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038848 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2]
def baseStart_8038848 : Nat := 118140960795 + 8038848 * 2 ^ 59
def prefixEnd_8038848 : Nat := 4983230072969 + 3 ^ 40 * 8038848 * 2
def baseEnd_8038848 : Nat := 4127792932434669203930017

theorem tailTrace_8038848 : CollatzResearch.WordTrace tailWord_8038848 prefixEnd_8038848 4127792932434669203930017 := by
  unfold tailWord_8038848
  simp only [CollatzResearch.WordTrace]
  refine ⟨146600436990317048389646599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195467249320422731186195465 146600436990317048389646599)
  ·
    refine ⟨219900655485475572584469899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146600436990317048389646599 219900655485475572584469899)
    ·
      refine ⟨329850983228213358876704849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219900655485475572584469899 329850983228213358876704849)
      ·
        refine ⟨247388237421160019157528637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329850983228213358876704849 247388237421160019157528637)
        ·
          refine ⟨92770589032935007184073239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247388237421160019157528637 92770589032935007184073239)
          ·
            refine ⟨139155883549402510776109859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92770589032935007184073239 139155883549402510776109859)
            ·
              refine ⟨208733825324103766164164789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139155883549402510776109859 208733825324103766164164789)
              ·
                refine ⟨19568796124134728077890449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208733825324103766164164789 19568796124134728077890449)
                ·
                  refine ⟨14676597093101046058417837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19568796124134728077890449 14676597093101046058417837)
                  ·
                    refine ⟨5503723909912892271906689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676597093101046058417837 5503723909912892271906689)
                    ·
                      refine ⟨4127792932434669203930017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503723909912892271906689 4127792932434669203930017)
                      ·
                        rfl

theorem cell23_8038848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_8038848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038848 prefixEnd_8038848 := by exact prefixLift 8038848
  have htrace : WordTrace (prefixWord ++ tailWord_8038848) baseStart_8038848 baseEnd_8038848 := by
    simpa [prefixWord, tailWord_8038848, baseEnd_8038848] using wordTrace_append hprefix tailTrace_8038848
  have hstable : (prefixWord ++ tailWord_8038848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038848).length < 2 ^ (prefixWord ++ tailWord_8038848).sum := by decide
  have hdescent : baseEnd_8038848 < baseStart_8038848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038881 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_8038881 : Nat := 118140960795 + 8038881 * 2 ^ 59
def prefixEnd_8038881 : Nat := 4983230072969 + 3 ^ 40 * 8038881 * 2
def baseEnd_8038881 : Nat := 4127809877296267574817365

theorem tailTrace_8038881 : CollatzResearch.WordTrace tailWord_8038881 prefixEnd_8038881 4127809877296267574817365 := by
  unfold tailWord_8038881
  simp only [CollatzResearch.WordTrace]
  refine ⟨293202077589514543415244497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195468051726343028943496331 293202077589514543415244497)
  ·
    refine ⟨219901558192135907561433373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293202077589514543415244497 219901558192135907561433373)
    ·
      refine ⟨82463084322050965335537515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219901558192135907561433373 82463084322050965335537515)
      ·
        refine ⟨123694626483076448003306273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82463084322050965335537515 123694626483076448003306273)
        ·
          refine ⟨92770969862307336002479705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123694626483076448003306273 92770969862307336002479705)
          ·
            refine ⟨69578227396730502001859779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92770969862307336002479705 69578227396730502001859779)
            ·
              refine ⟨104367341095095753002789669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69578227396730502001859779 104367341095095753002789669)
              ·
                refine ⟨19568876455330453688023063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104367341095095753002789669 19568876455330453688023063)
                ·
                  refine ⟨29353314682995680532034595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19568876455330453688023063 29353314682995680532034595)
                  ·
                    refine ⟨44029972024493520798051893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29353314682995680532034595 44029972024493520798051893)
                    ·
                      refine ⟨4127809877296267574817365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44029972024493520798051893 4127809877296267574817365)
                      ·
                        rfl

theorem cell23_8038881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_8038881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038881 prefixEnd_8038881 := by exact prefixLift 8038881
  have htrace : WordTrace (prefixWord ++ tailWord_8038881) baseStart_8038881 baseEnd_8038881 := by
    simpa [prefixWord, tailWord_8038881, baseEnd_8038881] using wordTrace_append hprefix tailTrace_8038881
  have hstable : (prefixWord ++ tailWord_8038881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038881).length < 2 ^ (prefixWord ++ tailWord_8038881).sum := by decide
  have hdescent : baseEnd_8038881 < baseStart_8038881 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038891 : List Nat := [1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4]
def baseStart_8038891 : Nat := 118140960795 + 8038891 * 2 ^ 59
def prefixEnd_8038891 : Nat := 4983230072969 + 3 ^ 40 * 8038891 * 2
def baseEnd_8038891 : Nat := 4127815012102812535692319

theorem tailTrace_8038891 : CollatzResearch.WordTrace tailWord_8038891 prefixEnd_8038891 4127815012102812535692319 := by
  unfold tailWord_8038891
  simp only [CollatzResearch.WordTrace]
  refine ⟨293202442319478315123108527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195468294879652210082072351 293202442319478315123108527)
  ·
    refine ⟨439803663479217472684662791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293202442319478315123108527 439803663479217472684662791)
    ·
      refine ⟨659705495218826209026994187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439803663479217472684662791 659705495218826209026994187)
      ·
        refine ⟨989558242828239313540491281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659705495218826209026994187 989558242828239313540491281)
        ·
          refine ⟨742168682121179485155368461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989558242828239313540491281 742168682121179485155368461)
          ·
            refine ⟨278313255795442306933263173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742168682121179485155368461 278313255795442306933263173)
            ·
              refine ⟨52183735461645432549986845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278313255795442306933263173 52183735461645432549986845)
              ·
                refine ⟨19568900798117037206245067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52183735461645432549986845 19568900798117037206245067)
                ·
                  refine ⟨29353351197175555809367601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19568900798117037206245067 29353351197175555809367601)
                  ·
                    refine ⟨22015013397881666857025701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29353351197175555809367601 22015013397881666857025701)
                    ·
                      refine ⟨4127815012102812535692319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22015013397881666857025701 4127815012102812535692319)
                      ·
                        rfl

theorem cell23_8038891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 4].length) (baseStart_8038891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038891 prefixEnd_8038891 := by exact prefixLift 8038891
  have htrace : WordTrace (prefixWord ++ tailWord_8038891) baseStart_8038891 baseEnd_8038891 := by
    simpa [prefixWord, tailWord_8038891, baseEnd_8038891] using wordTrace_append hprefix tailTrace_8038891
  have hstable : (prefixWord ++ tailWord_8038891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038891).length < 2 ^ (prefixWord ++ tailWord_8038891).sum := by decide
  have hdescent : baseEnd_8038891 < baseStart_8038891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038915 : List Nat := [1, 1, 1, 3, 2, 1, 7, 1, 1, 2, 3]
def baseStart_8038915 : Nat := 118140960795 + 8038915 * 2 ^ 59
def prefixEnd_8038915 : Nat := 4983230072969 + 3 ^ 40 * 8038915 * 2
def baseEnd_8038915 : Nat := 4127827335638520441792209

theorem tailTrace_8038915 : CollatzResearch.WordTrace tailWord_8038915 prefixEnd_8038915 4127827335638520441792209 := by
  unfold tailWord_8038915
  simp only [CollatzResearch.WordTrace]
  refine ⟨293203317671391367221982199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195468878447594244814654799 293203317671391367221982199)
  ·
    refine ⟨439804976507087050832973299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293203317671391367221982199 439804976507087050832973299)
    ·
      refine ⟨659707464760630576249459949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439804976507087050832973299 659707464760630576249459949)
      ·
        refine ⟨247390299285236466093547481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659707464760630576249459949 247390299285236466093547481)
        ·
          refine ⟨185542724463927349570160611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247390299285236466093547481 185542724463927349570160611)
          ·
            refine ⟨278314086695891024355240917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185542724463927349570160611 278314086695891024355240917)
            ·
              refine ⟨6522986406934945883325959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278314086695891024355240917 6522986406934945883325959)
              ·
                refine ⟨9784479610402418824988939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6522986406934945883325959 9784479610402418824988939)
                ·
                  refine ⟨14676719415603628237483409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784479610402418824988939 14676719415603628237483409)
                  ·
                    refine ⟨11007539561702721178112557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14676719415603628237483409 11007539561702721178112557)
                    ·
                      refine ⟨4127827335638520441792209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007539561702721178112557 4127827335638520441792209)
                      ·
                        rfl

theorem cell23_8038915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_8038915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038915 prefixEnd_8038915 := by exact prefixLift 8038915
  have htrace : WordTrace (prefixWord ++ tailWord_8038915) baseStart_8038915 baseEnd_8038915 := by
    simpa [prefixWord, tailWord_8038915, baseEnd_8038915] using wordTrace_append hprefix tailTrace_8038915
  have hstable : (prefixWord ++ tailWord_8038915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038915).length < 2 ^ (prefixWord ++ tailWord_8038915).sum := by decide
  have hdescent : baseEnd_8038915 < baseStart_8038915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038935 : List Nat := [1, 1, 3, 6, 1, 2, 1, 8]
def baseStart_8038935 : Nat := 118140960795 + 8038935 * 2 ^ 59
def prefixEnd_8038935 : Nat := 4983230072969 + 3 ^ 40 * 8038935 * 2
def baseEnd_8038935 : Nat := 152882874268578161612671

theorem tailTrace_8038935 : CollatzResearch.WordTrace tailWord_8038935 prefixEnd_8038935 152882874268578161612671 := by
  unfold tailWord_8038935
  simp only [CollatzResearch.WordTrace]
  refine ⟨293204047131318910637710259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195469364754212607091806839 293204047131318910637710259)
  ·
    refine ⟨439806070696978365956565389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293204047131318910637710259 439806070696978365956565389)
    ·
      refine ⟨164927276511366887233712021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439806070696978365956565389 164927276511366887233712021)
      ·
        refine ⟨7730966086470322839080251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 164927276511366887233712021 7730966086470322839080251)
        ·
          refine ⟨11596449129705484258620377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730966086470322839080251 11596449129705484258620377)
          ·
            refine ⟨8697336847279113193965283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11596449129705484258620377 8697336847279113193965283)
            ·
              refine ⟨13046005270918669790947925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697336847279113193965283 13046005270918669790947925)
              ·
                refine ⟨152882874268578161612671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13046005270918669790947925 152882874268578161612671)
                ·
                  rfl

theorem cell23_8038935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 8].length) (baseStart_8038935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038935 prefixEnd_8038935 := by exact prefixLift 8038935
  have htrace : WordTrace (prefixWord ++ tailWord_8038935) baseStart_8038935 baseEnd_8038935 := by
    simpa [prefixWord, tailWord_8038935, baseEnd_8038935] using wordTrace_append hprefix tailTrace_8038935
  have hstable : (prefixWord ++ tailWord_8038935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038935).length < 2 ^ (prefixWord ++ tailWord_8038935).sum := by decide
  have hdescent : baseEnd_8038935 < baseStart_8038935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038945 : List Nat := [1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_8038945 : Nat := 118140960795 + 8038945 * 2 ^ 59
def prefixEnd_8038945 : Nat := 4983230072969 + 3 ^ 40 * 8038945 * 2
def baseEnd_8038945 : Nat := 4127842740058155324417071

theorem tailTrace_8038945 : CollatzResearch.WordTrace tailWord_8038945 prefixEnd_8038945 4127842740058155324417071 := by
  unfold tailWord_8038945
  simp only [CollatzResearch.WordTrace]
  refine ⟨293204411861282682345574289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195469607907521788230382859 293204411861282682345574289)
  ·
    refine ⟨219903308895962011759180717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293204411861282682345574289 219903308895962011759180717)
    ·
      refine ⟨82463740835985754409692769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219903308895962011759180717 82463740835985754409692769)
      ·
        refine ⟨61847805626989315807269577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82463740835985754409692769 61847805626989315807269577)
        ·
          refine ⟨46385854220241986855452183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61847805626989315807269577 46385854220241986855452183)
          ·
            refine ⟨69578781330362980283178275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46385854220241986855452183 69578781330362980283178275)
            ·
              refine ⟨104368171995544470424767413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69578781330362980283178275 104368171995544470424767413)
              ·
                refine ⟨9784516124582294102321945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104368171995544470424767413 9784516124582294102321945)
                ·
                  refine ⟨7338387093436720576741459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9784516124582294102321945 7338387093436720576741459)
                  ·
                    refine ⟨11007580640155080865112189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7338387093436720576741459 11007580640155080865112189)
                    ·
                      refine ⟨4127842740058155324417071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007580640155080865112189 4127842740058155324417071)
                      ·
                        rfl

theorem cell23_8038945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_8038945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038945 prefixEnd_8038945 := by exact prefixLift 8038945
  have htrace : WordTrace (prefixWord ++ tailWord_8038945) baseStart_8038945 baseEnd_8038945 := by
    simpa [prefixWord, tailWord_8038945, baseEnd_8038945] using wordTrace_append hprefix tailTrace_8038945
  have hstable : (prefixWord ++ tailWord_8038945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038945).length < 2 ^ (prefixWord ++ tailWord_8038945).sum := by decide
  have hdescent : baseEnd_8038945 < baseStart_8038945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038972 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_8038972 : Nat := 118140960795 + 8038972 * 2 ^ 59
def prefixEnd_8038972 : Nat := 4983230072969 + 3 ^ 40 * 8038972 * 2
def baseEnd_8038972 : Nat := 4127856604035826718779447

theorem tailTrace_8038972 : CollatzResearch.WordTrace tailWord_8038972 prefixEnd_8038972 4127856604035826718779447 := by
  unfold tailWord_8038972
  simp only [CollatzResearch.WordTrace]
  refine ⟨146602698316092432978403585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195470264421456577304538113 146602698316092432978403585)
  ·
    refine ⟨109952023737069324733802689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146602698316092432978403585 109952023737069324733802689)
    ·
      refine ⟨82464017802801993550352017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109952023737069324733802689 82464017802801993550352017)
      ·
        refine ⟨61848013352101495162764013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82464017802801993550352017 61848013352101495162764013)
        ·
          refine ⟨23193005007038060686036505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61848013352101495162764013 23193005007038060686036505)
          ·
            refine ⟨17394753755278545514527379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23193005007038060686036505 17394753755278545514527379)
            ·
              refine ⟨26092130632917818271791069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17394753755278545514527379 26092130632917818271791069)
              ·
                refine ⟨9784548987344181851921651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26092130632917818271791069 9784548987344181851921651)
                ·
                  refine ⟨14676823481016272777882477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784548987344181851921651 14676823481016272777882477)
                  ·
                    refine ⟨5503808805381102291705929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14676823481016272777882477 5503808805381102291705929)
                    ·
                      refine ⟨4127856604035826718779447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5503808805381102291705929 4127856604035826718779447)
                      ·
                        rfl

theorem cell23_8038972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_8038972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038972 prefixEnd_8038972 := by exact prefixLift 8038972
  have htrace : WordTrace (prefixWord ++ tailWord_8038972) baseStart_8038972 baseEnd_8038972 := by
    simpa [prefixWord, tailWord_8038972, baseEnd_8038972] using wordTrace_append hprefix tailTrace_8038972
  have hstable : (prefixWord ++ tailWord_8038972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038972).length < 2 ^ (prefixWord ++ tailWord_8038972).sum := by decide
  have hdescent : baseEnd_8038972 < baseStart_8038972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8038991 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 7]
def baseStart_8038991 : Nat := 118140960795 + 8038991 * 2 ^ 59
def prefixEnd_8038991 : Nat := 4983230072969 + 3 ^ 40 * 8038991 * 2
def baseEnd_8038991 : Nat := 458651817796473571604651

theorem tailTrace_8038991 : CollatzResearch.WordTrace tailWord_8038991 prefixEnd_8038991 458651817796473571604651 := by
  unfold tailWord_8038991
  simp only [CollatzResearch.WordTrace]
  refine ⟨293206089619116032201748827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195470726412744021467832551 293206089619116032201748827)
  ·
    refine ⟨439809134428674048302623241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293206089619116032201748827 439809134428674048302623241)
    ·
      refine ⟨329856850821505536226967431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439809134428674048302623241 329856850821505536226967431)
      ·
        refine ⟨494785276232258304340451147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329856850821505536226967431 494785276232258304340451147)
        ·
          refine ⟨742177914348387456510676721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494785276232258304340451147 742177914348387456510676721)
          ·
            refine ⟨556633435761290592383007541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742177914348387456510676721 556633435761290592383007541)
            ·
              refine ⟨52184384602620993035906957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556633435761290592383007541 52184384602620993035906957)
              ·
                refine ⟨19569144225982872388465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52184384602620993035906957 19569144225982872388465109)
                ·
                  refine ⟨458651817796473571604651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19569144225982872388465109 458651817796473571604651)
                  ·
                    rfl

theorem cell23_8038991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 7].length) (baseStart_8038991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8038991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8038991 prefixEnd_8038991 := by exact prefixLift 8038991
  have htrace : WordTrace (prefixWord ++ tailWord_8038991) baseStart_8038991 baseEnd_8038991 := by
    simpa [prefixWord, tailWord_8038991, baseEnd_8038991] using wordTrace_append hprefix tailTrace_8038991
  have hstable : (prefixWord ++ tailWord_8038991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8038991).length < 2 ^ (prefixWord ++ tailWord_8038991).sum := by decide
  have hdescent : baseEnd_8038991 < baseStart_8038991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8038991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039051 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 8]
def baseStart_8039051 : Nat := 118140960795 + 8039051 * 2 ^ 59
def prefixEnd_8039051 : Nat := 4983230072969 + 3 ^ 40 * 8039051 * 2
def baseEnd_8039051 : Nat := 1375965723002510636563861

theorem tailTrace_8039051 : CollatzResearch.WordTrace tailWord_8039051 prefixEnd_8039051 1375965723002510636563861 := by
  unfold tailWord_8039051
  simp only [CollatzResearch.WordTrace]
  refine ⟨293208277998898662448933007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195472185332599108299288671 293208277998898662448933007)
  ·
    refine ⟨439812416998347993673399511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293208277998898662448933007 439812416998347993673399511)
    ·
      refine ⟨659718625497521990510099267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439812416998347993673399511 659718625497521990510099267)
      ·
        refine ⟨989577938246282985765148901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659718625497521990510099267 989577938246282985765148901)
        ·
          refine ⟨185545863421178059830965419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 989577938246282985765148901 185545863421178059830965419)
          ·
            refine ⟨278318795131767089746448129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185545863421178059830965419 278318795131767089746448129)
            ·
              refine ⟨208739096348825317309836097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278318795131767089746448129 208739096348825317309836097)
              ·
                refine ⟨156554322261618987982377073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208739096348825317309836097 156554322261618987982377073)
                ·
                  refine ⟨117415741696214240986782805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156554322261618987982377073 117415741696214240986782805)
                  ·
                    refine ⟨1375965723002510636563861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117415741696214240986782805 1375965723002510636563861)
                    ·
                      rfl

theorem cell23_8039051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_8039051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039051 prefixEnd_8039051 := by exact prefixLift 8039051
  have htrace : WordTrace (prefixWord ++ tailWord_8039051) baseStart_8039051 baseEnd_8039051 := by
    simpa [prefixWord, tailWord_8039051, baseEnd_8039051] using wordTrace_append hprefix tailTrace_8039051
  have hstable : (prefixWord ++ tailWord_8039051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039051).length < 2 ^ (prefixWord ++ tailWord_8039051).sum := by decide
  have hdescent : baseEnd_8039051 < baseStart_8039051 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039185 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_8039185 : Nat := 118140960795 + 8039185 * 2 ^ 59
def prefixEnd_8039185 : Nat := 4983230072969 + 3 ^ 40 * 8039185 * 2
def baseEnd_8039185 : Nat := 4127965975415234385415967

theorem tailTrace_8039185 : CollatzResearch.WordTrace tailWord_8039185 prefixEnd_8039185 4127965975415234385415967 := by
  unfold tailWord_8039185
  simp only [CollatzResearch.WordTrace]
  refine ⟨293213165380413203334311009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195475443586942135556207339 293213165380413203334311009)
  ·
    refine ⟨219909874035309902500733257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293213165380413203334311009 219909874035309902500733257)
    ·
      refine ⟨164932405526482426875549943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219909874035309902500733257 164932405526482426875549943)
      ·
        refine ⟨247398608289723640313324915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164932405526482426875549943 247398608289723640313324915)
        ·
          refine ⟨371097912434585460469987373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247398608289723640313324915 371097912434585460469987373)
          ·
            refine ⟨139161717162969547676245265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371097912434585460469987373 139161717162969547676245265)
            ·
              refine ⟨104371287872227160757183949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139161717162969547676245265 104371287872227160757183949)
              ·
                refine ⟨39139232952085185283943981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104371287872227160757183949 39139232952085185283943981)
                ·
                  refine ⟨14677212357031944481478993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39139232952085185283943981 14677212357031944481478993)
                  ·
                    refine ⟨11007909267773958361109245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14677212357031944481478993 11007909267773958361109245)
                    ·
                      refine ⟨4127965975415234385415967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007909267773958361109245 4127965975415234385415967)
                      ·
                        rfl

theorem cell23_8039185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_8039185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039185 prefixEnd_8039185 := by exact prefixLift 8039185
  have htrace : WordTrace (prefixWord ++ tailWord_8039185) baseStart_8039185 baseEnd_8039185 := by
    simpa [prefixWord, tailWord_8039185, baseEnd_8039185] using wordTrace_append hprefix tailTrace_8039185
  have hstable : (prefixWord ++ tailWord_8039185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039185).length < 2 ^ (prefixWord ++ tailWord_8039185).sum := by decide
  have hdescent : baseEnd_8039185 < baseStart_8039185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039202 : List Nat := [3, 3, 1, 1, 2, 3, 2, 1, 1, 1, 5]
def baseStart_8039202 : Nat := 118140960795 + 8039202 * 2 ^ 59
def prefixEnd_8039202 : Nat := 4983230072969 + 3 ^ 40 * 8039202 * 2
def baseEnd_8039202 : Nat := 4127974704586360818903389

theorem tailTrace_8039202 : CollatzResearch.WordTrace tailWord_8039202 prefixEnd_8039202 4127974704586360818903389 := by
  unfold tailWord_8039202
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303446355337903809419965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195475856947567743491786573 73303446355337903809419965)
  ·
    refine ⟨27488792383251713928532487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73303446355337903809419965 27488792383251713928532487)
    ·
      refine ⟨41233188574877570892798731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27488792383251713928532487 41233188574877570892798731)
      ·
        refine ⟨61849782862316356339198097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41233188574877570892798731 61849782862316356339198097)
        ·
          refine ⟨46387337146737267254398573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61849782862316356339198097 46387337146737267254398573)
          ·
            refine ⟨17395251430026475220399465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46387337146737267254398573 17395251430026475220399465)
            ·
              refine ⟨13046438572519856415299599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17395251430026475220399465 13046438572519856415299599)
              ·
                refine ⟨19569657858779784622949399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046438572519856415299599 19569657858779784622949399)
                ·
                  refine ⟨29354486788169676934424099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19569657858779784622949399 29354486788169676934424099)
                  ·
                    refine ⟨44031730182254515401636149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29354486788169676934424099 44031730182254515401636149)
                    ·
                      refine ⟨4127974704586360818903389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44031730182254515401636149 4127974704586360818903389)
                      ·
                        rfl

theorem cell23_8039202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_8039202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039202 prefixEnd_8039202 := by exact prefixLift 8039202
  have htrace : WordTrace (prefixWord ++ tailWord_8039202) baseStart_8039202 baseEnd_8039202 := by
    simpa [prefixWord, tailWord_8039202, baseEnd_8039202] using wordTrace_append hprefix tailTrace_8039202
  have hstable : (prefixWord ++ tailWord_8039202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039202).length < 2 ^ (prefixWord ++ tailWord_8039202).sum := by decide
  have hdescent : baseEnd_8039202 < baseStart_8039202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039210 : List Nat := [3, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_8039210 : Nat := 118140960795 + 8039210 * 2 ^ 59
def prefixEnd_8039210 : Nat := 4983230072969 + 3 ^ 40 * 8039210 * 2
def baseEnd_8039210 : Nat := 4127978812431596787603353

theorem tailTrace_8039210 : CollatzResearch.WordTrace tailWord_8039210 prefixEnd_8039210 4127978812431596787603353 := by
  unfold tailWord_8039210
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303519301330658150992771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195476051470215088402647389 73303519301330658150992771)
  ·
    refine ⟨109955278951995987226489157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73303519301330658150992771 109955278951995987226489157)
    ·
      refine ⟨20616614803499247604966717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109955278951995987226489157 20616614803499247604966717)
      ·
        refine ⟨7731230551312217851862519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20616614803499247604966717 7731230551312217851862519)
        ·
          refine ⟨11596845826968326777793779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731230551312217851862519 11596845826968326777793779)
          ·
            refine ⟨17395268740452490166690669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596845826968326777793779 17395268740452490166690669)
            ·
              refine ⟨6523225777669683812509001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17395268740452490166690669 6523225777669683812509001)
              ·
                refine ⟨4892419333252262859381751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523225777669683812509001 4892419333252262859381751)
                ·
                  refine ⟨7338628999878394289072627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892419333252262859381751 7338628999878394289072627)
                  ·
                    refine ⟨11007943499817591433608941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7338628999878394289072627 11007943499817591433608941)
                    ·
                      refine ⟨4127978812431596787603353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007943499817591433608941 4127978812431596787603353)
                      ·
                        rfl

theorem cell23_8039210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_8039210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039210 prefixEnd_8039210 := by exact prefixLift 8039210
  have htrace : WordTrace (prefixWord ++ tailWord_8039210) baseStart_8039210 baseEnd_8039210 := by
    simpa [prefixWord, tailWord_8039210, baseEnd_8039210] using wordTrace_append hprefix tailTrace_8039210
  have hstable : (prefixWord ++ tailWord_8039210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039210).length < 2 ^ (prefixWord ++ tailWord_8039210).sum := by decide
  have hdescent : baseEnd_8039210 < baseStart_8039210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039226 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_8039226 : Nat := 118140960795 + 8039226 * 2 ^ 59
def prefixEnd_8039226 : Nat := 4983230072969 + 3 ^ 40 * 8039226 * 2
def baseEnd_8039226 : Nat := 1375995676040689575001093

theorem tailTrace_8039226 : CollatzResearch.WordTrace tailWord_8039226 prefixEnd_8039226 1375995676040689575001093 := by
  unfold tailWord_8039226
  simp only [CollatzResearch.WordTrace]
  refine ⟨73303665193316166834138383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195476440515509778224369021 73303665193316166834138383)
  ·
    refine ⟨109955497789974250251207575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73303665193316166834138383 109955497789974250251207575)
    ·
      refine ⟨164933246684961375376811363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109955497789974250251207575 164933246684961375376811363)
      ·
        refine ⟨247399870027442063065217045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164933246684961375376811363 247399870027442063065217045)
        ·
          refine ⟨11596868907536346706182049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247399870027442063065217045 11596868907536346706182049)
          ·
            refine ⟨8697651680652260029636537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11596868907536346706182049 8697651680652260029636537)
            ·
              refine ⟨6523238760489195022227403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697651680652260029636537 6523238760489195022227403)
              ·
                refine ⟨9784858140733792533341105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523238760489195022227403 9784858140733792533341105)
                ·
                  refine ⟨7338643605550344400005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9784858140733792533341105 7338643605550344400005829)
                  ·
                    refine ⟨1375995676040689575001093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7338643605550344400005829 1375995676040689575001093)
                    ·
                      rfl

theorem cell23_8039226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_8039226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039226 prefixEnd_8039226 := by exact prefixLift 8039226
  have htrace : WordTrace (prefixWord ++ tailWord_8039226) baseStart_8039226 baseEnd_8039226 := by
    simpa [prefixWord, tailWord_8039226, baseEnd_8039226] using wordTrace_append hprefix tailTrace_8039226
  have hstable : (prefixWord ++ tailWord_8039226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039226).length < 2 ^ (prefixWord ++ tailWord_8039226).sum := by decide
  have hdescent : baseEnd_8039226 < baseStart_8039226 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039233 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 1, 1, 4]
def baseStart_8039233 : Nat := 118140960795 + 8039233 * 2 ^ 59
def prefixEnd_8039233 : Nat := 4983230072969 + 3 ^ 40 * 8039233 * 2
def baseEnd_8039233 : Nat := 4127990622486650197615747

theorem tailTrace_8039233 : CollatzResearch.WordTrace tailWord_8039233 prefixEnd_8039233 4127990622486650197615747 := by
  unfold tailWord_8039233
  simp only [CollatzResearch.WordTrace]
  refine ⟨293214916084239307532058353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195476610722826205021372235 293214916084239307532058353)
  ·
    refine ⟨219911187063179480649043765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293214916084239307532058353 219911187063179480649043765)
    ·
      refine ⟨20616673787173076310847853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219911187063179480649043765 20616673787173076310847853)
      ·
        refine ⟨7731252670189903616567945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20616673787173076310847853 7731252670189903616567945)
        ·
          refine ⟨5798439502642427712425959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7731252670189903616567945 5798439502642427712425959)
          ·
            refine ⟨8697659253963641568638939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798439502642427712425959 8697659253963641568638939)
            ·
              refine ⟨13046488880945462352958409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697659253963641568638939 13046488880945462352958409)
              ·
                refine ⟨9784866660709096764718807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13046488880945462352958409 9784866660709096764718807)
                ·
                  refine ⟨14677299991063645147078211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9784866660709096764718807 14677299991063645147078211)
                  ·
                    refine ⟨22015949986595467720617317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14677299991063645147078211 22015949986595467720617317)
                    ·
                      refine ⟨4127990622486650197615747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22015949986595467720617317 4127990622486650197615747)
                      ·
                        rfl

theorem cell23_8039233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_8039233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039233 prefixEnd_8039233 := by exact prefixLift 8039233
  have htrace : WordTrace (prefixWord ++ tailWord_8039233) baseStart_8039233 baseEnd_8039233 := by
    simpa [prefixWord, tailWord_8039233, baseEnd_8039233] using wordTrace_append hprefix tailTrace_8039233
  have hstable : (prefixWord ++ tailWord_8039233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039233).length < 2 ^ (prefixWord ++ tailWord_8039233).sum := by decide
  have hdescent : baseEnd_8039233 < baseStart_8039233 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039236 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_8039236 : Nat := 118140960795 + 8039236 * 2 ^ 59
def prefixEnd_8039236 : Nat := 4983230072969 + 3 ^ 40 * 8039236 * 2
def baseEnd_8039236 : Nat := 4127992162928613685878233

theorem tailTrace_8039236 : CollatzResearch.WordTrace tailWord_8039236 prefixEnd_8039236 4127992162928613685878233 := by
  unfold tailWord_8039236
  simp only [CollatzResearch.WordTrace]
  refine ⟨146607512751614219522208781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195476683668818959362945041 146607512751614219522208781)
  ·
    refine ⟨54977817281855332320828293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146607512751614219522208781 54977817281855332320828293)
    ·
      refine ⟨10308340740347874810155305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54977817281855332320828293 10308340740347874810155305)
      ·
        refine ⟨7731255555260906107616479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308340740347874810155305 7731255555260906107616479)
        ·
          refine ⟨11596883332891359161424719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731255555260906107616479 11596883332891359161424719)
          ·
            refine ⟨17395324999337038742137079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11596883332891359161424719 17395324999337038742137079)
            ·
              refine ⟨26092987499005558113205619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395324999337038742137079 26092987499005558113205619)
              ·
                refine ⟨39139481248508337169808429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26092987499005558113205619 39139481248508337169808429)
                ·
                  refine ⟨14677305468190626438678161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39139481248508337169808429 14677305468190626438678161)
                  ·
                    refine ⟨11007979101142969829008621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14677305468190626438678161 11007979101142969829008621)
                    ·
                      refine ⟨4127992162928613685878233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11007979101142969829008621 4127992162928613685878233)
                      ·
                        rfl

theorem cell23_8039236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_8039236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039236 prefixEnd_8039236 := by exact prefixLift 8039236
  have htrace : WordTrace (prefixWord ++ tailWord_8039236) baseStart_8039236 baseEnd_8039236 := by
    simpa [prefixWord, tailWord_8039236, baseEnd_8039236] using wordTrace_append hprefix tailTrace_8039236
  have hstable : (prefixWord ++ tailWord_8039236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039236).length < 2 ^ (prefixWord ++ tailWord_8039236).sum := by decide
  have hdescent : baseEnd_8039236 < baseStart_8039236 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039275 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3]
def baseStart_8039275 : Nat := 118140960795 + 8039275 * 2 ^ 59
def prefixEnd_8039275 : Nat := 4983230072969 + 3 ^ 40 * 8039275 * 2
def baseEnd_8039275 : Nat := 4128012188674139033290553

theorem tailTrace_8039275 : CollatzResearch.WordTrace tailWord_8039275 prefixEnd_8039275 4128012188674139033290553 := by
  unfold tailWord_8039275
  simp only [CollatzResearch.WordTrace]
  refine ⟨293216447950087148705087279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195477631966724765803391519 293216447950087148705087279)
  ·
    refine ⟨439824671925130723057630919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293216447950087148705087279 439824671925130723057630919)
    ·
      refine ⟨659737007887696084586446379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439824671925130723057630919 659737007887696084586446379)
      ·
        refine ⟨989605511831544126879669569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659737007887696084586446379 989605511831544126879669569)
        ·
          refine ⟨742204133873658095159752177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989605511831544126879669569 742204133873658095159752177)
          ·
            refine ⟨556653100405243571369814133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742204133873658095159752177 556653100405243571369814133)
            ·
              refine ⟨52186228162991584815920075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 556653100405243571369814133 52186228162991584815920075)
              ·
                refine ⟨78279342244487377223880113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52186228162991584815920075 78279342244487377223880113)
                ·
                  refine ⟨58709506683365532917910085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78279342244487377223880113 58709506683365532917910085)
                  ·
                    refine ⟨11008032503131037422108141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58709506683365532917910085 11008032503131037422108141)
                    ·
                      refine ⟨4128012188674139033290553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008032503131037422108141 4128012188674139033290553)
                      ·
                        rfl

theorem cell23_8039275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 3].length) (baseStart_8039275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039275 prefixEnd_8039275 := by exact prefixLift 8039275
  have htrace : WordTrace (prefixWord ++ tailWord_8039275) baseStart_8039275 baseEnd_8039275 := by
    simpa [prefixWord, tailWord_8039275, baseEnd_8039275] using wordTrace_append hprefix tailTrace_8039275
  have hstable : (prefixWord ++ tailWord_8039275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039275).length < 2 ^ (prefixWord ++ tailWord_8039275).sum := by decide
  have hdescent : baseEnd_8039275 < baseStart_8039275 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039289 : List Nat := [1, 2, 1, 3, 2, 4, 2, 1, 1, 4, 2]
def baseStart_8039289 : Nat := 118140960795 + 8039289 * 2 ^ 59
def prefixEnd_8039289 : Nat := 4983230072969 + 3 ^ 40 * 8039289 * 2
def baseEnd_8039289 : Nat := 4128019377403301978515489

theorem tailTrace_8039289 : CollatzResearch.WordTrace tailWord_8039289 prefixEnd_8039289 4128019377403301978515489 := by
  unfold tailWord_8039289
  simp only [CollatzResearch.WordTrace]
  refine ⟨293216958572036429096096921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195477972381357619397397947 293216958572036429096096921)
  ·
    refine ⟨219912718929027321822072691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293216958572036429096096921 219912718929027321822072691)
    ·
      refine ⟨329869078393540982733109037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219912718929027321822072691 329869078393540982733109037)
      ·
        refine ⟨123700904397577868524915889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329869078393540982733109037 123700904397577868524915889)
        ·
          refine ⟨92775678298183401393686917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123700904397577868524915889 92775678298183401393686917)
          ·
            refine ⟨17395439680909387761316297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92775678298183401393686917 17395439680909387761316297)
            ·
              refine ⟨13046579760682040820987223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17395439680909387761316297 13046579760682040820987223)
              ·
                refine ⟨19569869641023061231480835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046579760682040820987223 19569869641023061231480835)
                ·
                  refine ⟨29354804461534591847221253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19569869641023061231480835 29354804461534591847221253)
                  ·
                    refine ⟨5504025836537735971353985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29354804461534591847221253 5504025836537735971353985)
                    ·
                      refine ⟨4128019377403301978515489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504025836537735971353985 4128019377403301978515489)
                      ·
                        rfl

theorem cell23_8039289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_8039289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039289 prefixEnd_8039289 := by exact prefixLift 8039289
  have htrace : WordTrace (prefixWord ++ tailWord_8039289) baseStart_8039289 baseEnd_8039289 := by
    simpa [prefixWord, tailWord_8039289, baseEnd_8039289] using wordTrace_append hprefix tailTrace_8039289
  have hstable : (prefixWord ++ tailWord_8039289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039289).length < 2 ^ (prefixWord ++ tailWord_8039289).sum := by decide
  have hdescent : baseEnd_8039289 < baseStart_8039289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039329 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 5]
def baseStart_8039329 : Nat := 118140960795 + 8039329 * 2 ^ 59
def prefixEnd_8039329 : Nat := 4983230072969 + 3 ^ 40 * 8039329 * 2
def baseEnd_8039329 : Nat := 458671101847720202446145

theorem tailTrace_8039329 : CollatzResearch.WordTrace tailWord_8039329 prefixEnd_8039329 458671101847720202446145 := by
  unfold tailWord_8039329
  simp only [CollatzResearch.WordTrace]
  refine ⟨293218417491891515927553041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195478944994594343951702027 293218417491891515927553041)
  ·
    refine ⟨219913813118918636945664781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293218417491891515927553041 219913813118918636945664781)
    ·
      refine ⟨82467679919594488854624293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219913813118918636945664781 82467679919594488854624293)
      ·
        refine ⟨15462689984923966660242055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82467679919594488854624293 15462689984923966660242055)
        ·
          refine ⟨23194034977385949990363083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462689984923966660242055 23194034977385949990363083)
          ·
            refine ⟨34791052466078924985544625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23194034977385949990363083 34791052466078924985544625)
            ·
              refine ⟨26093289349559193739158469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34791052466078924985544625 26093289349559193739158469)
              ·
                refine ⟨4892491753042348826092213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26093289349559193739158469 4892491753042348826092213)
                ·
                  refine ⟨458671101847720202446145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892491753042348826092213 458671101847720202446145)
                  ·
                    rfl

theorem cell23_8039329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 5].length) (baseStart_8039329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039329 prefixEnd_8039329 := by exact prefixLift 8039329
  have htrace : WordTrace (prefixWord ++ tailWord_8039329) baseStart_8039329 baseEnd_8039329 := by
    simpa [prefixWord, tailWord_8039329, baseEnd_8039329] using wordTrace_append hprefix tailTrace_8039329
  have hstable : (prefixWord ++ tailWord_8039329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039329).length < 2 ^ (prefixWord ++ tailWord_8039329).sum := by decide
  have hdescent : baseEnd_8039329 < baseStart_8039329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039413 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 4]
def baseStart_8039413 : Nat := 118140960795 + 8039413 * 2 ^ 59
def prefixEnd_8039413 : Nat := 4983230072969 + 3 ^ 40 * 8039413 * 2
def baseEnd_8039413 : Nat := 4128083049004459493364919

theorem tailTrace_8039413 : CollatzResearch.WordTrace tailWord_8039413 prefixEnd_8039413 4128083049004459493364919 := by
  unfold tailWord_8039413
  simp only [CollatzResearch.WordTrace]
  refine ⟨293221481223587198273610893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195480987482391465515740595 293221481223587198273610893)
  ·
    refine ⟨109958055458845199352604085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293221481223587198273610893 109958055458845199352604085)
    ·
      refine ⟨10308567699266737439306633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 109958055458845199352604085 10308567699266737439306633)
      ·
        refine ⟨7731425774450053079479975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308567699266737439306633 7731425774450053079479975)
        ·
          refine ⟨11597138661675079619219963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731425774450053079479975 11597138661675079619219963)
          ·
            refine ⟨17395707992512619428829945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597138661675079619219963 17395707992512619428829945)
            ·
              refine ⟨13046780994384464571622459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17395707992512619428829945 13046780994384464571622459)
              ·
                refine ⟨19570171491576696857433689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13046780994384464571622459 19570171491576696857433689)
                ·
                  refine ⟨14677628618682522643075267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19570171491576696857433689 14677628618682522643075267)
                  ·
                    refine ⟨22016442928023783964612901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14677628618682522643075267 22016442928023783964612901)
                    ·
                      refine ⟨4128083049004459493364919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22016442928023783964612901 4128083049004459493364919)
                      ·
                        rfl

theorem cell23_8039413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_8039413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039413 prefixEnd_8039413 := by exact prefixLift 8039413
  have htrace : WordTrace (prefixWord ++ tailWord_8039413) baseStart_8039413 baseEnd_8039413 := by
    simpa [prefixWord, tailWord_8039413, baseEnd_8039413] using wordTrace_append hprefix tailTrace_8039413
  have hstable : (prefixWord ++ tailWord_8039413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039413).length < 2 ^ (prefixWord ++ tailWord_8039413).sum := by decide
  have hdescent : baseEnd_8039413 < baseStart_8039413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039463 : List Nat := [1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_8039463 : Nat := 118140960795 + 8039463 * 2 ^ 59
def prefixEnd_8039463 : Nat := 4983230072969 + 3 ^ 40 * 8039463 * 2
def baseEnd_8039463 : Nat := 4128108723037184297739689

theorem tailTrace_8039463 : CollatzResearch.WordTrace tailWord_8039463 prefixEnd_8039463 4128108723037184297739689 := by
  unfold tailWord_8039463
  simp only [CollatzResearch.WordTrace]
  refine ⟨293223304873406056812931043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195482203248937371208620695 293223304873406056812931043)
  ·
    refine ⟨439834957310109085219396565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293223304873406056812931043 439834957310109085219396565)
    ·
      refine ⟨10308631811955681684829607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 439834957310109085219396565 10308631811955681684829607)
      ·
        refine ⟨15462947717933522527244411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308631811955681684829607 15462947717933522527244411)
        ·
          refine ⟨23194421576900283790866617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462947717933522527244411 23194421576900283790866617)
          ·
            refine ⟨17395816182675212843149963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23194421576900283790866617 17395816182675212843149963)
            ·
              refine ⟨26093724274012819264724945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17395816182675212843149963 26093724274012819264724945)
              ·
                refine ⟨19570293205509614448543709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26093724274012819264724945 19570293205509614448543709)
                ·
                  refine ⟨7338859952066105418203891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19570293205509614448543709 7338859952066105418203891)
                  ·
                    refine ⟨11008289928099158127305837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7338859952066105418203891 11008289928099158127305837)
                    ·
                      refine ⟨4128108723037184297739689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008289928099158127305837 4128108723037184297739689)
                      ·
                        rfl

theorem cell23_8039463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_8039463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039463 prefixEnd_8039463 := by exact prefixLift 8039463
  have htrace : WordTrace (prefixWord ++ tailWord_8039463) baseStart_8039463 baseEnd_8039463 := by
    simpa [prefixWord, tailWord_8039463, baseEnd_8039463] using wordTrace_append hprefix tailTrace_8039463
  have hstable : (prefixWord ++ tailWord_8039463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039463).length < 2 ^ (prefixWord ++ tailWord_8039463).sum := by decide
  have hdescent : baseEnd_8039463 < baseStart_8039463 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039532 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_8039532 : Nat := 118140960795 + 8039532 * 2 ^ 59
def prefixEnd_8039532 : Nat := 4983230072969 + 3 ^ 40 * 8039532 * 2
def baseEnd_8039532 : Nat := 4128144153202344527776871

theorem tailTrace_8039532 : CollatzResearch.WordTrace tailWord_8039532 prefixEnd_8039532 4128144153202344527776871 := by
  unfold tailWord_8039532
  simp only [CollatzResearch.WordTrace]
  refine ⟨146612910755078040798596425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195483881006770721064795233 146612910755078040798596425)
  ·
    refine ⟨109959683066308530598947319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146612910755078040798596425 109959683066308530598947319)
    ·
      refine ⟨164939524599462795898420979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109959683066308530598947319 164939524599462795898420979)
      ·
        refine ⟨247409286899194193847631469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164939524599462795898420979 247409286899194193847631469)
        ·
          refine ⟨92778482587197822692861801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247409286899194193847631469 92778482587197822692861801)
          ·
            refine ⟨69583861940398367019646351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92778482587197822692861801 69583861940398367019646351)
            ·
              refine ⟨104375792910597550529469527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69583861940398367019646351 104375792910597550529469527)
              ·
                refine ⟨156563689365896325794204291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104375792910597550529469527 156563689365896325794204291)
                ·
                  refine ⟨234845534048844488691306437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156563689365896325794204291 234845534048844488691306437)
                  ·
                    refine ⟨44033537634158341629619957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234845534048844488691306437 44033537634158341629619957)
                    ·
                      refine ⟨4128144153202344527776871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44033537634158341629619957 4128144153202344527776871)
                      ·
                        rfl

theorem cell23_8039532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_8039532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039532 prefixEnd_8039532 := by exact prefixLift 8039532
  have htrace : WordTrace (prefixWord ++ tailWord_8039532) baseStart_8039532 baseEnd_8039532 := by
    simpa [prefixWord, tailWord_8039532, baseEnd_8039532] using wordTrace_append hprefix tailTrace_8039532
  have hstable : (prefixWord ++ tailWord_8039532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039532).length < 2 ^ (prefixWord ++ tailWord_8039532).sum := by decide
  have hdescent : baseEnd_8039532 < baseStart_8039532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039552 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_8039552 : Nat := 118140960795 + 8039552 * 2 ^ 59
def prefixEnd_8039552 : Nat := 4983230072969 + 3 ^ 40 * 8039552 * 2
def baseEnd_8039552 : Nat := 1376051474271811483175593

theorem tailTrace_8039552 : CollatzResearch.WordTrace tailWord_8039552 prefixEnd_8039552 1376051474271811483175593 := by
  unfold tailWord_8039552
  simp only [CollatzResearch.WordTrace]
  refine ⟨146613275485041812506460455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195484367313389083341947273 146613275485041812506460455)
  ·
    refine ⟨219919913227562718759690683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146613275485041812506460455 219919913227562718759690683)
    ·
      refine ⟨329879869841344078139536025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219919913227562718759690683 329879869841344078139536025)
      ·
        refine ⟨247409902381008058604652019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329879869841344078139536025 247409902381008058604652019)
        ·
          refine ⟨371114853571512087906978029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247409902381008058604652019 371114853571512087906978029)
          ·
            refine ⟨139168070089317032965116761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371114853571512087906978029 139168070089317032965116761)
            ·
              refine ⟨104376052566987774723837571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139168070089317032965116761 104376052566987774723837571)
              ·
                refine ⟨156564078850481662085756357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104376052566987774723837571 156564078850481662085756357)
                ·
                  refine ⟨29355764784465311641079317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156564078850481662085756357 29355764784465311641079317)
                  ·
                    refine ⟨1376051474271811483175593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29355764784465311641079317 1376051474271811483175593)
                    ·
                      rfl

theorem cell23_8039552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_8039552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039552 prefixEnd_8039552 := by exact prefixLift 8039552
  have htrace : WordTrace (prefixWord ++ tailWord_8039552) baseStart_8039552 baseEnd_8039552 := by
    simpa [prefixWord, tailWord_8039552, baseEnd_8039552] using wordTrace_append hprefix tailTrace_8039552
  have hstable : (prefixWord ++ tailWord_8039552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039552).length < 2 ^ (prefixWord ++ tailWord_8039552).sum := by decide
  have hdescent : baseEnd_8039552 < baseStart_8039552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039570 : List Nat := [3, 2, 3, 1, 1, 2, 4, 1, 2, 1, 3]
def baseStart_8039570 : Nat := 118140960795 + 8039570 * 2 ^ 59
def prefixEnd_8039570 : Nat := 4983230072969 + 3 ^ 40 * 8039570 * 2
def baseEnd_8039570 : Nat := 4128163665467215379101697

theorem tailTrace_8039570 : CollatzResearch.WordTrace tailWord_8039570 prefixEnd_8039570 4128163665467215379101697 := by
  unfold tailWord_8039570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73306801871004603521769041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195484804989345609391384109 73306801871004603521769041)
  ·
    refine ⟨54980101403253452641326781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73306801871004603521769041 54980101403253452641326781)
    ·
      refine ⟨20617538026220044740497543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54980101403253452641326781 20617538026220044740497543)
      ·
        refine ⟨30926307039330067110746315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20617538026220044740497543 30926307039330067110746315)
        ·
          refine ⟨46389460558995100666119473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30926307039330067110746315 46389460558995100666119473)
          ·
            refine ⟨34792095419246325499589605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46389460558995100666119473 34792095419246325499589605)
            ·
              refine ⟨6523517891108686031173051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34792095419246325499589605 6523517891108686031173051)
              ·
                refine ⟨9785276836663029046759577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523517891108686031173051 9785276836663029046759577)
                ·
                  refine ⟨7338957627497271785069683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785276836663029046759577 7338957627497271785069683)
                  ·
                    refine ⟨11008436441245907677604525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7338957627497271785069683 11008436441245907677604525)
                    ·
                      refine ⟨4128163665467215379101697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008436441245907677604525 4128163665467215379101697)
                      ·
                        rfl

theorem cell23_8039570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_8039570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039570 prefixEnd_8039570 := by exact prefixLift 8039570
  have htrace : WordTrace (prefixWord ++ tailWord_8039570) baseStart_8039570 baseEnd_8039570 := by
    simpa [prefixWord, tailWord_8039570, baseEnd_8039570] using wordTrace_append hprefix tailTrace_8039570
  have hstable : (prefixWord ++ tailWord_8039570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039570).length < 2 ^ (prefixWord ++ tailWord_8039570).sum := by decide
  have hdescent : baseEnd_8039570 < baseStart_8039570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039580 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_8039580 : Nat := 118140960795 + 8039580 * 2 ^ 59
def prefixEnd_8039580 : Nat := 4983230072969 + 3 ^ 40 * 8039580 * 2
def baseEnd_8039580 : Nat := 4128168800273760339976651

theorem tailTrace_8039580 : CollatzResearch.WordTrace tailWord_8039580 prefixEnd_8039580 4128168800273760339976651 := by
  unfold tailWord_8039580
  simp only [CollatzResearch.WordTrace]
  refine ⟨146613786106991092897470097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195485048142654790529960129 146613786106991092897470097)
  ·
    refine ⟨109960339580243319673102573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146613786106991092897470097 109960339580243319673102573)
    ·
      refine ⟨41235127342591244877413465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109960339580243319673102573 41235127342591244877413465)
      ·
        refine ⟨30926345506943433658060099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41235127342591244877413465 30926345506943433658060099)
        ·
          refine ⟨46389518260415150487090149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30926345506943433658060099 46389518260415150487090149)
          ·
            refine ⟨8698034673827840716329403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46389518260415150487090149 8698034673827840716329403)
            ·
              refine ⟨13047052010741761074494105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698034673827840716329403 13047052010741761074494105)
              ·
                refine ⟨9785289008056320805870579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13047052010741761074494105 9785289008056320805870579)
                ·
                  refine ⟨14677933512084481208805869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785289008056320805870579 14677933512084481208805869)
                  ·
                    refine ⟨5504225067031680453302201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14677933512084481208805869 5504225067031680453302201)
                    ·
                      refine ⟨4128168800273760339976651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504225067031680453302201 4128168800273760339976651)
                      ·
                        rfl

theorem cell23_8039580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_8039580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039580 prefixEnd_8039580 := by exact prefixLift 8039580
  have htrace : WordTrace (prefixWord ++ tailWord_8039580) baseStart_8039580 baseEnd_8039580 := by
    simpa [prefixWord, tailWord_8039580, baseEnd_8039580] using wordTrace_append hprefix tailTrace_8039580
  have hstable : (prefixWord ++ tailWord_8039580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039580).length < 2 ^ (prefixWord ++ tailWord_8039580).sum := by decide
  have hdescent : baseEnd_8039580 < baseStart_8039580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039597 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_8039597 : Nat := 118140960795 + 8039597 * 2 ^ 59
def prefixEnd_8039597 : Nat := 4983230072969 + 3 ^ 40 * 8039597 * 2
def baseEnd_8039597 : Nat := 4128177529444886773464073

theorem tailTrace_8039597 : CollatzResearch.WordTrace tailWord_8039597 prefixEnd_8039597 4128177529444886773464073 := by
  unfold tailWord_8039597
  simp only [CollatzResearch.WordTrace]
  refine ⟨293228192254920597698309045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195485461503280398465539363 293228192254920597698309045)
  ·
    refine ⟨27490143023898806034216473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293228192254920597698309045 27490143023898806034216473)
    ·
      refine ⟨20617607267924104525662355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27490143023898806034216473 20617607267924104525662355)
      ·
        refine ⟨30926410901886156788493533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20617607267924104525662355 30926410901886156788493533)
        ·
          refine ⟨11597404088207308795685075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30926410901886156788493533 11597404088207308795685075)
          ·
            refine ⟨17396106132310963193527613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597404088207308795685075 17396106132310963193527613)
            ·
              refine ⟨6523539799616611197572855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17396106132310963193527613 6523539799616611197572855)
              ·
                refine ⟨9785309699424916796359283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523539799616611197572855 9785309699424916796359283)
                ·
                  refine ⟨14677964549137375194538925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785309699424916796359283 14677964549137375194538925)
                  ·
                    refine ⟨5504236705926515697952097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14677964549137375194538925 5504236705926515697952097)
                    ·
                      refine ⟨4128177529444886773464073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504236705926515697952097 4128177529444886773464073)
                      ·
                        rfl

theorem cell23_8039597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_8039597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039597 prefixEnd_8039597 := by exact prefixLift 8039597
  have htrace : WordTrace (prefixWord ++ tailWord_8039597) baseStart_8039597 baseEnd_8039597 := by
    simpa [prefixWord, tailWord_8039597, baseEnd_8039597] using wordTrace_append hprefix tailTrace_8039597
  have hstable : (prefixWord ++ tailWord_8039597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039597).length < 2 ^ (prefixWord ++ tailWord_8039597).sum := by decide
  have hdescent : baseEnd_8039597 < baseStart_8039597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039626 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3]
def baseStart_8039626 : Nat := 118140960795 + 8039626 * 2 ^ 59
def prefixEnd_8039626 : Nat := 4983230072969 + 3 ^ 40 * 8039626 * 2
def baseEnd_8039626 : Nat := 4128192420383867160001439

theorem tailTrace_8039626 : CollatzResearch.WordTrace tailWord_8039626 prefixEnd_8039626 4128192420383867160001439 := by
  unfold tailWord_8039626
  simp only [CollatzResearch.WordTrace]
  refine ⟨73307312492953883912778683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195486166647877023767409821 73307312492953883912778683)
  ·
    refine ⟨109960968739430825869168025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73307312492953883912778683 109960968739430825869168025)
    ·
      refine ⟨82470726554573119401876019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109960968739430825869168025 82470726554573119401876019)
      ·
        refine ⟨123706089831859679102814029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82470726554573119401876019 123706089831859679102814029)
        ·
          refine ⟨46389783686947379663555261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123706089831859679102814029 46389783686947379663555261)
          ·
            refine ⟨17396168882605267373833223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46389783686947379663555261 17396168882605267373833223)
            ·
              refine ⟨26094253323907901060749835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17396168882605267373833223 26094253323907901060749835)
              ·
                refine ⟨39141379985861851591124753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26094253323907901060749835 39141379985861851591124753)
                ·
                  refine ⟨29356034989396388693343565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39141379985861851591124753 29356034989396388693343565)
                  ·
                    refine ⟨11008513121023645760003837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29356034989396388693343565 11008513121023645760003837)
                    ·
                      refine ⟨4128192420383867160001439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008513121023645760003837 4128192420383867160001439)
                      ·
                        rfl

theorem cell23_8039626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_8039626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039626 prefixEnd_8039626 := by exact prefixLift 8039626
  have htrace : WordTrace (prefixWord ++ tailWord_8039626) baseStart_8039626 baseEnd_8039626 := by
    simpa [prefixWord, tailWord_8039626, baseEnd_8039626] using wordTrace_append hprefix tailTrace_8039626
  have hstable : (prefixWord ++ tailWord_8039626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039626).length < 2 ^ (prefixWord ++ tailWord_8039626).sum := by decide
  have hdescent : baseEnd_8039626 < baseStart_8039626 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039749 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_8039749 : Nat := 118140960795 + 8039749 * 2 ^ 59
def prefixEnd_8039749 : Nat := 4983230072969 + 3 ^ 40 * 8039749 * 2
def baseEnd_8039749 : Nat := 1376085192834790059587791

theorem tailTrace_8039749 : CollatzResearch.WordTrace tailWord_8039749 prefixEnd_8039749 1376085192834790059587791 := by
  unfold tailWord_8039749
  simp only [CollatzResearch.WordTrace]
  refine ⟨293233736150369927657842301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195489157433579951771894867 293233736150369927657842301)
  ·
    refine ⟨109962651056388722871690863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293233736150369927657842301 109962651056388722871690863)
    ·
      refine ⟨164943976584583084307536295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109962651056388722871690863 164943976584583084307536295)
      ·
        refine ⟨247415964876874626461304443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164943976584583084307536295 247415964876874626461304443)
        ·
          refine ⟨371123947315311939691956665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247415964876874626461304443 371123947315311939691956665)
          ·
            refine ⟨278342960486483954768967499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371123947315311939691956665 278342960486483954768967499)
            ·
              refine ⟨417514440729725932153451249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278342960486483954768967499 417514440729725932153451249)
              ·
                refine ⟨313135830547294449115088437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417514440729725932153451249 313135830547294449115088437)
                ·
                  refine ⟨29356484113808854604539541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313135830547294449115088437 29356484113808854604539541)
                  ·
                    refine ⟨1376085192834790059587791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29356484113808854604539541 1376085192834790059587791)
                    ·
                      rfl

theorem cell23_8039749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_8039749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039749 prefixEnd_8039749 := by exact prefixLift 8039749
  have htrace : WordTrace (prefixWord ++ tailWord_8039749) baseStart_8039749 baseEnd_8039749 := by
    simpa [prefixWord, tailWord_8039749, baseEnd_8039749] using wordTrace_append hprefix tailTrace_8039749
  have hstable : (prefixWord ++ tailWord_8039749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039749).length < 2 ^ (prefixWord ++ tailWord_8039749).sum := by decide
  have hdescent : baseEnd_8039749 < baseStart_8039749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039779 : List Nat := [1, 1, 1, 5, 2, 13]
def baseStart_8039779 : Nat := 118140960795 + 8039779 * 2 ^ 59
def prefixEnd_8039779 : Nat := 4983230072969 + 3 ^ 40 * 8039779 * 2
def baseEnd_8039779 : Nat := 16988769477053518771145

theorem tailTrace_8039779 : CollatzResearch.WordTrace tailWord_8039779 prefixEnd_8039779 16988769477053518771145 := by
  unfold tailWord_8039779
  simp only [CollatzResearch.WordTrace]
  refine ⟨293234830340261242781434391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195489886893507495187622927 293234830340261242781434391)
  ·
    refine ⟨439852245510391864172151587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293234830340261242781434391 439852245510391864172151587)
    ·
      refine ⟨659778368265587796258227381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439852245510391864172151587 659778368265587796258227381)
      ·
        refine ⟨61854222024898855899208817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 659778368265587796258227381 61854222024898855899208817)
        ·
          refine ⟨46390666518674141924406613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61854222024898855899208817 46390666518674141924406613)
          ·
            refine ⟨16988769477053518771145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 46390666518674141924406613 16988769477053518771145)
            ·
              rfl

theorem cell23_8039779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 13].length) (baseStart_8039779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039779 prefixEnd_8039779 := by exact prefixLift 8039779
  have htrace : WordTrace (prefixWord ++ tailWord_8039779) baseStart_8039779 baseEnd_8039779 := by
    simpa [prefixWord, tailWord_8039779, baseEnd_8039779] using wordTrace_append hprefix tailTrace_8039779
  have hstable : (prefixWord ++ tailWord_8039779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039779).length < 2 ^ (prefixWord ++ tailWord_8039779).sum := by decide
  have hdescent : baseEnd_8039779 < baseStart_8039779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039857 : List Nat := [1, 2, 2, 4, 1, 1, 5, 1, 2, 1, 3]
def baseStart_8039857 : Nat := 118140960795 + 8039857 * 2 ^ 59
def prefixEnd_8039857 : Nat := 4983230072969 + 3 ^ 40 * 8039857 * 2
def baseEnd_8039857 : Nat := 4128311034415055756212877

theorem tailTrace_8039857 : CollatzResearch.WordTrace tailWord_8039857 prefixEnd_8039857 4128311034415055756212877 := by
  unfold tailWord_8039857
  simp only [CollatzResearch.WordTrace]
  refine ⟨293237675233978662102773825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195491783489319108068515883 293237675233978662102773825)
  ·
    refine ⟨219928256425483996577080369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293237675233978662102773825 219928256425483996577080369)
    ·
      refine ⟨164946192319112997432810277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219928256425483996577080369 164946192319112997432810277)
      ·
        refine ⟨30927411059833687018651927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164946192319112997432810277 30927411059833687018651927)
        ·
          refine ⟨46391116589750530527977891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30927411059833687018651927 46391116589750530527977891)
          ·
            refine ⟨69586674884625795791966837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46391116589750530527977891 69586674884625795791966837)
            ·
              refine ⟨6523750770433668355496891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69586674884625795791966837 6523750770433668355496891)
              ·
                refine ⟨9785626155650502533245337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523750770433668355496891 9785626155650502533245337)
                ·
                  refine ⟨7339219616737876899934003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785626155650502533245337 7339219616737876899934003)
                  ·
                    refine ⟨11008829425106815349901005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339219616737876899934003 11008829425106815349901005)
                    ·
                      refine ⟨4128311034415055756212877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008829425106815349901005 4128311034415055756212877)
                      ·
                        rfl

theorem cell23_8039857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_8039857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039857 prefixEnd_8039857 := by exact prefixLift 8039857
  have htrace : WordTrace (prefixWord ++ tailWord_8039857) baseStart_8039857 baseEnd_8039857 := by
    simpa [prefixWord, tailWord_8039857, baseEnd_8039857] using wordTrace_append hprefix tailTrace_8039857
  have hstable : (prefixWord ++ tailWord_8039857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039857).length < 2 ^ (prefixWord ++ tailWord_8039857).sum := by decide
  have hdescent : baseEnd_8039857 < baseStart_8039857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039880 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_8039880 : Nat := 118140960795 + 8039880 * 2 ^ 59
def prefixEnd_8039880 : Nat := 4983230072969 + 3 ^ 40 * 8039880 * 2
def baseEnd_8039880 : Nat := 4128322844470109166225271

theorem tailTrace_8039880 : CollatzResearch.WordTrace tailWord_8039880 prefixEnd_8039880 4128322844470109166225271 := by
  unfold tailWord_8039880
  simp only [CollatzResearch.WordTrace]
  refine ⟨146619257056447668515430547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195492342741930224687240729 146619257056447668515430547)
  ·
    refine ⟨219928885584671502773145821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146619257056447668515430547 219928885584671502773145821)
    ·
      refine ⟨82473332094251813539929683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219928885584671502773145821 82473332094251813539929683)
      ·
        refine ⟨123709998141377720309894525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82473332094251813539929683 123709998141377720309894525)
        ·
          refine ⟨46391249303016645116210447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123709998141377720309894525 46391249303016645116210447)
          ·
            refine ⟨69586873954524967674315671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46391249303016645116210447 69586873954524967674315671)
            ·
              refine ⟨104380310931787451511473507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69586873954524967674315671 104380310931787451511473507)
              ·
                refine ⟨156570466397681177267210261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104380310931787451511473507 156570466397681177267210261)
                ·
                  refine ⟨7339240612391305184400481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156570466397681177267210261 7339240612391305184400481)
                  ·
                    refine ⟨5504430459293478888300361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339240612391305184400481 5504430459293478888300361)
                    ·
                      refine ⟨4128322844470109166225271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504430459293478888300361 4128322844470109166225271)
                      ·
                        rfl

theorem cell23_8039880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_8039880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039880 prefixEnd_8039880 := by exact prefixLift 8039880
  have htrace : WordTrace (prefixWord ++ tailWord_8039880) baseStart_8039880 baseEnd_8039880 := by
    simpa [prefixWord, tailWord_8039880, baseEnd_8039880] using wordTrace_append hprefix tailTrace_8039880
  have hstable : (prefixWord ++ tailWord_8039880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039880).length < 2 ^ (prefixWord ++ tailWord_8039880).sum := by decide
  have hdescent : baseEnd_8039880 < baseStart_8039880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039886 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 9]
def baseStart_8039886 : Nat := 118140960795 + 8039886 * 2 ^ 59
def prefixEnd_8039886 : Nat := 4983230072969 + 3 ^ 40 * 8039886 * 2
def baseEnd_8039886 : Nat := 458702880594892904750027

theorem tailTrace_8039886 : CollatzResearch.WordTrace tailWord_8039886 prefixEnd_8039886 458702880594892904750027 := by
  unfold tailWord_8039886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654841618859200006947439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195492488633915733370386341 36654841618859200006947439)
  ·
    refine ⟨54982262428288800010421159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654841618859200006947439 54982262428288800010421159)
    ·
      refine ⟨82473393642433200015631739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54982262428288800010421159 82473393642433200015631739)
      ·
        refine ⟨123710090463649800023447609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82473393642433200015631739 123710090463649800023447609)
        ·
          refine ⟨92782567847737350017585707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123710090463649800023447609 92782567847737350017585707)
          ·
            refine ⟨139173851771606025026378561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92782567847737350017585707 139173851771606025026378561)
            ·
              refine ⟨104380388828704518769783921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139173851771606025026378561 104380388828704518769783921)
              ·
                refine ⟨78285291621528389077337941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104380388828704518769783921 78285291621528389077337941)
                ·
                  refine ⟨458702880594892904750027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78285291621528389077337941 458702880594892904750027)
                  ·
                    rfl

theorem cell23_8039886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 9].length) (baseStart_8039886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039886 prefixEnd_8039886 := by exact prefixLift 8039886
  have htrace : WordTrace (prefixWord ++ tailWord_8039886) baseStart_8039886 baseEnd_8039886 := by
    simpa [prefixWord, tailWord_8039886, baseEnd_8039886] using wordTrace_append hprefix tailTrace_8039886
  have hstable : (prefixWord ++ tailWord_8039886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039886).length < 2 ^ (prefixWord ++ tailWord_8039886).sum := by decide
  have hdescent : baseEnd_8039886 < baseStart_8039886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039914 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2]
def baseStart_8039914 : Nat := 118140960795 + 8039914 * 2 ^ 59
def prefixEnd_8039914 : Nat := 4983230072969 + 3 ^ 40 * 8039914 * 2
def baseEnd_8039914 : Nat := 4128340302812362033200115

theorem tailTrace_8039914 : CollatzResearch.WordTrace tailWord_8039914 prefixEnd_8039914 4128340302812362033200115 := by
  unfold tailWord_8039914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73309938548693040209399699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195493169463181440558399197 73309938548693040209399699)
  ·
    refine ⟨109964907823039560314099549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73309938548693040209399699 109964907823039560314099549)
    ·
      refine ⟨41236840433639835117787331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109964907823039560314099549 41236840433639835117787331)
      ·
        refine ⟨61855260650459752676680997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41236840433639835117787331 61855260650459752676680997)
        ·
          refine ⟨11597861371961203626877687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61855260650459752676680997 11597861371961203626877687)
          ·
            refine ⟨17396792057941805440316531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11597861371961203626877687 17396792057941805440316531)
            ·
              refine ⟨26095188086912708160474797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17396792057941805440316531 26095188086912708160474797)
              ·
                refine ⟨9785695532592265560178049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26095188086912708160474797 9785695532592265560178049)
                ·
                  refine ⟨7339271649444199170133537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785695532592265560178049 7339271649444199170133537)
                  ·
                    refine ⟨5504453737083149377600153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339271649444199170133537 5504453737083149377600153)
                    ·
                      refine ⟨4128340302812362033200115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504453737083149377600153 4128340302812362033200115)
                      ·
                        rfl

theorem cell23_8039914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_8039914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039914 prefixEnd_8039914 := by exact prefixLift 8039914
  have htrace : WordTrace (prefixWord ++ tailWord_8039914) baseStart_8039914 baseEnd_8039914 := by
    simpa [prefixWord, tailWord_8039914, baseEnd_8039914] using wordTrace_append hprefix tailTrace_8039914
  have hstable : (prefixWord ++ tailWord_8039914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039914).length < 2 ^ (prefixWord ++ tailWord_8039914).sum := by decide
  have hdescent : baseEnd_8039914 < baseStart_8039914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039916 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_8039916 : Nat := 118140960795 + 8039916 * 2 ^ 59
def prefixEnd_8039916 : Nat := 4983230072969 + 3 ^ 40 * 8039916 * 2
def baseEnd_8039916 : Nat := 1376113776591223675125035

theorem tailTrace_8039916 : CollatzResearch.WordTrace tailWord_8039916 prefixEnd_8039916 1376113776591223675125035 := by
  unfold tailWord_8039916
  simp only [CollatzResearch.WordTrace]
  refine ⟨146619913570382457589585801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195493218093843276786114401 146619913570382457589585801)
  ·
    refine ⟨109964935177786843192189351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146619913570382457589585801 109964935177786843192189351)
    ·
      refine ⟨164947402766680264788284027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109964935177786843192189351 164947402766680264788284027)
      ·
        refine ⟨247421104150020397182426041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164947402766680264788284027 247421104150020397182426041)
        ·
          refine ⟨185565828112515297886819531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247421104150020397182426041 185565828112515297886819531)
          ·
            refine ⟨278348742168772946830229297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185565828112515297886819531 278348742168772946830229297)
            ·
              refine ⟨208761556626579710122671973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278348742168772946830229297 208761556626579710122671973)
              ·
                refine ⟨39142791867483695648000995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208761556626579710122671973 39142791867483695648000995)
                ·
                  refine ⟨58714187801225543472001493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39142791867483695648000995 58714187801225543472001493)
                  ·
                    refine ⟨1376113776591223675125035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58714187801225543472001493 1376113776591223675125035)
                    ·
                      rfl

theorem cell23_8039916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_8039916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039916 prefixEnd_8039916 := by exact prefixLift 8039916
  have htrace : WordTrace (prefixWord ++ tailWord_8039916) baseStart_8039916 baseEnd_8039916 := by
    simpa [prefixWord, tailWord_8039916, baseEnd_8039916] using wordTrace_append hprefix tailTrace_8039916
  have hstable : (prefixWord ++ tailWord_8039916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039916).length < 2 ^ (prefixWord ++ tailWord_8039916).sum := by decide
  have hdescent : baseEnd_8039916 < baseStart_8039916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039923 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 4, 5, 2]
def baseStart_8039923 : Nat := 118140960795 + 8039923 * 2 ^ 59
def prefixEnd_8039923 : Nat := 4983230072969 + 3 ^ 40 * 8039923 * 2
def baseEnd_8039923 : Nat := 4128344924138252497987573

theorem tailTrace_8039923 : CollatzResearch.WordTrace tailWord_8039923 prefixEnd_8039923 4128344924138252497987573 := by
  unfold tailWord_8039923
  simp only [CollatzResearch.WordTrace]
  refine ⟨293240082451739555374676423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195493388301159703583117615 293240082451739555374676423)
  ·
    refine ⟨439860123677609333062014635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293240082451739555374676423 439860123677609333062014635)
    ·
      refine ⟨659790185516413999593021953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439860123677609333062014635 659790185516413999593021953)
      ·
        refine ⟨494842639137310499694766465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659790185516413999593021953 494842639137310499694766465)
        ·
          refine ⟨371131979352982874771074849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494842639137310499694766465 371131979352982874771074849)
          ·
            refine ⟨278348984514737156078306137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371131979352982874771074849 278348984514737156078306137)
            ·
              refine ⟨208761738386052867058729603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278348984514737156078306137 208761738386052867058729603)
              ·
                refine ⟨313142607579079300588094405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208761738386052867058729603 313142607579079300588094405)
                ·
                  refine ⟨58714238921077368860267701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313142607579079300588094405 58714238921077368860267701)
                  ·
                    refine ⟨5504459898851003330650097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58714238921077368860267701 5504459898851003330650097)
                    ·
                      refine ⟨4128344924138252497987573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504459898851003330650097 4128344924138252497987573)
                      ·
                        rfl

theorem cell23_8039923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 5, 2].length) (baseStart_8039923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039923 prefixEnd_8039923 := by exact prefixLift 8039923
  have htrace : WordTrace (prefixWord ++ tailWord_8039923) baseStart_8039923 baseEnd_8039923 := by
    simpa [prefixWord, tailWord_8039923, baseEnd_8039923] using wordTrace_append hprefix tailTrace_8039923
  have hstable : (prefixWord ++ tailWord_8039923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039923).length < 2 ^ (prefixWord ++ tailWord_8039923).sum := by decide
  have hdescent : baseEnd_8039923 < baseStart_8039923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039933 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_8039933 : Nat := 118140960795 + 8039933 * 2 ^ 59
def prefixEnd_8039933 : Nat := 4983230072969 + 3 ^ 40 * 8039933 * 2
def baseEnd_8039933 : Nat := 1376116686314932486287509

theorem tailTrace_8039933 : CollatzResearch.WordTrace tailWord_8039933 prefixEnd_8039933 1376116686314932486287509 := by
  unfold tailWord_8039933
  simp only [CollatzResearch.WordTrace]
  refine ⟨293240447181703327082540453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195493631454468884721693635 293240447181703327082540453)
  ·
    refine ⟨54982583846569373827976335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293240447181703327082540453 54982583846569373827976335)
    ·
      refine ⟨82473875769854060741964503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54982583846569373827976335 82473875769854060741964503)
      ·
        refine ⟨123710813654781091112946755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82473875769854060741964503 123710813654781091112946755)
        ·
          refine ⟨185566220482171636669420133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123710813654781091112946755 185566220482171636669420133)
          ·
            refine ⟨34793666340407181875516275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185566220482171636669420133 34793666340407181875516275)
            ·
              refine ⟨52190499510610772813274413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34793666340407181875516275 52190499510610772813274413)
              ·
                refine ⟨19571437316479039804977905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52190499510610772813274413 19571437316479039804977905)
                ·
                  refine ⟨14678577987359279853733429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19571437316479039804977905 14678577987359279853733429)
                  ·
                    refine ⟨1376116686314932486287509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14678577987359279853733429 1376116686314932486287509)
                    ·
                      rfl

theorem cell23_8039933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_8039933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039933 prefixEnd_8039933 := by exact prefixLift 8039933
  have htrace : WordTrace (prefixWord ++ tailWord_8039933) baseStart_8039933 baseEnd_8039933 := by
    simpa [prefixWord, tailWord_8039933, baseEnd_8039933] using wordTrace_append hprefix tailTrace_8039933
  have hstable : (prefixWord ++ tailWord_8039933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039933).length < 2 ^ (prefixWord ++ tailWord_8039933).sum := by decide
  have hdescent : baseEnd_8039933 < baseStart_8039933 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039943 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_8039943 : Nat := 118140960795 + 8039943 * 2 ^ 59
def prefixEnd_8039943 : Nat := 4983230072969 + 3 ^ 40 * 8039943 * 2
def baseEnd_8039943 : Nat := 4128355193751342419737481

theorem tailTrace_8039943 : CollatzResearch.WordTrace tailWord_8039943 prefixEnd_8039943 4128355193751342419737481 := by
  unfold tailWord_8039943
  simp only [CollatzResearch.WordTrace]
  refine ⟨293240811911667098790404483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195493874607778065860269655 293240811911667098790404483)
  ·
    refine ⟨439861217867500648185606725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293240811911667098790404483 439861217867500648185606725)
    ·
      refine ⟨82473978350156371534801261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439861217867500648185606725 82473978350156371534801261)
      ·
        refine ⟨30927741881308639325550473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82473978350156371534801261 30927741881308639325550473)
        ·
          refine ⟨23195806410981479494162855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30927741881308639325550473 23195806410981479494162855)
          ·
            refine ⟨34793709616472219241244283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23195806410981479494162855 34793709616472219241244283)
            ·
              refine ⟨52190564424708328861866425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34793709616472219241244283 52190564424708328861866425)
              ·
                refine ⟨39142923318531246646399819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52190564424708328861866425 39142923318531246646399819)
                ·
                  refine ⟨58714384977796869969599729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39142923318531246646399819 58714384977796869969599729)
                  ·
                    refine ⟨44035788733347652477199797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58714384977796869969599729 44035788733347652477199797)
                    ·
                      refine ⟨4128355193751342419737481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44035788733347652477199797 4128355193751342419737481)
                      ·
                        rfl

theorem cell23_8039943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_8039943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039943 prefixEnd_8039943 := by exact prefixLift 8039943
  have htrace : WordTrace (prefixWord ++ tailWord_8039943) baseStart_8039943 baseEnd_8039943 := by
    simpa [prefixWord, tailWord_8039943, baseEnd_8039943] using wordTrace_append hprefix tailTrace_8039943
  have hstable : (prefixWord ++ tailWord_8039943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039943).length < 2 ^ (prefixWord ++ tailWord_8039943).sum := by decide
  have hdescent : baseEnd_8039943 < baseStart_8039943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039953 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_8039953 : Nat := 118140960795 + 8039953 * 2 ^ 59
def prefixEnd_8039953 : Nat := 4983230072969 + 3 ^ 40 * 8039953 * 2
def baseEnd_8039953 : Nat := 4128360328557887380612435

theorem tailTrace_8039953 : CollatzResearch.WordTrace tailWord_8039953 prefixEnd_8039953 4128360328557887380612435 := by
  unfold tailWord_8039953
  simp only [CollatzResearch.WordTrace]
  refine ⟨293241176641630870498268513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195494117761087246998845675 293241176641630870498268513)
  ·
    refine ⟨219930882481223152873701385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293241176641630870498268513 219930882481223152873701385)
    ·
      refine ⟨164948161860917364655276039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219930882481223152873701385 164948161860917364655276039)
      ·
        refine ⟨247422242791376046982914059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164948161860917364655276039 247422242791376046982914059)
        ·
          refine ⟨371133364187064070474371089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247422242791376046982914059 371133364187064070474371089)
          ·
            refine ⟨278350023140298052855778317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371133364187064070474371089 278350023140298052855778317)
            ·
              refine ⟨104381258677611769820916869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278350023140298052855778317 104381258677611769820916869)
              ·
                refine ⟨19571486002052206841421913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104381258677611769820916869 19571486002052206841421913)
                ·
                  refine ⟨14678614501539155131066435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19571486002052206841421913 14678614501539155131066435)
                  ·
                    refine ⟨22017921752308732696599653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14678614501539155131066435 22017921752308732696599653)
                    ·
                      refine ⟨4128360328557887380612435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22017921752308732696599653 4128360328557887380612435)
                      ·
                        rfl

theorem cell23_8039953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_8039953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039953 prefixEnd_8039953 := by exact prefixLift 8039953
  have htrace : WordTrace (prefixWord ++ tailWord_8039953) baseStart_8039953 baseEnd_8039953 := by
    simpa [prefixWord, tailWord_8039953, baseEnd_8039953] using wordTrace_append hprefix tailTrace_8039953
  have hstable : (prefixWord ++ tailWord_8039953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039953).length < 2 ^ (prefixWord ++ tailWord_8039953).sum := by decide
  have hdescent : baseEnd_8039953 < baseStart_8039953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039970 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 1, 6, 2]
def baseStart_8039970 : Nat := 118140960795 + 8039970 * 2 ^ 59
def prefixEnd_8039970 : Nat := 4983230072969 + 3 ^ 40 * 8039970 * 2
def baseEnd_8039970 : Nat := 4128369057729013814099857

theorem tailTrace_8039970 : CollatzResearch.WordTrace tailWord_8039970 prefixEnd_8039970 4128369057729013814099857 := by
  unfold tailWord_8039970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73310449170642320600409341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195494531121712854934424909 73310449170642320600409341)
  ·
    refine ⟨27491418438990870225153503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73310449170642320600409341 27491418438990870225153503)
    ·
      refine ⟨41237127658486305337730255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27491418438990870225153503 41237127658486305337730255)
      ·
        refine ⟨61855691487729458006595383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41237127658486305337730255 61855691487729458006595383)
        ·
          refine ⟨92783537231594187009893075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61855691487729458006595383 92783537231594187009893075)
          ·
            refine ⟨139175305847391280514839613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92783537231594187009893075 139175305847391280514839613)
            ·
              refine ⟨52190739692771730193064855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139175305847391280514839613 52190739692771730193064855)
              ·
                refine ⟨78286109539157595289597283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52190739692771730193064855 78286109539157595289597283)
                ·
                  refine ⟨117429164308736392934395925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78286109539157595289597283 117429164308736392934395925)
                  ·
                    refine ⟨5504492076972018418799809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117429164308736392934395925 5504492076972018418799809)
                    ·
                      refine ⟨4128369057729013814099857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504492076972018418799809 4128369057729013814099857)
                      ·
                        rfl

theorem cell23_8039970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_8039970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039970 prefixEnd_8039970 := by exact prefixLift 8039970
  have htrace : WordTrace (prefixWord ++ tailWord_8039970) baseStart_8039970 baseEnd_8039970 := by
    simpa [prefixWord, tailWord_8039970, baseEnd_8039970] using wordTrace_append hprefix tailTrace_8039970
  have hstable : (prefixWord ++ tailWord_8039970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039970).length < 2 ^ (prefixWord ++ tailWord_8039970).sum := by decide
  have hdescent : baseEnd_8039970 < baseStart_8039970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8039973 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 3]
def baseStart_8039973 : Nat := 118140960795 + 8039973 * 2 ^ 59
def prefixEnd_8039973 : Nat := 4983230072969 + 3 ^ 40 * 8039973 * 2
def baseEnd_8039973 : Nat := 4128370598170977302362343

theorem tailTrace_8039973 : CollatzResearch.WordTrace tailWord_8039973 prefixEnd_8039973 4128370598170977302362343 := by
  unfold tailWord_8039973
  simp only [CollatzResearch.WordTrace]
  refine ⟨293241906101558413913996573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195494604067705609275997715 293241906101558413913996573)
  ·
    refine ⟨109965714788084405217748715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293241906101558413913996573 109965714788084405217748715)
    ·
      refine ⟨164948572182126607826623073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109965714788084405217748715 164948572182126607826623073)
      ·
        refine ⟨123711429136594955869967305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164948572182126607826623073 123711429136594955869967305)
        ·
          refine ⟨92783571852446216902475479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123711429136594955869967305 92783571852446216902475479)
          ·
            refine ⟨139175357778669325353713219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92783571852446216902475479 139175357778669325353713219)
            ·
              refine ⟨208763036668003988030569829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139175357778669325353713219 208763036668003988030569829)
              ·
                refine ⟨39143069375250747755731843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208763036668003988030569829 39143069375250747755731843)
                ·
                  refine ⟨58714604062876121633597765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39143069375250747755731843 58714604062876121633597765)
                  ·
                    refine ⟨11008988261789272806299581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58714604062876121633597765 11008988261789272806299581)
                    ·
                      refine ⟨4128370598170977302362343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11008988261789272806299581 4128370598170977302362343)
                      ·
                        rfl

theorem cell23_8039973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_8039973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8039973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8039973 prefixEnd_8039973 := by exact prefixLift 8039973
  have htrace : WordTrace (prefixWord ++ tailWord_8039973) baseStart_8039973 baseEnd_8039973 := by
    simpa [prefixWord, tailWord_8039973, baseEnd_8039973] using wordTrace_append hprefix tailTrace_8039973
  have hstable : (prefixWord ++ tailWord_8039973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8039973).length < 2 ^ (prefixWord ++ tailWord_8039973).sum := by decide
  have hdescent : baseEnd_8039973 < baseStart_8039973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8039973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040037 : List Nat := [1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 3]
def baseStart_8040037 : Nat := 118140960795 + 8040037 * 2 ^ 59
def prefixEnd_8040037 : Nat := 4983230072969 + 3 ^ 40 * 8040037 * 2
def baseEnd_8040037 : Nat := 4128403460932865051962049

theorem tailTrace_8040037 : CollatzResearch.WordTrace tailWord_8040037 prefixEnd_8040037 4128403460932865051962049 := by
  unfold tailWord_8040037
  simp only [CollatzResearch.WordTrace]
  refine ⟨293244240373326552844326365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195496160248884368562884243 293244240373326552844326365)
  ·
    refine ⟨109966590139997457316622387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293244240373326552844326365 109966590139997457316622387)
    ·
      refine ⟨164949885209996185974933581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109966590139997457316622387 164949885209996185974933581)
      ·
        refine ⟨61856206953748569740600093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164949885209996185974933581 61856206953748569740600093)
        ·
          refine ⟨23196077607655713652725035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61856206953748569740600093 23196077607655713652725035)
          ·
            refine ⟨34794116411483570479087553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23196077607655713652725035 34794116411483570479087553)
            ·
              refine ⟨26095587308612677859315665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34794116411483570479087553 26095587308612677859315665)
              ·
                refine ⟨19571690481459508394486749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26095587308612677859315665 19571690481459508394486749)
                ·
                  refine ⟨7339383930547315647932531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19571690481459508394486749 7339383930547315647932531)
                  ·
                    refine ⟨11009075895820973471898797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339383930547315647932531 11009075895820973471898797)
                    ·
                      refine ⟨4128403460932865051962049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009075895820973471898797 4128403460932865051962049)
                      ·
                        rfl

theorem cell23_8040037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_8040037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040037 prefixEnd_8040037 := by exact prefixLift 8040037
  have htrace : WordTrace (prefixWord ++ tailWord_8040037) baseStart_8040037 baseEnd_8040037 := by
    simpa [prefixWord, tailWord_8040037, baseEnd_8040037] using wordTrace_append hprefix tailTrace_8040037
  have hstable : (prefixWord ++ tailWord_8040037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040037).length < 2 ^ (prefixWord ++ tailWord_8040037).sum := by decide
  have hdescent : baseEnd_8040037 < baseStart_8040037 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040043 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4]
def baseStart_8040043 : Nat := 118140960795 + 8040043 * 2 ^ 59
def prefixEnd_8040043 : Nat := 4983230072969 + 3 ^ 40 * 8040043 * 2
def baseEnd_8040043 : Nat := 4128406541816792028487021

theorem tailTrace_8040043 : CollatzResearch.WordTrace tailWord_8040043 prefixEnd_8040043 4128406541816792028487021 := by
  unfold tailWord_8040043
  simp only [CollatzResearch.WordTrace]
  refine ⟨293244459211304815869044783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195496306140869877246029855 293244459211304815869044783)
  ·
    refine ⟨439866688816957223803567175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293244459211304815869044783 439866688816957223803567175)
    ·
      refine ⟨659800033225435835705350763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439866688816957223803567175 659800033225435835705350763)
      ·
        refine ⟨989700049838153753558026145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659800033225435835705350763 989700049838153753558026145)
        ·
          refine ⟨742275037378615315168519609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989700049838153753558026145 742275037378615315168519609)
          ·
            refine ⟨556706278033961486376389707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742275037378615315168519609 556706278033961486376389707)
            ·
              refine ⟨835059417050942229564584561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556706278033961486376389707 835059417050942229564584561)
              ·
                refine ⟨626294562788206672173438421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835059417050942229564584561 626294562788206672173438421)
                ·
                  refine ⟨14678778815348593879064963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 626294562788206672173438421 14678778815348593879064963)
                  ·
                    refine ⟨22018168223022890818597445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14678778815348593879064963 22018168223022890818597445)
                    ·
                      refine ⟨4128406541816792028487021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22018168223022890818597445 4128406541816792028487021)
                      ·
                        rfl

theorem cell23_8040043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 4].length) (baseStart_8040043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040043 prefixEnd_8040043 := by exact prefixLift 8040043
  have htrace : WordTrace (prefixWord ++ tailWord_8040043) baseStart_8040043 baseEnd_8040043 := by
    simpa [prefixWord, tailWord_8040043, baseEnd_8040043] using wordTrace_append hprefix tailTrace_8040043
  have hstable : (prefixWord ++ tailWord_8040043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040043).length < 2 ^ (prefixWord ++ tailWord_8040043).sum := by decide
  have hdescent : baseEnd_8040043 < baseStart_8040043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040063 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3]
def baseStart_8040063 : Nat := 118140960795 + 8040063 * 2 ^ 59
def prefixEnd_8040063 : Nat := 4983230072969 + 3 ^ 40 * 8040063 * 2
def baseEnd_8040063 : Nat := 4128416811429881950236929

theorem tailTrace_8040063 : CollatzResearch.WordTrace tailWord_8040063 prefixEnd_8040063 4128416811429881950236929 := by
  unfold tailWord_8040063
  simp only [CollatzResearch.WordTrace]
  refine ⟨293245188671232359284772843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195496792447488239523181895 293245188671232359284772843)
  ·
    refine ⟨439867783006848538927159265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293245188671232359284772843 439867783006848538927159265)
    ·
      refine ⟨329900837255136404195369449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439867783006848538927159265 329900837255136404195369449)
      ·
        refine ⟨247425627941352303146527087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329900837255136404195369449 247425627941352303146527087)
        ·
          refine ⟨371138441912028454719790631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247425627941352303146527087 371138441912028454719790631)
          ·
            refine ⟨556707662868042682079685947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371138441912028454719790631 556707662868042682079685947)
            ·
              refine ⟨835061494302064023119528921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556707662868042682079685947 835061494302064023119528921)
              ·
                refine ⟨626296120726548017339646691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 835061494302064023119528921 626296120726548017339646691)
                ·
                  refine ⟨939444181089822026009470037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 626296120726548017339646691 939444181089822026009470037)
                  ·
                    refine ⟨11009111497146351867298477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 939444181089822026009470037 11009111497146351867298477)
                    ·
                      refine ⟨4128416811429881950236929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009111497146351867298477 4128416811429881950236929)
                      ·
                        rfl

theorem cell23_8040063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 3].length) (baseStart_8040063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040063 prefixEnd_8040063 := by exact prefixLift 8040063
  have htrace : WordTrace (prefixWord ++ tailWord_8040063) baseStart_8040063 baseEnd_8040063 := by
    simpa [prefixWord, tailWord_8040063, baseEnd_8040063] using wordTrace_append hprefix tailTrace_8040063
  have hstable : (prefixWord ++ tailWord_8040063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040063).length < 2 ^ (prefixWord ++ tailWord_8040063).sum := by decide
  have hdescent : baseEnd_8040063 < baseStart_8040063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040071 : List Nat := [1, 1, 4, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_8040071 : Nat := 118140960795 + 8040071 * 2 ^ 59
def prefixEnd_8040071 : Nat := 4983230072969 + 3 ^ 40 * 8040071 * 2
def baseEnd_8040071 : Nat := 4128420919275117918936893

theorem tailTrace_8040071 : CollatzResearch.WordTrace tailWord_8040071 prefixEnd_8040071 4128420919275117918936893 := by
  unfold tailWord_8040071
  simp only [CollatzResearch.WordTrace]
  refine ⟨293245480455203376651064067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195496986970135584434042711 293245480455203376651064067)
  ·
    refine ⟨439868220682805064976596101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293245480455203376651064067 439868220682805064976596101)
    ·
      refine ⟨82475291378025949683111769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439868220682805064976596101 82475291378025949683111769)
      ·
        refine ⟨61856468533519462262333827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82475291378025949683111769 61856468533519462262333827)
        ·
          refine ⟨92784702800279193393500741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61856468533519462262333827 92784702800279193393500741)
          ·
            refine ⟨17397131775052348761281389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92784702800279193393500741 17397131775052348761281389)
            ·
              refine ⟨6523924415644630785480521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17397131775052348761281389 6523924415644630785480521)
              ·
                refine ⟨4892943311733473089110391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523924415644630785480521 4892943311733473089110391)
                ·
                  refine ⟨7339414967600209633665587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4892943311733473089110391 7339414967600209633665587)
                  ·
                    refine ⟨11009122451400314450498381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339414967600209633665587 11009122451400314450498381)
                    ·
                      refine ⟨4128420919275117918936893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009122451400314450498381 4128420919275117918936893)
                      ·
                        rfl

theorem cell23_8040071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_8040071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040071 prefixEnd_8040071 := by exact prefixLift 8040071
  have htrace : WordTrace (prefixWord ++ tailWord_8040071) baseStart_8040071 baseEnd_8040071 := by
    simpa [prefixWord, tailWord_8040071, baseEnd_8040071] using wordTrace_append hprefix tailTrace_8040071
  have hstable : (prefixWord ++ tailWord_8040071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040071).length < 2 ^ (prefixWord ++ tailWord_8040071).sum := by decide
  have hdescent : baseEnd_8040071 < baseStart_8040071 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040073 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 6]
def baseStart_8040073 : Nat := 118140960795 + 8040073 * 2 ^ 59
def prefixEnd_8040073 : Nat := 4983230072969 + 3 ^ 40 * 8040073 * 2
def baseEnd_8040073 : Nat := 4128421946236426911111883

theorem tailTrace_8040073 : CollatzResearch.WordTrace tailWord_8040073 prefixEnd_8040073 4128421946236426911111883 := by
  unfold tailWord_8040073
  simp only [CollatzResearch.WordTrace]
  refine ⟨293245553401196130992636873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195497035600797420661757915 293245553401196130992636873)
  ·
    refine ⟨219934165050897098244477655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293245553401196130992636873 219934165050897098244477655)
    ·
      refine ⟨329901247576345647366716483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219934165050897098244477655 329901247576345647366716483)
      ·
        refine ⟨494851871364518471050074725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329901247576345647366716483 494851871364518471050074725)
        ·
          refine ⟨92784725880847213321889011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494851871364518471050074725 92784725880847213321889011)
          ·
            refine ⟨139177088821270819982833517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92784725880847213321889011 139177088821270819982833517)
            ·
              refine ⟨52191408307976557493562569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139177088821270819982833517 52191408307976557493562569)
              ·
                refine ⟨39143556230982418120171927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52191408307976557493562569 39143556230982418120171927)
                ·
                  refine ⟨58715334346473627180257891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39143556230982418120171927 58715334346473627180257891)
                  ·
                    refine ⟨88073001519710440770386837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58715334346473627180257891 88073001519710440770386837)
                    ·
                      refine ⟨4128421946236426911111883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88073001519710440770386837 4128421946236426911111883)
                      ·
                        rfl

theorem cell23_8040073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_8040073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040073 prefixEnd_8040073 := by exact prefixLift 8040073
  have htrace : WordTrace (prefixWord ++ tailWord_8040073) baseStart_8040073 baseEnd_8040073 := by
    simpa [prefixWord, tailWord_8040073, baseEnd_8040073] using wordTrace_append hprefix tailTrace_8040073
  have hstable : (prefixWord ++ tailWord_8040073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040073).length < 2 ^ (prefixWord ++ tailWord_8040073).sum := by decide
  have hdescent : baseEnd_8040073 < baseStart_8040073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040087 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 2, 4]
def baseStart_8040087 : Nat := 118140960795 + 8040087 * 2 ^ 59
def prefixEnd_8040087 : Nat := 4983230072969 + 3 ^ 40 * 8040087 * 2
def baseEnd_8040087 : Nat := 1376143044988529952112273

theorem tailTrace_8040087 : CollatzResearch.WordTrace tailWord_8040087 prefixEnd_8040087 1376143044988529952112273 := by
  unfold tailWord_8040087
  simp only [CollatzResearch.WordTrace]
  refine ⟨293246064023145411383646515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195497376015430274255764343 293246064023145411383646515)
  ·
    refine ⟨439869096034718117075469773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293246064023145411383646515 439869096034718117075469773)
    ·
      refine ⟨164950911013019293903301165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439869096034718117075469773 164950911013019293903301165)
      ·
        refine ⟨61856591629882235213737937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164950911013019293903301165 61856591629882235213737937)
        ·
          refine ⟨46392443722411676410303453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61856591629882235213737937 46392443722411676410303453)
          ·
            refine ⟨17397166395904378653863795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46392443722411676410303453 17397166395904378653863795)
            ·
              refine ⟨26095749593856567980795693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397166395904378653863795 26095749593856567980795693)
              ·
                refine ⟨9785906097696212992798385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26095749593856567980795693 9785906097696212992798385)
                ·
                  refine ⟨7339429573272159744598789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785906097696212992798385 7339429573272159744598789)
                  ·
                    refine ⟨1376143044988529952112273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7339429573272159744598789 1376143044988529952112273)
                    ·
                      rfl

theorem cell23_8040087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 4].length) (baseStart_8040087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040087 prefixEnd_8040087 := by exact prefixLift 8040087
  have htrace : WordTrace (prefixWord ++ tailWord_8040087) baseStart_8040087 baseEnd_8040087 := by
    simpa [prefixWord, tailWord_8040087, baseEnd_8040087] using wordTrace_append hprefix tailTrace_8040087
  have hstable : (prefixWord ++ tailWord_8040087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040087).length < 2 ^ (prefixWord ++ tailWord_8040087).sum := by decide
  have hdescent : baseEnd_8040087 < baseStart_8040087 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040094 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_8040094 : Nat := 118140960795 + 8040094 * 2 ^ 59
def prefixEnd_8040094 : Nat := 4983230072969 + 3 ^ 40 * 8040094 * 2
def baseEnd_8040094 : Nat := 4128432729330171328949287

theorem tailTrace_8040094 : CollatzResearch.WordTrace tailWord_8040094 prefixEnd_8040094 4128432729330171328949287 := by
  unfold tailWord_8040094
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655789916765006447393917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195497546222746701052767557 36655789916765006447393917)
  ·
    refine ⟨13745921218786877417772719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36655789916765006447393917 13745921218786877417772719)
    ·
      refine ⟨20618881828180316126659079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13745921218786877417772719 20618881828180316126659079)
      ·
        refine ⟨30928322742270474189988619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618881828180316126659079 30928322742270474189988619)
        ·
          refine ⟨46392484113405711284982929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30928322742270474189988619 46392484113405711284982929)
          ·
            refine ⟨34794363085054283463737197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46392484113405711284982929 34794363085054283463737197)
            ·
              refine ⟨13047886156895356298901449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34794363085054283463737197 13047886156895356298901449)
              ·
                refine ⟨9785914617671517224176087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13047886156895356298901449 9785914617671517224176087)
                ·
                  refine ⟨14678871926507275836264131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9785914617671517224176087 14678871926507275836264131)
                  ·
                    refine ⟨22018307889760913754396197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14678871926507275836264131 22018307889760913754396197)
                    ·
                      refine ⟨4128432729330171328949287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22018307889760913754396197 4128432729330171328949287)
                      ·
                        rfl

theorem cell23_8040094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_8040094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040094 prefixEnd_8040094 := by exact prefixLift 8040094
  have htrace : WordTrace (prefixWord ++ tailWord_8040094) baseStart_8040094 baseEnd_8040094 := by
    simpa [prefixWord, tailWord_8040094, baseEnd_8040094] using wordTrace_append hprefix tailTrace_8040094
  have hstable : (prefixWord ++ tailWord_8040094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040094).length < 2 ^ (prefixWord ++ tailWord_8040094).sum := by decide
  have hdescent : baseEnd_8040094 < baseStart_8040094 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040097 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_8040097 : Nat := 118140960795 + 8040097 * 2 ^ 59
def prefixEnd_8040097 : Nat := 4983230072969 + 3 ^ 40 * 8040097 * 2
def baseEnd_8040097 : Nat := 4128434269772134817211773

theorem tailTrace_8040097 : CollatzResearch.WordTrace tailWord_8040097 prefixEnd_8040097 4128434269772134817211773 := by
  unfold tailWord_8040097
  simp only [CollatzResearch.WordTrace]
  refine ⟨293246428753109183091510545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195497619168739455394340363 293246428753109183091510545)
  ·
    refine ⟨219934821564831887318632909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293246428753109183091510545 219934821564831887318632909)
    ·
      refine ⟨82475558086811957744487341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219934821564831887318632909 82475558086811957744487341)
      ·
        refine ⟨30928334282554484154182753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82475558086811957744487341 30928334282554484154182753)
        ·
          refine ⟨23196250711915863115637065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30928334282554484154182753 23196250711915863115637065)
          ·
            refine ⟨17397188033936897336727799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23196250711915863115637065 17397188033936897336727799)
            ·
              refine ⟨26095782050905346005091699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397188033936897336727799 26095782050905346005091699)
              ·
                refine ⟨39143673076358019007637549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26095782050905346005091699 39143673076358019007637549)
                ·
                  refine ⟨14678877403634257127864081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39143673076358019007637549 14678877403634257127864081)
                  ·
                    refine ⟨11009158052725692845898061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14678877403634257127864081 11009158052725692845898061)
                    ·
                      refine ⟨4128434269772134817211773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009158052725692845898061 4128434269772134817211773)
                      ·
                        rfl

theorem cell23_8040097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_8040097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040097 prefixEnd_8040097 := by exact prefixLift 8040097
  have htrace : WordTrace (prefixWord ++ tailWord_8040097) baseStart_8040097 baseEnd_8040097 := by
    simpa [prefixWord, tailWord_8040097, baseEnd_8040097] using wordTrace_append hprefix tailTrace_8040097
  have hstable : (prefixWord ++ tailWord_8040097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040097).length < 2 ^ (prefixWord ++ tailWord_8040097).sum := by decide
  have hdescent : baseEnd_8040097 < baseStart_8040097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040123 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5]
def baseStart_8040123 : Nat := 118140960795 + 8040123 * 2 ^ 59
def prefixEnd_8040123 : Nat := 4983230072969 + 3 ^ 40 * 8040123 * 2
def baseEnd_8040123 : Nat := 4128447620269151715486653

theorem tailTrace_8040123 : CollatzResearch.WordTrace tailWord_8040123 prefixEnd_8040123 4128447620269151715486653 := by
  unfold tailWord_8040123
  simp only [CollatzResearch.WordTrace]
  refine ⟨293247377051014989531957023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195498251367343326354638015 293247377051014989531957023)
  ·
    refine ⟨439871065576522484297935535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293247377051014989531957023 439871065576522484297935535)
    ·
      refine ⟨659806598364783726446903303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439871065576522484297935535 659806598364783726446903303)
      ·
        refine ⟨989709897547175589670354955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659806598364783726446903303 989709897547175589670354955)
        ·
          refine ⟨1484564846320763384505532433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989709897547175589670354955 1484564846320763384505532433)
          ·
            refine ⟨1113423634740572538379149325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484564846320763384505532433 1113423634740572538379149325)
            ·
              refine ⟨417533863027714701892180997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1113423634740572538379149325 417533863027714701892180997)
              ·
                refine ⟨78287599317696506604783937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417533863027714701892180997 78287599317696506604783937)
                ·
                  refine ⟨58715699488272379953587953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78287599317696506604783937 58715699488272379953587953)
                  ·
                    refine ⟨44036774616204284965190965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58715699488272379953587953 44036774616204284965190965)
                    ·
                      refine ⟨4128447620269151715486653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44036774616204284965190965 4128447620269151715486653)
                      ·
                        rfl

theorem cell23_8040123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 5].length) (baseStart_8040123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040123 prefixEnd_8040123 := by exact prefixLift 8040123
  have htrace : WordTrace (prefixWord ++ tailWord_8040123) baseStart_8040123 baseEnd_8040123 := by
    simpa [prefixWord, tailWord_8040123, baseEnd_8040123] using wordTrace_append hprefix tailTrace_8040123
  have hstable : (prefixWord ++ tailWord_8040123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040123).length < 2 ^ (prefixWord ++ tailWord_8040123).sum := by decide
  have hdescent : baseEnd_8040123 < baseStart_8040123 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040134 : List Nat := [6, 1, 2, 1, 1, 1, 3, 8]
def baseStart_8040134 : Nat := 118140960795 + 8040134 * 2 ^ 59
def prefixEnd_8040134 : Nat := 4983230072969 + 3 ^ 40 * 8040134 * 2
def baseEnd_8040134 : Nat := 152905676613198191572189

theorem tailTrace_8040134 : CollatzResearch.WordTrace tailWord_8040134 prefixEnd_8040134 152905676613198191572189 := by
  unfold tailWord_8040134
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163993070436723075331483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195498518835983425607071637 9163993070436723075331483)
  ·
    refine ⟨13745989605655084612997225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163993070436723075331483 13745989605655084612997225)
    ·
      refine ⟨10309492204241313459747919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13745989605655084612997225 10309492204241313459747919)
      ·
        refine ⟨15464238306361970189621879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10309492204241313459747919 15464238306361970189621879)
        ·
          refine ⟨23196357459542955284432819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15464238306361970189621879 23196357459542955284432819)
          ·
            refine ⟨34794536189314432926649229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23196357459542955284432819 34794536189314432926649229)
            ·
              refine ⟨13047951070992912347493461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34794536189314432926649229 13047951070992912347493461)
              ·
                refine ⟨152905676613198191572189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13047951070992912347493461 152905676613198191572189)
                ·
                  rfl

theorem cell23_8040134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_8040134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040134 prefixEnd_8040134 := by exact prefixLift 8040134
  have htrace : WordTrace (prefixWord ++ tailWord_8040134) baseStart_8040134 baseEnd_8040134 := by
    simpa [prefixWord, tailWord_8040134, baseEnd_8040134] using wordTrace_append hprefix tailTrace_8040134
  have hstable : (prefixWord ++ tailWord_8040134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040134).length < 2 ^ (prefixWord ++ tailWord_8040134).sum := by decide
  have hdescent : baseEnd_8040134 < baseStart_8040134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040170 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_8040170 : Nat := 118140960795 + 8040170 * 2 ^ 59
def prefixEnd_8040170 : Nat := 4983230072969 + 3 ^ 40 * 8040170 * 2
def baseEnd_8040170 : Nat := 4128471753859913031598937

theorem tailTrace_8040170 : CollatzResearch.WordTrace tailWord_8040170 prefixEnd_8040170 4128471753859913031598937 := by
  unfold tailWord_8040170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73312272820461179139729491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195499394187896477705945309 73312272820461179139729491)
  ·
    refine ⟨109968409230691768709594237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73312272820461179139729491 109968409230691768709594237)
    ·
      refine ⟨41238153461509413266097839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109968409230691768709594237 41238153461509413266097839)
      ·
        refine ⟨61857230192264119899146759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238153461509413266097839 61857230192264119899146759)
        ·
          refine ⟨92785845288396179848720139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61857230192264119899146759 92785845288396179848720139)
          ·
            refine ⟨139178767932594269773080209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92785845288396179848720139 139178767932594269773080209)
            ·
              refine ⟨104384075949445702329810157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139178767932594269773080209 104384075949445702329810157)
              ·
                refine ⟨39144028481042138373678809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104384075949445702329810157 39144028481042138373678809)
                ·
                  refine ⟨29358021360781603780259107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39144028481042138373678809 29358021360781603780259107)
                  ·
                    refine ⟨44037032041172405670388661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29358021360781603780259107 44037032041172405670388661)
                    ·
                      refine ⟨4128471753859913031598937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44037032041172405670388661 4128471753859913031598937)
                      ·
                        rfl

theorem cell23_8040170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_8040170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040170 prefixEnd_8040170 := by exact prefixLift 8040170
  have htrace : WordTrace (prefixWord ++ tailWord_8040170) baseStart_8040170 baseEnd_8040170 := by
    simpa [prefixWord, tailWord_8040170, baseEnd_8040170] using wordTrace_append hprefix tailTrace_8040170
  have hstable : (prefixWord ++ tailWord_8040170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040170).length < 2 ^ (prefixWord ++ tailWord_8040170).sum := by decide
  have hdescent : baseEnd_8040170 < baseStart_8040170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040184 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_8040184 : Nat := 118140960795 + 8040184 * 2 ^ 59
def prefixEnd_8040184 : Nat := 4983230072969 + 3 ^ 40 * 8040184 * 2
def baseEnd_8040184 : Nat := 4128478942589075976823873

theorem tailTrace_8040184 : CollatzResearch.WordTrace tailWord_8040184 prefixEnd_8040184 4128478942589075976823873 := by
  unfold tailWord_8040184
  simp only [CollatzResearch.WordTrace]
  refine ⟨146624800951896998474963803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195499734602529331299951737 146624800951896998474963803)
  ·
    refine ⟨219937201427845497712445705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146624800951896998474963803 219937201427845497712445705)
    ·
      refine ⟨164952901070884123284334279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219937201427845497712445705 164952901070884123284334279)
      ·
        refine ⟨247429351606326184926501419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164952901070884123284334279 247429351606326184926501419)
        ·
          refine ⟨371144027409489277389752129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247429351606326184926501419 371144027409489277389752129)
          ·
            refine ⟨278358020557116958042314097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371144027409489277389752129 278358020557116958042314097)
            ·
              refine ⟨208768515417837718531735573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278358020557116958042314097 208768515417837718531735573)
              ·
                refine ⟨9786024160211143056175105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208768515417837718531735573 9786024160211143056175105)
                ·
                  refine ⟨7339518120158357292131329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9786024160211143056175105 7339518120158357292131329)
                  ·
                    refine ⟨5504638590118767969098497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339518120158357292131329 5504638590118767969098497)
                    ·
                      refine ⟨4128478942589075976823873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504638590118767969098497 4128478942589075976823873)
                      ·
                        rfl

theorem cell23_8040184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_8040184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040184 prefixEnd_8040184 := by exact prefixLift 8040184
  have htrace : WordTrace (prefixWord ++ tailWord_8040184) baseStart_8040184 baseEnd_8040184 := by
    simpa [prefixWord, tailWord_8040184, baseEnd_8040184] using wordTrace_append hprefix tailTrace_8040184
  have hstable : (prefixWord ++ tailWord_8040184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040184).length < 2 ^ (prefixWord ++ tailWord_8040184).sum := by decide
  have hdescent : baseEnd_8040184 < baseStart_8040184 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040220 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_8040220 : Nat := 118140960795 + 8040220 * 2 ^ 59
def prefixEnd_8040220 : Nat := 4983230072969 + 3 ^ 40 * 8040220 * 2
def baseEnd_8040220 : Nat := 1376165809297545945324569

theorem tailTrace_8040220 : CollatzResearch.WordTrace tailWord_8040220 prefixEnd_8040220 1376165809297545945324569 := by
  unfold tailWord_8040220
  simp only [CollatzResearch.WordTrace]
  refine ⟨146625457465831787549119057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195500609954442383398825409 146625457465831787549119057)
  ·
    refine ⟨109969093099373840661839293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146625457465831787549119057 109969093099373840661839293)
    ·
      refine ⟨41238409912265190248189735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109969093099373840661839293 41238409912265190248189735)
      ·
        refine ⟨61857614868397785372284603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238409912265190248189735 61857614868397785372284603)
        ·
          refine ⟨92786422302596678058426905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61857614868397785372284603 92786422302596678058426905)
          ·
            refine ⟨69589816726947508543820179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92786422302596678058426905 69589816726947508543820179)
            ·
              refine ⟨104384725090421262815730269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69589816726947508543820179 104384725090421262815730269)
              ·
                refine ⟨39144271908907973555898851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104384725090421262815730269 39144271908907973555898851)
                ·
                  refine ⟨58716407863361960333848277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39144271908907973555898851 58716407863361960333848277)
                  ·
                    refine ⟨1376165809297545945324569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58716407863361960333848277 1376165809297545945324569)
                    ·
                      rfl

theorem cell23_8040220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_8040220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040220 prefixEnd_8040220 := by exact prefixLift 8040220
  have htrace : WordTrace (prefixWord ++ tailWord_8040220) baseStart_8040220 baseEnd_8040220 := by
    simpa [prefixWord, tailWord_8040220, baseEnd_8040220] using wordTrace_append hprefix tailTrace_8040220
  have hstable : (prefixWord ++ tailWord_8040220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040220).length < 2 ^ (prefixWord ++ tailWord_8040220).sum := by decide
  have hdescent : baseEnd_8040220 < baseStart_8040220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040270 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_8040270 : Nat := 118140960795 + 8040270 * 2 ^ 59
def prefixEnd_8040270 : Nat := 4983230072969 + 3 ^ 40 * 8040270 * 2
def baseEnd_8040270 : Nat := 4128523101925362640348477

theorem tailTrace_8040270 : CollatzResearch.WordTrace tailWord_8040270 prefixEnd_8040270 4128523101925362640348477 := by
  unfold tailWord_8040270
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656592322685304204694783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195501825720988289091705509 36656592322685304204694783)
  ·
    refine ⟨54984888484027956307042175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36656592322685304204694783 54984888484027956307042175)
    ·
      refine ⟨82477332726041934460563263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54984888484027956307042175 82477332726041934460563263)
      ·
        refine ⟨123715999089062901690844895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82477332726041934460563263 123715999089062901690844895)
        ·
          refine ⟨185573998633594352536267343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123715999089062901690844895 185573998633594352536267343)
          ·
            refine ⟨278360997950391528804401015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185573998633594352536267343 278360997950391528804401015)
            ·
              refine ⟨417541496925587293206601523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278360997950391528804401015 417541496925587293206601523)
              ·
                refine ⟨626312245388380939809902285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417541496925587293206601523 626312245388380939809902285)
                ·
                  refine ⟨234867092020642852428713357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 626312245388380939809902285 234867092020642852428713357)
                  ·
                    refine ⟨88075159507741069660767509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234867092020642852428713357 88075159507741069660767509)
                    ·
                      refine ⟨4128523101925362640348477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88075159507741069660767509 4128523101925362640348477)
                      ·
                        rfl

theorem cell23_8040270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_8040270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040270 prefixEnd_8040270 := by exact prefixLift 8040270
  have htrace : WordTrace (prefixWord ++ tailWord_8040270) baseStart_8040270 baseEnd_8040270 := by
    simpa [prefixWord, tailWord_8040270, baseEnd_8040270] using wordTrace_append hprefix tailTrace_8040270
  have hstable : (prefixWord ++ tailWord_8040270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040270).length < 2 ^ (prefixWord ++ tailWord_8040270).sum := by decide
  have hdescent : baseEnd_8040270 < baseStart_8040270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040274 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4]
def baseStart_8040274 : Nat := 118140960795 + 8040274 * 2 ^ 59
def prefixEnd_8040274 : Nat := 4983230072969 + 3 ^ 40 * 8040274 * 2
def baseEnd_8040274 : Nat := 4128525155847980624698459

theorem tailTrace_8040274 : CollatzResearch.WordTrace tailWord_8040274 prefixEnd_8040274 4128525155847980624698459 := by
  unfold tailWord_8040274
  simp only [CollatzResearch.WordTrace]
  refine ⟨73313221118366985580175969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195501922982311961547135917 73313221118366985580175969)
  ·
    refine ⟨54984915838775239185131977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73313221118366985580175969 54984915838775239185131977)
    ·
      refine ⟨41238686879081429388848983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54984915838775239185131977 41238686879081429388848983)
      ·
        refine ⟨61858030318622144083273475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238686879081429388848983 61858030318622144083273475)
        ·
          refine ⟨92787045477933216124910213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61858030318622144083273475 92787045477933216124910213)
          ·
            refine ⟨17397571027112478023420665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92787045477933216124910213 17397571027112478023420665)
            ·
              refine ⟨13048178270334358517565499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17397571027112478023420665 13048178270334358517565499)
              ·
                refine ⟨19572267405501537776348249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048178270334358517565499 19572267405501537776348249)
                ·
                  refine ⟨14679200554126153332261187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19572267405501537776348249 14679200554126153332261187)
                  ·
                    refine ⟨22018800831189229998391781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14679200554126153332261187 22018800831189229998391781)
                    ·
                      refine ⟨4128525155847980624698459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22018800831189229998391781 4128525155847980624698459)
                      ·
                        rfl

theorem cell23_8040274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4].length) (baseStart_8040274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040274 prefixEnd_8040274 := by exact prefixLift 8040274
  have htrace : WordTrace (prefixWord ++ tailWord_8040274) baseStart_8040274 baseEnd_8040274 := by
    simpa [prefixWord, tailWord_8040274, baseEnd_8040274] using wordTrace_append hprefix tailTrace_8040274
  have hstable : (prefixWord ++ tailWord_8040274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040274).length < 2 ^ (prefixWord ++ tailWord_8040274).sum := by decide
  have hdescent : baseEnd_8040274 < baseStart_8040274 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040320 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_8040320 : Nat := 118140960795 + 8040320 * 2 ^ 59
def prefixEnd_8040320 : Nat := 4983230072969 + 3 ^ 40 * 8040320 * 2
def baseEnd_8040320 : Nat := 4128548775958087444723247

theorem tailTrace_8040320 : CollatzResearch.WordTrace tailWord_8040320 prefixEnd_8040320 4128548775958087444723247 := by
  unfold tailWord_8040320
  simp only [CollatzResearch.WordTrace]
  refine ⟨146627281115650646088439207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195503041487534194784585609 146627281115650646088439207)
  ·
    refine ⟨219940921673475969132658811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146627281115650646088439207 219940921673475969132658811)
    ·
      refine ⟨329911382510213953698988217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219940921673475969132658811 329911382510213953698988217)
      ·
        refine ⟨247433536882660465274241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329911382510213953698988217 247433536882660465274241163)
        ·
          refine ⟨371150305323990697911361745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247433536882660465274241163 371150305323990697911361745)
          ·
            refine ⟨278362728992993023433521309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371150305323990697911361745 278362728992993023433521309)
            ·
              refine ⟨104386023372372383787570491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278362728992993023433521309 104386023372372383787570491)
              ·
                refine ⟨156579035058558575681355737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104386023372372383787570491 156579035058558575681355737)
                ·
                  refine ⟨117434276293918931761016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156579035058558575681355737 117434276293918931761016803)
                  ·
                    refine ⟨176151414440878397641525205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117434276293918931761016803 176151414440878397641525205)
                    ·
                      refine ⟨4128548775958087444723247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176151414440878397641525205 4128548775958087444723247)
                      ·
                        rfl

theorem cell23_8040320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_8040320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040320 prefixEnd_8040320 := by exact prefixLift 8040320
  have htrace : WordTrace (prefixWord ++ tailWord_8040320) baseStart_8040320 baseEnd_8040320 := by
    simpa [prefixWord, tailWord_8040320, baseEnd_8040320] using wordTrace_append hprefix tailTrace_8040320
  have hstable : (prefixWord ++ tailWord_8040320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040320).length < 2 ^ (prefixWord ++ tailWord_8040320).sum := by decide
  have hdescent : baseEnd_8040320 < baseStart_8040320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040324 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_8040324 : Nat := 118140960795 + 8040324 * 2 ^ 59
def prefixEnd_8040324 : Nat := 4983230072969 + 3 ^ 40 * 8040324 * 2
def baseEnd_8040324 : Nat := 4128550829880705429073229

theorem tailTrace_8040324 : CollatzResearch.WordTrace tailWord_8040324 prefixEnd_8040324 4128550829880705429073229 := by
  unfold tailWord_8040324
  simp only [CollatzResearch.WordTrace]
  refine ⟨146627354061643400430012013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195503138748857867240016017 146627354061643400430012013)
  ·
    refine ⟨54985257773116275161254505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146627354061643400430012013 54985257773116275161254505)
    ·
      refine ⟨41238943329837206370940879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54985257773116275161254505 41238943329837206370940879)
      ·
        refine ⟨61858414994755809556411319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238943329837206370940879 61858414994755809556411319)
        ·
          refine ⟨92787622492133714334616979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61858414994755809556411319 92787622492133714334616979)
          ·
            refine ⟨139181433738200571501925469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92787622492133714334616979 139181433738200571501925469)
            ·
              refine ⟨52193037651825214313222051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139181433738200571501925469 52193037651825214313222051)
              ·
                refine ⟨78289556477737821469833077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52193037651825214313222051 78289556477737821469833077)
                ·
                  refine ⟨7339645919787920762796851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78289556477737821469833077 7339645919787920762796851)
                  ·
                    refine ⟨11009468879681881144195277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339645919787920762796851 11009468879681881144195277)
                    ·
                      refine ⟨4128550829880705429073229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009468879681881144195277 4128550829880705429073229)
                      ·
                        rfl

theorem cell23_8040324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_8040324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040324 prefixEnd_8040324 := by exact prefixLift 8040324
  have htrace : WordTrace (prefixWord ++ tailWord_8040324) baseStart_8040324 baseEnd_8040324 := by
    simpa [prefixWord, tailWord_8040324, baseEnd_8040324] using wordTrace_append hprefix tailTrace_8040324
  have hstable : (prefixWord ++ tailWord_8040324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040324).length < 2 ^ (prefixWord ++ tailWord_8040324).sum := by decide
  have hdescent : baseEnd_8040324 < baseStart_8040324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040328 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_8040328 : Nat := 118140960795 + 8040328 * 2 ^ 59
def prefixEnd_8040328 : Nat := 4983230072969 + 3 ^ 40 * 8040328 * 2
def baseEnd_8040328 : Nat := 4128552883803323413423211

theorem tailTrace_8040328 : CollatzResearch.WordTrace tailWord_8040328 prefixEnd_8040328 4128552883803323413423211 := by
  unfold tailWord_8040328
  simp only [CollatzResearch.WordTrace]
  refine ⟨146627427007636154771584819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195503236010181539695446425 146627427007636154771584819)
  ·
    refine ⟨219941140511454232157377229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146627427007636154771584819 219941140511454232157377229)
    ·
      refine ⟨82477927691795337059016461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219941140511454232157377229 82477927691795337059016461)
      ·
        refine ⟨30929222884423251397131173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82477927691795337059016461 30929222884423251397131173)
        ·
          refine ⟨5799229290829359636962095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30929222884423251397131173 5799229290829359636962095)
          ·
            refine ⟨8698843936244039455443143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799229290829359636962095 8698843936244039455443143)
            ·
              refine ⟨13048265904366059183164715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698843936244039455443143 13048265904366059183164715)
              ·
                refine ⟨19572398856549088774747073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048265904366059183164715 19572398856549088774747073)
                ·
                  refine ⟨14679299142411816581060305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19572398856549088774747073 14679299142411816581060305)
                  ·
                    refine ⟨11009474356808862435795229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679299142411816581060305 11009474356808862435795229)
                    ·
                      refine ⟨4128552883803323413423211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009474356808862435795229 4128552883803323413423211)
                      ·
                        rfl

theorem cell23_8040328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_8040328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040328 prefixEnd_8040328 := by exact prefixLift 8040328
  have htrace : WordTrace (prefixWord ++ tailWord_8040328) baseStart_8040328 baseEnd_8040328 := by
    simpa [prefixWord, tailWord_8040328, baseEnd_8040328] using wordTrace_append hprefix tailTrace_8040328
  have hstable : (prefixWord ++ tailWord_8040328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040328).length < 2 ^ (prefixWord ++ tailWord_8040328).sum := by decide
  have hdescent : baseEnd_8040328 < baseStart_8040328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040367 : List Nat := [1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5]
def baseStart_8040367 : Nat := 118140960795 + 8040367 * 2 ^ 59
def prefixEnd_8040367 : Nat := 4983230072969 + 3 ^ 40 * 8040367 * 2
def baseEnd_8040367 : Nat := 4128572909548848760835531

theorem tailTrace_8040367 : CollatzResearch.WordTrace tailWord_8040367 prefixEnd_8040367 4128572909548848760835531 := by
  unfold tailWord_8040367
  simp only [CollatzResearch.WordTrace]
  refine ⟨293256276462131019203839355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195504184308087346135892903 293256276462131019203839355)
  ·
    refine ⟨439884414693196528805759033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293256276462131019203839355 439884414693196528805759033)
    ·
      refine ⟨329913311019897396604319275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439884414693196528805759033 329913311019897396604319275)
      ·
        refine ⟨494869966529846094906478913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329913311019897396604319275 494869966529846094906478913)
        ·
          refine ⟨371152474897384571179859185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494869966529846094906478913 371152474897384571179859185)
          ·
            refine ⟨278364356173038428384894389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371152474897384571179859185 278364356173038428384894389)
            ·
              refine ⟨26096658391222352661083849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278364356173038428384894389 26096658391222352661083849)
              ·
                refine ⟨19572493793416764495812887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26096658391222352661083849 19572493793416764495812887)
                ·
                  refine ⟨29358740690125146743719331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19572493793416764495812887 29358740690125146743719331)
                  ·
                    refine ⟨44038111035187720115578997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29358740690125146743719331 44038111035187720115578997)
                    ·
                      refine ⟨4128572909548848760835531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44038111035187720115578997 4128572909548848760835531)
                      ·
                        rfl

theorem cell23_8040367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 5].length) (baseStart_8040367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040367 prefixEnd_8040367 := by exact prefixLift 8040367
  have htrace : WordTrace (prefixWord ++ tailWord_8040367) baseStart_8040367 baseEnd_8040367 := by
    simpa [prefixWord, tailWord_8040367, baseEnd_8040367] using wordTrace_append hprefix tailTrace_8040367
  have hstable : (prefixWord ++ tailWord_8040367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040367).length < 2 ^ (prefixWord ++ tailWord_8040367).sum := by decide
  have hdescent : baseEnd_8040367 < baseStart_8040367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040377 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 6]
def baseStart_8040377 : Nat := 118140960795 + 8040377 * 2 ^ 59
def prefixEnd_8040377 : Nat := 4983230072969 + 3 ^ 40 * 8040377 * 2
def baseEnd_8040377 : Nat := 4128578044355393721710485

theorem tailTrace_8040377 : CollatzResearch.WordTrace tailWord_8040377 prefixEnd_8040377 4128578044355393721710485 := by
  unfold tailWord_8040377
  simp only [CollatzResearch.WordTrace]
  refine ⟨293256641192094790911703385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195504427461396527274468923 293256641192094790911703385)
  ·
    refine ⟨219942480894071093183777539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293256641192094790911703385 219942480894071093183777539)
    ·
      refine ⟨329913721341106639775666309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219942480894071093183777539 329913721341106639775666309)
      ·
        refine ⟨61858822751457494957937433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329913721341106639775666309 61858822751457494957937433)
        ·
          refine ⟨46394117063593121218453075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61858822751457494957937433 46394117063593121218453075)
          ·
            refine ⟨69591175595389681827679613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46394117063593121218453075 69591175595389681827679613)
            ·
              refine ⟨26096690848271130685379855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69591175595389681827679613 26096690848271130685379855)
              ·
                refine ⟨39145036272406696028069783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26096690848271130685379855 39145036272406696028069783)
                ·
                  refine ⟨58717554408610044042104675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39145036272406696028069783 58717554408610044042104675)
                  ·
                    refine ⟨88076331612915066063157013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58717554408610044042104675 88076331612915066063157013)
                    ·
                      refine ⟨4128578044355393721710485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88076331612915066063157013 4128578044355393721710485)
                      ·
                        rfl

theorem cell23_8040377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_8040377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040377 prefixEnd_8040377 := by exact prefixLift 8040377
  have htrace : WordTrace (prefixWord ++ tailWord_8040377) baseStart_8040377 baseEnd_8040377 := by
    simpa [prefixWord, tailWord_8040377, baseEnd_8040377] using wordTrace_append hprefix tailTrace_8040377
  have hstable : (prefixWord ++ tailWord_8040377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040377).length < 2 ^ (prefixWord ++ tailWord_8040377).sum := by decide
  have hdescent : baseEnd_8040377 < baseStart_8040377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040381 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_8040381 : Nat := 118140960795 + 8040381 * 2 ^ 59
def prefixEnd_8040381 : Nat := 4983230072969 + 3 ^ 40 * 8040381 * 2
def baseEnd_8040381 : Nat := 4128580098278011706060467

theorem tailTrace_8040381 : CollatzResearch.WordTrace tailWord_8040381 prefixEnd_8040381 4128580098278011706060467 := by
  unfold tailWord_8040381
  simp only [CollatzResearch.WordTrace]
  refine ⟨293256787084080299594848997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195504524722720199729899331 293256787084080299594848997)
  ·
    refine ⟨54985647578265056174034187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293256787084080299594848997 54985647578265056174034187)
    ·
      refine ⟨82478471367397584261051281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54985647578265056174034187 82478471367397584261051281)
      ·
        refine ⟨61858853525548188195788461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82478471367397584261051281 61858853525548188195788461)
        ·
          refine ⟨23197070072080570573420673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61858853525548188195788461 23197070072080570573420673)
          ·
            refine ⟨17397802554060427930065505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23197070072080570573420673 17397802554060427930065505)
            ·
              refine ⟨13048351915545320947549129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17397802554060427930065505 13048351915545320947549129)
              ·
                refine ⟨9786263936658990710661847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13048351915545320947549129 9786263936658990710661847)
                ·
                  refine ⟨14679395904988486065992771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9786263936658990710661847 14679395904988486065992771)
                  ·
                    refine ⟨22019093857482729098989157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14679395904988486065992771 22019093857482729098989157)
                    ·
                      refine ⟨4128580098278011706060467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22019093857482729098989157 4128580098278011706060467)
                      ·
                        rfl

theorem cell23_8040381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_8040381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040381 prefixEnd_8040381 := by exact prefixLift 8040381
  have htrace : WordTrace (prefixWord ++ tailWord_8040381) baseStart_8040381 baseEnd_8040381 := by
    simpa [prefixWord, tailWord_8040381, baseEnd_8040381] using wordTrace_append hprefix tailTrace_8040381
  have hstable : (prefixWord ++ tailWord_8040381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040381).length < 2 ^ (prefixWord ++ tailWord_8040381).sum := by decide
  have hdescent : baseEnd_8040381 < baseStart_8040381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040424 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_8040424 : Nat := 118140960795 + 8040424 * 2 ^ 59
def prefixEnd_8040424 : Nat := 4983230072969 + 3 ^ 40 * 8040424 * 2
def baseEnd_8040424 : Nat := 4128602177946155037822769

theorem tailTrace_8040424 : CollatzResearch.WordTrace tailWord_8040424 prefixEnd_8040424 4128602177946155037822769 := by
  unfold tailWord_8040424
  simp only [CollatzResearch.WordTrace]
  refine ⟨146629177711462258969332163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195505570281949678625776217 146629177711462258969332163)
  ·
    refine ⟨219943766567193388453998245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146629177711462258969332163 219943766567193388453998245)
    ·
      refine ⟨41239456231348760335124671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219943766567193388453998245 41239456231348760335124671)
      ·
        refine ⟨61859184347023140502687007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41239456231348760335124671 61859184347023140502687007)
        ·
          refine ⟨92788776520534710754030511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61859184347023140502687007 92788776520534710754030511)
          ·
            refine ⟨139183164780802066131045767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92788776520534710754030511 139183164780802066131045767)
            ·
              refine ⟨208774747171203099196568651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139183164780802066131045767 208774747171203099196568651)
              ·
                refine ⟨313162120756804648794852977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208774747171203099196568651 313162120756804648794852977)
                ·
                  refine ⟨234871590567603486596139733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313162120756804648794852977 234871590567603486596139733)
                  ·
                    refine ⟨5504802903928206717097025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 234871590567603486596139733 5504802903928206717097025)
                    ·
                      refine ⟨4128602177946155037822769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504802903928206717097025 4128602177946155037822769)
                      ·
                        rfl

theorem cell23_8040424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_8040424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040424 prefixEnd_8040424 := by exact prefixLift 8040424
  have htrace : WordTrace (prefixWord ++ tailWord_8040424) baseStart_8040424 baseEnd_8040424 := by
    simpa [prefixWord, tailWord_8040424, baseEnd_8040424] using wordTrace_append hprefix tailTrace_8040424
  have hstable : (prefixWord ++ tailWord_8040424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040424).length < 2 ^ (prefixWord ++ tailWord_8040424).sum := by decide
  have hdescent : baseEnd_8040424 < baseStart_8040424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040431 : List Nat := [1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 3]
def baseStart_8040431 : Nat := 118140960795 + 8040431 * 2 ^ 59
def prefixEnd_8040431 : Nat := 4983230072969 + 3 ^ 40 * 8040431 * 2
def baseEnd_8040431 : Nat := 4128605772310736510435237

theorem tailTrace_8040431 : CollatzResearch.WordTrace tailWord_8040431 prefixEnd_8040431 4128605772310736510435237 := by
  unfold tailWord_8040431
  simp only [CollatzResearch.WordTrace]
  refine ⟨293258610733899158134169147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195505740489266105422779431 293258610733899158134169147)
  ·
    refine ⟨439887916100848737201253721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293258610733899158134169147 439887916100848737201253721)
    ·
      refine ⟨329915937075636552900940291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439887916100848737201253721 329915937075636552900940291)
      ·
        refine ⟨494873905613454829351410437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329915937075636552900940291 494873905613454829351410437)
        ·
          refine ⟨92788857302522780503389457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 494873905613454829351410437 92788857302522780503389457)
          ·
            refine ⟨69591642976892085377542093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92788857302522780503389457 69591642976892085377542093)
            ·
              refine ⟨26096866116334532016578285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69591642976892085377542093 26096866116334532016578285)
              ·
                refine ⟨9786324793625449506216857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26096866116334532016578285 9786324793625449506216857)
                ·
                  refine ⟨7339743595219087129662643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9786324793625449506216857 7339743595219087129662643)
                  ·
                    refine ⟨11009615392828630694493965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339743595219087129662643 11009615392828630694493965)
                    ·
                      refine ⟨4128605772310736510435237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009615392828630694493965 4128605772310736510435237)
                      ·
                        rfl

theorem cell23_8040431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 1, 3].length) (baseStart_8040431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040431 prefixEnd_8040431 := by exact prefixLift 8040431
  have htrace : WordTrace (prefixWord ++ tailWord_8040431) baseStart_8040431 baseEnd_8040431 := by
    simpa [prefixWord, tailWord_8040431, baseEnd_8040431] using wordTrace_append hprefix tailTrace_8040431
  have hstable : (prefixWord ++ tailWord_8040431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040431).length < 2 ^ (prefixWord ++ tailWord_8040431).sum := by decide
  have hdescent : baseEnd_8040431 < baseStart_8040431 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040441 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 3, 3, 2]
def baseStart_8040441 : Nat := 118140960795 + 8040441 * 2 ^ 59
def prefixEnd_8040441 : Nat := 4983230072969 + 3 ^ 40 * 8040441 * 2
def baseEnd_8040441 : Nat := 4128610907117281471310191

theorem tailTrace_8040441 : CollatzResearch.WordTrace tailWord_8040441 prefixEnd_8040441 4128610907117281471310191 := by
  unfold tailWord_8040441
  simp only [CollatzResearch.WordTrace]
  refine ⟨293258975463862929842033177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195505983642575286561355451 293258975463862929842033177)
  ·
    refine ⟨219944231597897197381524883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293258975463862929842033177 219944231597897197381524883)
    ·
      refine ⟨329916347396845796072287325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219944231597897197381524883 329916347396845796072287325)
      ·
        refine ⟨123718630273817173527107747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329916347396845796072287325 123718630273817173527107747)
        ·
          refine ⟨185577945410725760290661621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123718630273817173527107747 185577945410725760290661621)
          ·
            refine ⟨17397932382255540027249527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185577945410725760290661621 17397932382255540027249527)
            ·
              refine ⟨26096898573383310040874291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17397932382255540027249527 26096898573383310040874291)
              ·
                refine ⟨39145347860074965061311437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26096898573383310040874291 39145347860074965061311437)
                ·
                  refine ⟨14679505447528111897991789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39145347860074965061311437 14679505447528111897991789)
                  ·
                    refine ⟨5504814542823041961746921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14679505447528111897991789 5504814542823041961746921)
                    ·
                      refine ⟨4128610907117281471310191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504814542823041961746921 4128610907117281471310191)
                      ·
                        rfl

theorem cell23_8040441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_8040441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040441 prefixEnd_8040441 := by exact prefixLift 8040441
  have htrace : WordTrace (prefixWord ++ tailWord_8040441) baseStart_8040441 baseEnd_8040441 := by
    simpa [prefixWord, tailWord_8040441, baseEnd_8040441] using wordTrace_append hprefix tailTrace_8040441
  have hstable : (prefixWord ++ tailWord_8040441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040441).length < 2 ^ (prefixWord ++ tailWord_8040441).sum := by decide
  have hdescent : baseEnd_8040441 < baseStart_8040441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040474 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3]
def baseStart_8040474 : Nat := 118140960795 + 8040474 * 2 ^ 59
def prefixEnd_8040474 : Nat := 4983230072969 + 3 ^ 40 * 8040474 * 2
def baseEnd_8040474 : Nat := 4128627851978879842197539

theorem tailTrace_8040474 : CollatzResearch.WordTrace tailWord_8040474 prefixEnd_8040474 4128627851978879842197539 := by
  unfold tailWord_8040474
  simp only [CollatzResearch.WordTrace]
  refine ⟨73315044768185844119496119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195506786048495584318656317 73315044768185844119496119)
  ·
    refine ⟨109972567152278766179244179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73315044768185844119496119 109972567152278766179244179)
    ·
      refine ⟨164958850728418149268866269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109972567152278766179244179 164958850728418149268866269)
      ·
        refine ⟨61859569023156805975824851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164958850728418149268866269 61859569023156805975824851)
        ·
          refine ⟨92789353534735208963737277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61859569023156805975824851 92789353534735208963737277)
          ·
            refine ⟨34796007575525703361401479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92789353534735208963737277 34796007575525703361401479)
            ·
              refine ⟨52194011363288555042102219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34796007575525703361401479 52194011363288555042102219)
              ·
                refine ⟨78291017044932832563153329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52194011363288555042102219 78291017044932832563153329)
                ·
                  refine ⟨58718262783699624422364997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78291017044932832563153329 58718262783699624422364997)
                  ·
                    refine ⟨11009674271943679579193437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58718262783699624422364997 11009674271943679579193437)
                    ·
                      refine ⟨4128627851978879842197539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009674271943679579193437 4128627851978879842197539)
                      ·
                        rfl

theorem cell23_8040474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_8040474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040474 prefixEnd_8040474 := by exact prefixLift 8040474
  have htrace : WordTrace (prefixWord ++ tailWord_8040474) baseStart_8040474 baseEnd_8040474 := by
    simpa [prefixWord, tailWord_8040474, baseEnd_8040474] using wordTrace_append hprefix tailTrace_8040474
  have hstable : (prefixWord ++ tailWord_8040474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040474).length < 2 ^ (prefixWord ++ tailWord_8040474).sum := by decide
  have hdescent : baseEnd_8040474 < baseStart_8040474 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040494 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 9]
def baseStart_8040494 : Nat := 118140960795 + 8040494 * 2 ^ 59
def prefixEnd_8040494 : Nat := 4983230072969 + 3 ^ 40 * 8040494 * 2
def baseEnd_8040494 : Nat := 458737569065774418216383

theorem tailTrace_8040494 : CollatzResearch.WordTrace tailWord_8040494 prefixEnd_8040494 458737569065774418216383 := by
  unfold tailWord_8040494
  simp only [CollatzResearch.WordTrace]
  refine ⟨36657613566583864986714067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195507272355113946595808357 36657613566583864986714067)
  ·
    refine ⟨54986420349875797480071101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36657613566583864986714067 54986420349875797480071101)
    ·
      refine ⟨20619907631203424055026663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54986420349875797480071101 20619907631203424055026663)
      ·
        refine ⟨30929861446805136082539995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20619907631203424055026663 30929861446805136082539995)
        ·
          refine ⟨46394792170207704123809993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30929861446805136082539995 46394792170207704123809993)
          ·
            refine ⟨34796094127655778092857495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46394792170207704123809993 34796094127655778092857495)
            ·
              refine ⟨52194141191483667139286243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34796094127655778092857495 52194141191483667139286243)
              ·
                refine ⟨78291211787225500708929365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52194141191483667139286243 78291211787225500708929365)
                ·
                  refine ⟨458737569065774418216383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78291211787225500708929365 458737569065774418216383)
                  ·
                    rfl

theorem cell23_8040494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 9].length) (baseStart_8040494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040494 prefixEnd_8040494 := by exact prefixLift 8040494
  have htrace : WordTrace (prefixWord ++ tailWord_8040494) baseStart_8040494 baseEnd_8040494 := by
    simpa [prefixWord, tailWord_8040494, baseEnd_8040494] using wordTrace_append hprefix tailTrace_8040494
  have hstable : (prefixWord ++ tailWord_8040494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040494).length < 2 ^ (prefixWord ++ tailWord_8040494).sum := by decide
  have hdescent : baseEnd_8040494 < baseStart_8040494 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040507 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 7]
def baseStart_8040507 : Nat := 118140960795 + 8040507 * 2 ^ 59
def prefixEnd_8040507 : Nat := 4983230072969 + 3 ^ 40 * 8040507 * 2
def baseEnd_8040507 : Nat := 1376214932280159404361629

theorem tailTrace_8040507 : CollatzResearch.WordTrace tailWord_8040507 prefixEnd_8040507 1376214932280159404361629 := by
  unfold tailWord_8040507
  simp only [CollatzResearch.WordTrace]
  refine ⟨293261382681623823113935775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195507588454415882075957183 293261382681623823113935775)
  ·
    refine ⟨439892074022435734670903663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293261382681623823113935775 439892074022435734670903663)
    ·
      refine ⟨659838111033653602006355495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439892074022435734670903663 659838111033653602006355495)
      ·
        refine ⟨989757166550480403009533243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659838111033653602006355495 989757166550480403009533243)
        ·
          refine ⟨1484635749825720604514299865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989757166550480403009533243 1484635749825720604514299865)
          ·
            refine ⟨1113476812369290453385724899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484635749825720604514299865 1113476812369290453385724899)
            ·
              refine ⟨1670215218553935680078587349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113476812369290453385724899 1670215218553935680078587349)
              ·
                refine ⟨39145669184857867501841891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1670215218553935680078587349 39145669184857867501841891)
                ·
                  refine ⟨58718503777286801252762837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39145669184857867501841891 58718503777286801252762837)
                  ·
                    refine ⟨1376214932280159404361629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58718503777286801252762837 1376214932280159404361629)
                    ·
                      rfl

theorem cell23_8040507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 7].length) (baseStart_8040507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040507 prefixEnd_8040507 := by exact prefixLift 8040507
  have htrace : WordTrace (prefixWord ++ tailWord_8040507) baseStart_8040507 baseEnd_8040507 := by
    simpa [prefixWord, tailWord_8040507, baseEnd_8040507] using wordTrace_append hprefix tailTrace_8040507
  have hstable : (prefixWord ++ tailWord_8040507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040507).length < 2 ^ (prefixWord ++ tailWord_8040507).sum := by decide
  have hdescent : baseEnd_8040507 < baseStart_8040507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040524 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_8040524 : Nat := 118140960795 + 8040524 * 2 ^ 59
def prefixEnd_8040524 : Nat := 4983230072969 + 3 ^ 40 * 8040524 * 2
def baseEnd_8040524 : Nat := 1376217842003868215524103

theorem tailTrace_8040524 : CollatzResearch.WordTrace tailWord_8040524 prefixEnd_8040524 1376217842003868215524103 := by
  unfold tailWord_8040524
  simp only [CollatzResearch.WordTrace]
  refine ⟨146631001361281117508652313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195508001815041490011536417 146631001361281117508652313)
  ·
    refine ⟨109973251020960838131489235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146631001361281117508652313 109973251020960838131489235)
    ·
      refine ⟨164959876531441257197233853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109973251020960838131489235 164959876531441257197233853)
      ·
        refine ⟨61859953699290471448962695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164959876531441257197233853 61859953699290471448962695)
        ·
          refine ⟨92789930548935707173444043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61859953699290471448962695 92789930548935707173444043)
          ·
            refine ⟨139184895823403560760166065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92789930548935707173444043 139184895823403560760166065)
            ·
              refine ⟨104388671867552670570124549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139184895823403560760166065 104388671867552670570124549)
              ·
                refine ⟨19572875975166125731898353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104388671867552670570124549 19572875975166125731898353)
                ·
                  refine ⟨14679656981374594298923765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19572875975166125731898353 14679656981374594298923765)
                  ·
                    refine ⟨1376217842003868215524103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14679656981374594298923765 1376217842003868215524103)
                    ·
                      rfl

theorem cell23_8040524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_8040524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040524 prefixEnd_8040524 := by exact prefixLift 8040524
  have htrace : WordTrace (prefixWord ++ tailWord_8040524) baseStart_8040524 baseEnd_8040524 := by
    simpa [prefixWord, tailWord_8040524, baseEnd_8040524] using wordTrace_append hprefix tailTrace_8040524
  have hstable : (prefixWord ++ tailWord_8040524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040524).length < 2 ^ (prefixWord ++ tailWord_8040524).sum := by decide
  have hdescent : baseEnd_8040524 < baseStart_8040524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040541 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_8040541 : Nat := 118140960795 + 8040541 * 2 ^ 59
def prefixEnd_8040541 : Nat := 4983230072969 + 3 ^ 40 * 8040541 * 2
def baseEnd_8040541 : Nat := 1376220751727577026686577

theorem tailTrace_8040541 : CollatzResearch.WordTrace tailWord_8040541 prefixEnd_8040541 1376220751727577026686577 := by
  unfold tailWord_8040541
  simp only [CollatzResearch.WordTrace]
  refine ⟨293262622763500646920673477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195508415175667097947115651 293262622763500646920673477)
  ·
    refine ⟨54986741768156371297626277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293262622763500646920673477 54986741768156371297626277)
    ·
      refine ⟨10310014081529319618304927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54986741768156371297626277 10310014081529319618304927)
      ·
        refine ⟨15465021122293979427457391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310014081529319618304927 15465021122293979427457391)
        ·
          refine ⟨23197531683440969141186087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15465021122293979427457391 23197531683440969141186087)
          ·
            refine ⟨34796297525161453711779131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23197531683440969141186087 34796297525161453711779131)
            ·
              refine ⟨52194446287742180567668697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34796297525161453711779131 52194446287742180567668697)
              ·
                refine ⟨39145834715806635425751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52194446287742180567668697 39145834715806635425751523)
                ·
                  refine ⟨58718752073709953138627285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39145834715806635425751523 58718752073709953138627285)
                  ·
                    refine ⟨1376220751727577026686577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58718752073709953138627285 1376220751727577026686577)
                    ·
                      rfl

theorem cell23_8040541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_8040541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040541 prefixEnd_8040541 := by exact prefixLift 8040541
  have htrace : WordTrace (prefixWord ++ tailWord_8040541) baseStart_8040541 baseEnd_8040541 := by
    simpa [prefixWord, tailWord_8040541, baseEnd_8040541] using wordTrace_append hprefix tailTrace_8040541
  have hstable : (prefixWord ++ tailWord_8040541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040541).length < 2 ^ (prefixWord ++ tailWord_8040541).sum := by decide
  have hdescent : baseEnd_8040541 < baseStart_8040541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040544 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_8040544 : Nat := 118140960795 + 8040544 * 2 ^ 59
def prefixEnd_8040544 : Nat := 4983230072969 + 3 ^ 40 * 8040544 * 2
def baseEnd_8040544 : Nat := 4128663795624694568322217

theorem tailTrace_8040544 : CollatzResearch.WordTrace tailWord_8040544 prefixEnd_8040544 4128663795624694568322217 := by
  unfold tailWord_8040544
  simp only [CollatzResearch.WordTrace]
  refine ⟨146631366091244889216516343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195508488121659852288688457 146631366091244889216516343)
  ·
    refine ⟨219947049136867333824774515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146631366091244889216516343 219947049136867333824774515)
    ·
      refine ⟨329920573705301000737161773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219947049136867333824774515 329920573705301000737161773)
      ·
        refine ⟨123720215139487875276435665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 329920573705301000737161773 123720215139487875276435665)
        ·
          refine ⟨92790161354615906457326749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123720215139487875276435665 92790161354615906457326749)
          ·
            refine ⟨34796310507980964921497531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92790161354615906457326749 34796310507980964921497531)
            ·
              refine ⟨52194465761971447382246297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34796310507980964921497531 52194465761971447382246297)
              ·
                refine ⟨39145849321478585536684723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52194465761971447382246297 39145849321478585536684723)
                ·
                  refine ⟨58718773982217878305027085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39145849321478585536684723 58718773982217878305027085)
                  ·
                    refine ⟨22019540243331704364385157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58718773982217878305027085 22019540243331704364385157)
                    ·
                      refine ⟨4128663795624694568322217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22019540243331704364385157 4128663795624694568322217)
                      ·
                        rfl

theorem cell23_8040544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_8040544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040544 prefixEnd_8040544 := by exact prefixLift 8040544
  have htrace : WordTrace (prefixWord ++ tailWord_8040544) baseStart_8040544 baseEnd_8040544 := by
    simpa [prefixWord, tailWord_8040544, baseEnd_8040544] using wordTrace_append hprefix tailTrace_8040544
  have hstable : (prefixWord ++ tailWord_8040544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040544).length < 2 ^ (prefixWord ++ tailWord_8040544).sum := by decide
  have hdescent : baseEnd_8040544 < baseStart_8040544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040581 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 3]
def baseStart_8040581 : Nat := 118140960795 + 8040581 * 2 ^ 59
def prefixEnd_8040581 : Nat := 4983230072969 + 3 ^ 40 * 8040581 * 2
def baseEnd_8040581 : Nat := 4128682794408910923559547

theorem tailTrace_8040581 : CollatzResearch.WordTrace tailWord_8040581 prefixEnd_8040581 4128682794408910923559547 := by
  unfold tailWord_8040581
  simp only [CollatzResearch.WordTrace]
  refine ⟨293264081683355733752129597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195509387788903822501419731 293264081683355733752129597)
  ·
    refine ⟨109974030631258400157048599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293264081683355733752129597 109974030631258400157048599)
    ·
      refine ⟨164961045946887600235572899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109974030631258400157048599 164961045946887600235572899)
      ·
        refine ⟨247441568920331400353359349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164961045946887600235572899 247441568920331400353359349)
        ·
          refine ⟨23197647086281068783127439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247441568920331400353359349 23197647086281068783127439)
          ·
            refine ⟨34796470629421603174691159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23197647086281068783127439 34796470629421603174691159)
            ·
              refine ⟨52194705944132404762036739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34796470629421603174691159 52194705944132404762036739)
              ·
                refine ⟨78292058916198607143055109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52194705944132404762036739 78292058916198607143055109)
                ·
                  refine ⟨14679761046787238839322833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78292058916198607143055109 14679761046787238839322833)
                  ·
                    refine ⟨11009820785090429129492125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679761046787238839322833 11009820785090429129492125)
                    ·
                      refine ⟨4128682794408910923559547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009820785090429129492125 4128682794408910923559547)
                      ·
                        rfl

theorem cell23_8040581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_8040581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040581 prefixEnd_8040581 := by exact prefixLift 8040581
  have htrace : WordTrace (prefixWord ++ tailWord_8040581) baseStart_8040581 baseEnd_8040581 := by
    simpa [prefixWord, tailWord_8040581, baseEnd_8040581] using wordTrace_append hprefix tailTrace_8040581
  have hstable : (prefixWord ++ tailWord_8040581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040581).length < 2 ^ (prefixWord ++ tailWord_8040581).sum := by decide
  have hdescent : baseEnd_8040581 < baseStart_8040581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040615 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_8040615 : Nat := 118140960795 + 8040615 * 2 ^ 59
def prefixEnd_8040615 : Nat := 4983230072969 + 3 ^ 40 * 8040615 * 2
def baseEnd_8040615 : Nat := 4128700252751163790534391

theorem tailTrace_8040615 : CollatzResearch.WordTrace tailWord_8040615 prefixEnd_8040615 4128700252751163790534391 := by
  unfold tailWord_8040615
  simp only [CollatzResearch.WordTrace]
  refine ⟨293265321765232557558867299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195510214510155038372578199 293265321765232557558867299)
  ·
    refine ⟨439897982647848836338300949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293265321765232557558867299 439897982647848836338300949)
    ·
      refine ⟨20620217936617914203357857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 439897982647848836338300949 20620217936617914203357857)
      ·
        refine ⟨15465163452463435652518393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20620217936617914203357857 15465163452463435652518393)
        ·
          refine ⟨11598872589347576739388795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15465163452463435652518393 11598872589347576739388795)
          ·
            refine ⟨17398308884021365109083193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11598872589347576739388795 17398308884021365109083193)
            ·
              refine ⟨13048731663016023831812395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17398308884021365109083193 13048731663016023831812395)
              ·
                refine ⟨19573097494524035747718593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048731663016023831812395 19573097494524035747718593)
                ·
                  refine ⟨14679823120893026810788945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19573097494524035747718593 14679823120893026810788945)
                  ·
                    refine ⟨11009867340669770108091709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14679823120893026810788945 11009867340669770108091709)
                    ·
                      refine ⟨4128700252751163790534391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009867340669770108091709 4128700252751163790534391)
                      ·
                        rfl

theorem cell23_8040615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_8040615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040615 prefixEnd_8040615 := by exact prefixLift 8040615
  have htrace : WordTrace (prefixWord ++ tailWord_8040615) baseStart_8040615 baseEnd_8040615 := by
    simpa [prefixWord, tailWord_8040615, baseEnd_8040615] using wordTrace_append hprefix tailTrace_8040615
  have hstable : (prefixWord ++ tailWord_8040615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040615).length < 2 ^ (prefixWord ++ tailWord_8040615).sum := by decide
  have hdescent : baseEnd_8040615 < baseStart_8040615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040662 : List Nat := [5, 2, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_8040662 : Nat := 118140960795 + 8040662 * 2 ^ 59
def prefixEnd_8040662 : Nat := 4983230072969 + 3 ^ 40 * 8040662 * 2
def baseEnd_8040662 : Nat := 4128724386341925106646675

theorem tailTrace_8040662 : CollatzResearch.WordTrace tailWord_8040662 prefixEnd_8040662 4128724386341925106646675 := by
  unfold tailWord_8040662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329189749753892786614265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195511357330708189723885493 18329189749753892786614265)
  ·
    refine ⟨13746892312315419589960699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18329189749753892786614265 13746892312315419589960699)
    ·
      refine ⟨20620338468473129384941049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746892312315419589960699 20620338468473129384941049)
      ·
        refine ⟨15465253851354847038705787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20620338468473129384941049 15465253851354847038705787)
        ·
          refine ⟨23197880777032270558058681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15465253851354847038705787 23197880777032270558058681)
          ·
            refine ⟨17398410582774202918544011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23197880777032270558058681 17398410582774202918544011)
            ·
              refine ⟨26097615874161304377816017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17398410582774202918544011 26097615874161304377816017)
              ·
                refine ⟨19573211905620978283362013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26097615874161304377816017 19573211905620978283362013)
                ·
                  refine ⟨7339954464607866856260755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19573211905620978283362013 7339954464607866856260755)
                  ·
                    refine ⟨11009931696911800284391133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7339954464607866856260755 11009931696911800284391133)
                    ·
                      refine ⟨4128724386341925106646675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009931696911800284391133 4128724386341925106646675)
                      ·
                        rfl

theorem cell23_8040662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_8040662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040662 prefixEnd_8040662 := by exact prefixLift 8040662
  have htrace : WordTrace (prefixWord ++ tailWord_8040662) baseStart_8040662 baseEnd_8040662 := by
    simpa [prefixWord, tailWord_8040662, baseEnd_8040662] using wordTrace_append hprefix tailTrace_8040662
  have hstable : (prefixWord ++ tailWord_8040662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040662).length < 2 ^ (prefixWord ++ tailWord_8040662).sum := by decide
  have hdescent : baseEnd_8040662 < baseStart_8040662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040685 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_8040685 : Nat := 118140960795 + 8040685 * 2 ^ 59
def prefixEnd_8040685 : Nat := 4983230072969 + 3 ^ 40 * 8040685 * 2
def baseEnd_8040685 : Nat := 4128736196396978516659069

theorem tailTrace_8040685 : CollatzResearch.WordTrace tailWord_8040685 prefixEnd_8040685 4128736196396978516659069 := by
  unfold tailWord_8040685
  simp only [CollatzResearch.WordTrace]
  refine ⟨293267874874978959513915509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195511916583319306342610339 293267874874978959513915509)
  ·
    refine ⟨27493863269529277454429579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293267874874978959513915509 27493863269529277454429579)
    ·
      refine ⟨41240794904293916181644369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27493863269529277454429579 41240794904293916181644369)
      ·
        refine ⟨30930596178220437136233277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41240794904293916181644369 30930596178220437136233277)
        ·
          refine ⟨11598973566832663926087479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30930596178220437136233277 11598973566832663926087479)
          ·
            refine ⟨17398460350248995889131219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11598973566832663926087479 17398460350248995889131219)
            ·
              refine ⟨26097690525373493833696829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17398460350248995889131219 26097690525373493833696829)
              ·
                refine ⟨9786633947015060187636311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26097690525373493833696829 9786633947015060187636311)
                ·
                  refine ⟨14679950920522590281454467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9786633947015060187636311 14679950920522590281454467)
                  ·
                    refine ⟨22019926380783885422181701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14679950920522590281454467 22019926380783885422181701)
                    ·
                      refine ⟨4128736196396978516659069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22019926380783885422181701 4128736196396978516659069)
                      ·
                        rfl

theorem cell23_8040685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_8040685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040685 prefixEnd_8040685 := by exact prefixLift 8040685
  have htrace : WordTrace (prefixWord ++ tailWord_8040685) baseStart_8040685 baseEnd_8040685 := by
    simpa [prefixWord, tailWord_8040685, baseEnd_8040685] using wordTrace_append hprefix tailTrace_8040685
  have hstable : (prefixWord ++ tailWord_8040685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040685).length < 2 ^ (prefixWord ++ tailWord_8040685).sum := by decide
  have hdescent : baseEnd_8040685 < baseStart_8040685 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040701 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_8040701 : Nat := 118140960795 + 8040701 * 2 ^ 59
def prefixEnd_8040701 : Nat := 4983230072969 + 3 ^ 40 * 8040701 * 2
def baseEnd_8040701 : Nat := 4128744412087450454058995

theorem tailTrace_8040701 : CollatzResearch.WordTrace tailWord_8040701 prefixEnd_8040701 4128744412087450454058995 := by
  unfold tailWord_8040701
  simp only [CollatzResearch.WordTrace]
  refine ⟨293268458442920994246497957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195512305628613996164331971 293268458442920994246497957)
  ·
    refine ⟨54987835958047686421218367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293268458442920994246497957 54987835958047686421218367)
    ·
      refine ⟨82481753937071529631827551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987835958047686421218367 82481753937071529631827551)
      ·
        refine ⟨123722630905607294447741327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82481753937071529631827551 123722630905607294447741327)
        ·
          refine ⟨185583946358410941671611991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123722630905607294447741327 185583946358410941671611991)
          ·
            refine ⟨278375919537616412507417987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185583946358410941671611991 278375919537616412507417987)
            ·
              refine ⟨417563879306424618761126981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278375919537616412507417987 417563879306424618761126981)
              ·
                refine ⟨78293227369954616017711309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 417563879306424618761126981 78293227369954616017711309)
                ·
                  refine ⟨29359960263732981006641741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78293227369954616017711309 29359960263732981006641741)
                  ·
                    refine ⟨11009985098899867877490653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29359960263732981006641741 11009985098899867877490653)
                    ·
                      refine ⟨4128744412087450454058995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11009985098899867877490653 4128744412087450454058995)
                      ·
                        rfl

theorem cell23_8040701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_8040701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040701 prefixEnd_8040701 := by exact prefixLift 8040701
  have htrace : WordTrace (prefixWord ++ tailWord_8040701) baseStart_8040701 baseEnd_8040701 := by
    simpa [prefixWord, tailWord_8040701, baseEnd_8040701] using wordTrace_append hprefix tailTrace_8040701
  have hstable : (prefixWord ++ tailWord_8040701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040701).length < 2 ^ (prefixWord ++ tailWord_8040701).sum := by decide
  have hdescent : baseEnd_8040701 < baseStart_8040701 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040702 : List Nat := [4, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_8040702 : Nat := 118140960795 + 8040702 * 2 ^ 59
def prefixEnd_8040702 : Nat := 4983230072969 + 3 ^ 40 * 8040702 * 2
def baseEnd_8040702 : Nat := 4128744925568104950146491

theorem tailTrace_8040702 : CollatzResearch.WordTrace tailWord_8040702 prefixEnd_8040702 4128744925568104950146491 := by
  unfold tailWord_8040702
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658561864489671427160545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195512329943944914278189573 36658561864489671427160545)
  ·
    refine ⟨27493921398367253570370409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36658561864489671427160545 27493921398367253570370409)
    ·
      refine ⟨20620441048775440177777807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27493921398367253570370409 20620441048775440177777807)
      ·
        refine ⟨30930661573163160266666711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620441048775440177777807 30930661573163160266666711)
        ·
          refine ⟨46395992359744740400000067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30930661573163160266666711 46395992359744740400000067)
          ·
            refine ⟨69593988539617110600000101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46395992359744740400000067 69593988539617110600000101)
            ·
              refine ⟨13048872851178208237500019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69593988539617110600000101 13048872851178208237500019)
              ·
                refine ⟨19573309276767312356250029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13048872851178208237500019 19573309276767312356250029)
                ·
                  refine ⟨7339990978787742133593761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19573309276767312356250029 7339990978787742133593761)
                  ·
                    refine ⟨5504993234090806600195321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339990978787742133593761 5504993234090806600195321)
                    ·
                      refine ⟨4128744925568104950146491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5504993234090806600195321 4128744925568104950146491)
                      ·
                        rfl

theorem cell23_8040702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_8040702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040702 prefixEnd_8040702 := by exact prefixLift 8040702
  have htrace : WordTrace (prefixWord ++ tailWord_8040702) baseStart_8040702 baseEnd_8040702 := by
    simpa [prefixWord, tailWord_8040702, baseEnd_8040702] using wordTrace_append hprefix tailTrace_8040702
  have hstable : (prefixWord ++ tailWord_8040702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040702).length < 2 ^ (prefixWord ++ tailWord_8040702).sum := by decide
  have hdescent : baseEnd_8040702 < baseStart_8040702 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040704 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_8040704 : Nat := 118140960795 + 8040704 * 2 ^ 59
def prefixEnd_8040704 : Nat := 4983230072969 + 3 ^ 40 * 8040704 * 2
def baseEnd_8040704 : Nat := 1376248650843137980773827

theorem tailTrace_8040704 : CollatzResearch.WordTrace tailWord_8040704 prefixEnd_8040704 1376248650843137980773827 := by
  unfold tailWord_8040704
  simp only [CollatzResearch.WordTrace]
  refine ⟨146634283930955062879428583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195512378574606750505904777 146634283930955062879428583)
  ·
    refine ⟨219951425896432594319142875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146634283930955062879428583 219951425896432594319142875)
    ·
      refine ⟨329927138844648891478714313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219951425896432594319142875 329927138844648891478714313)
      ·
        refine ⟨247445354133486668609035735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329927138844648891478714313 247445354133486668609035735)
        ·
          refine ⟨371168031200230002913553603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247445354133486668609035735 371168031200230002913553603)
          ·
            refine ⟨556752046800345004370330405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371168031200230002913553603 556752046800345004370330405)
            ·
              refine ⟨104391008775064688319436951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556752046800345004370330405 104391008775064688319436951)
              ·
                refine ⟨156586513162597032479155427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104391008775064688319436951 156586513162597032479155427)
                ·
                  refine ⟨234879769743895548718733141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156586513162597032479155427 234879769743895548718733141)
                  ·
                    refine ⟨1376248650843137980773827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234879769743895548718733141 1376248650843137980773827)
                    ·
                      rfl

theorem cell23_8040704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_8040704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040704 prefixEnd_8040704 := by exact prefixLift 8040704
  have htrace : WordTrace (prefixWord ++ tailWord_8040704) baseStart_8040704 baseEnd_8040704 := by
    simpa [prefixWord, tailWord_8040704, baseEnd_8040704] using wordTrace_append hprefix tailTrace_8040704
  have hstable : (prefixWord ++ tailWord_8040704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040704).length < 2 ^ (prefixWord ++ tailWord_8040704).sum := by decide
  have hdescent : baseEnd_8040704 < baseStart_8040704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040771 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4]
def baseStart_8040771 : Nat := 118140960795 + 8040771 * 2 ^ 59
def prefixEnd_8040771 : Nat := 4983230072969 + 3 ^ 40 * 8040771 * 2
def baseEnd_8040771 : Nat := 4128780355733265180183673

theorem tailTrace_8040771 : CollatzResearch.WordTrace tailWord_8040771 prefixEnd_8040771 4128780355733265180183673 := by
  unfold tailWord_8040771
  simp only [CollatzResearch.WordTrace]
  refine ⟨293271011552667396201546167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195514007701778264134364111 293271011552667396201546167)
  ·
    refine ⟨439906517329001094302319251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293271011552667396201546167 439906517329001094302319251)
    ·
      refine ⟨659859775993501641453478877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439906517329001094302319251 659859775993501641453478877)
      ·
        refine ⟨247447415997563115545054579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659859775993501641453478877 247447415997563115545054579)
        ·
          refine ⟨371171123996344673317581869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247447415997563115545054579 371171123996344673317581869)
          ·
            refine ⟨139189171498629252494093201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371171123996344673317581869 139189171498629252494093201)
            ·
              refine ⟨104391878623971939370569901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139189171498629252494093201 104391878623971939370569901)
              ·
                refine ⟨39146954483989477263963713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104391878623971939370569901 39146954483989477263963713)
                ·
                  refine ⟨29360215862992107947972785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39146954483989477263963713 29360215862992107947972785)
                  ·
                    refine ⟨22020161897244080960979589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29360215862992107947972785 22020161897244080960979589)
                    ·
                      refine ⟨4128780355733265180183673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22020161897244080960979589 4128780355733265180183673)
                      ·
                        rfl

theorem cell23_8040771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_8040771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040771 prefixEnd_8040771 := by exact prefixLift 8040771
  have htrace : WordTrace (prefixWord ++ tailWord_8040771) baseStart_8040771 baseEnd_8040771 := by
    simpa [prefixWord, tailWord_8040771, baseEnd_8040771] using wordTrace_append hprefix tailTrace_8040771
  have hstable : (prefixWord ++ tailWord_8040771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040771).length < 2 ^ (prefixWord ++ tailWord_8040771).sum := by decide
  have hdescent : baseEnd_8040771 < baseStart_8040771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040796 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_8040796 : Nat := 118140960795 + 8040796 * 2 ^ 59
def prefixEnd_8040796 : Nat := 4983230072969 + 3 ^ 40 * 8040796 * 2
def baseEnd_8040796 : Nat := 4128793192749627582371059

theorem tailTrace_8040796 : CollatzResearch.WordTrace tailWord_8040796 prefixEnd_8040796 4128793192749627582371059 := by
  unfold tailWord_8040796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146635961688788412735603121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195514615585051216980804161 146635961688788412735603121)
  ·
    refine ⟨109976971266591309551702341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146635961688788412735603121 109976971266591309551702341)
    ·
      refine ⟨20620682112485870540944189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109976971266591309551702341 20620682112485870540944189)
      ·
        refine ⟨7732755792182201452854071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20620682112485870540944189 7732755792182201452854071)
        ·
          refine ⟨11599133688273302179281107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732755792182201452854071 11599133688273302179281107)
          ·
            refine ⟨17398700532409953268921661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599133688273302179281107 17398700532409953268921661)
            ·
              refine ⟨6524512699653732475845623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17398700532409953268921661 6524512699653732475845623)
              ·
                refine ⟨9786769049480598713768435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524512699653732475845623 9786769049480598713768435)
                ·
                  refine ⟨14680153574220898070652653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9786769049480598713768435 14680153574220898070652653)
                  ·
                    refine ⟨5505057590332836776494745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14680153574220898070652653 5505057590332836776494745)
                    ·
                      refine ⟨4128793192749627582371059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505057590332836776494745 4128793192749627582371059)
                      ·
                        rfl

theorem cell23_8040796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_8040796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040796 prefixEnd_8040796 := by exact prefixLift 8040796
  have htrace : WordTrace (prefixWord ++ tailWord_8040796) baseStart_8040796 baseEnd_8040796 := by
    simpa [prefixWord, tailWord_8040796, baseEnd_8040796] using wordTrace_append hprefix tailTrace_8040796
  have hstable : (prefixWord ++ tailWord_8040796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040796).length < 2 ^ (prefixWord ++ tailWord_8040796).sum := by decide
  have hdescent : baseEnd_8040796 < baseStart_8040796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040822 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_8040822 : Nat := 118140960795 + 8040822 * 2 ^ 59
def prefixEnd_8040822 : Nat := 4983230072969 + 3 ^ 40 * 8040822 * 2
def baseEnd_8040822 : Nat := 4128806543246644480645939

theorem tailTrace_8040822 : CollatzResearch.WordTrace tailWord_8040822 prefixEnd_8040822 4128806543246644480645939 := by
  unfold tailWord_8040822
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329554479717664494478295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195515247783655087941101813 18329554479717664494478295)
  ·
    refine ⟨27494331719576496741717443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18329554479717664494478295 27494331719576496741717443)
    ·
      refine ⟨41241497579364745112576165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27494331719576496741717443 41241497579364745112576165)
      ·
        refine ⟨7732780796130889708608031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41241497579364745112576165 7732780796130889708608031)
        ·
          refine ⟨11599171194196334562912047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732780796130889708608031 11599171194196334562912047)
          ·
            refine ⟨17398756791294501844368071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599171194196334562912047 17398756791294501844368071)
            ·
              refine ⟨26098135186941752766552107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17398756791294501844368071 26098135186941752766552107)
              ·
                refine ⟨39147202780412629149828161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26098135186941752766552107 39147202780412629149828161)
                ·
                  refine ⟨29360402085309471862371121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39147202780412629149828161 29360402085309471862371121)
                  ·
                    refine ⟨22020301563982103896778341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29360402085309471862371121 22020301563982103896778341)
                    ·
                      refine ⟨4128806543246644480645939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22020301563982103896778341 4128806543246644480645939)
                      ·
                        rfl

theorem cell23_8040822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_8040822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040822 prefixEnd_8040822 := by exact prefixLift 8040822
  have htrace : WordTrace (prefixWord ++ tailWord_8040822) baseStart_8040822 baseEnd_8040822 := by
    simpa [prefixWord, tailWord_8040822, baseEnd_8040822] using wordTrace_append hprefix tailTrace_8040822
  have hstable : (prefixWord ++ tailWord_8040822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040822).length < 2 ^ (prefixWord ++ tailWord_8040822).sum := by decide
  have hdescent : baseEnd_8040822 < baseStart_8040822 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040831 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4]
def baseStart_8040831 : Nat := 118140960795 + 8040831 * 2 ^ 59
def prefixEnd_8040831 : Nat := 4983230072969 + 3 ^ 40 * 8040831 * 2
def baseEnd_8040831 : Nat := 4128811164572534945433397

theorem tailTrace_8040831 : CollatzResearch.WordTrace tailWord_8040831 prefixEnd_8040831 4128811164572534945433397 := by
  unfold tailWord_8040831
  simp only [CollatzResearch.WordTrace]
  refine ⟨293273199932450026448730347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195515466621633350965820231 293273199932450026448730347)
  ·
    refine ⟨439909799898675039673095521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293273199932450026448730347 439909799898675039673095521)
    ·
      refine ⟨329932349924006279754821641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439909799898675039673095521 329932349924006279754821641)
      ·
        refine ⟨247449262443004709816116231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329932349924006279754821641 247449262443004709816116231)
        ·
          refine ⟨371173893664507064724174347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247449262443004709816116231 371173893664507064724174347)
          ·
            refine ⟨556760840496760597086261521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371173893664507064724174347 556760840496760597086261521)
            ·
              refine ⟨417570630372570447814696141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556760840496760597086261521 417570630372570447814696141)
              ·
                refine ⟨156588986389713917930511053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417570630372570447814696141 156588986389713917930511053)
                ·
                  refine ⟨58720869896142719223941645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156588986389713917930511053 58720869896142719223941645)
                  ·
                    refine ⟨22020326211053519708978117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58720869896142719223941645 22020326211053519708978117)
                    ·
                      refine ⟨4128811164572534945433397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22020326211053519708978117 4128811164572534945433397)
                      ·
                        rfl

theorem cell23_8040831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 4].length) (baseStart_8040831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040831 prefixEnd_8040831 := by exact prefixLift 8040831
  have htrace : WordTrace (prefixWord ++ tailWord_8040831) baseStart_8040831 baseEnd_8040831 := by
    simpa [prefixWord, tailWord_8040831, baseEnd_8040831] using wordTrace_append hprefix tailTrace_8040831
  have hstable : (prefixWord ++ tailWord_8040831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040831).length < 2 ^ (prefixWord ++ tailWord_8040831).sum := by decide
  have hdescent : baseEnd_8040831 < baseStart_8040831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040901 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_8040901 : Nat := 118140960795 + 8040901 * 2 ^ 59
def prefixEnd_8040901 : Nat := 4983230072969 + 3 ^ 40 * 8040901 * 2
def baseEnd_8040901 : Nat := 1376282369406116557186025

theorem tailTrace_8040901 : CollatzResearch.WordTrace tailWord_8040901 prefixEnd_8040901 1376282369406116557186025 := by
  unfold tailWord_8040901
  simp only [CollatzResearch.WordTrace]
  refine ⟨293275753042196428403778557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195517168694797618935852371 293275753042196428403778557)
  ·
    refine ⟨109978407390823660651416959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293275753042196428403778557 109978407390823660651416959)
    ·
      refine ⟨164967611086235490977125439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109978407390823660651416959 164967611086235490977125439)
      ·
        refine ⟨247451416629353236465688159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164967611086235490977125439 247451416629353236465688159)
        ·
          refine ⟨371177124944029854698532239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247451416629353236465688159 371177124944029854698532239)
          ·
            refine ⟨556765687416044782047798359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371177124944029854698532239 556765687416044782047798359)
            ·
              refine ⟨835148531124067173071697539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556765687416044782047798359 835148531124067173071697539)
              ·
                refine ⟨1252722796686100759607546309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835148531124067173071697539 1252722796686100759607546309)
                ·
                  refine ⟨234885524378643892426414933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1252722796686100759607546309 234885524378643892426414933)
                  ·
                    refine ⟨1376282369406116557186025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 234885524378643892426414933 1376282369406116557186025)
                    ·
                      rfl

theorem cell23_8040901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_8040901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040901 prefixEnd_8040901 := by exact prefixLift 8040901
  have htrace : WordTrace (prefixWord ++ tailWord_8040901) baseStart_8040901 baseEnd_8040901 := by
    simpa [prefixWord, tailWord_8040901, baseEnd_8040901] using wordTrace_append hprefix tailTrace_8040901
  have hstable : (prefixWord ++ tailWord_8040901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040901).length < 2 ^ (prefixWord ++ tailWord_8040901).sum := by decide
  have hdescent : baseEnd_8040901 < baseStart_8040901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040995 : List Nat := [1, 1, 1, 4, 4, 3, 1, 8]
def baseStart_8040995 : Nat := 118140960795 + 8040995 * 2 ^ 59
def prefixEnd_8040995 : Nat := 4983230072969 + 3 ^ 40 * 8040995 * 2
def baseEnd_8040995 : Nat := 152922050940736011251209

theorem tailTrace_8040995 : CollatzResearch.WordTrace tailWord_8040995 prefixEnd_8040995 152922050940736011251209 := by
  unfold tailWord_8040995
  simp only [CollatzResearch.WordTrace]
  refine ⟨293279181503855882457700439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195519454335903921638466959 293279181503855882457700439)
  ·
    refine ⟨439918772255783823686550659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293279181503855882457700439 439918772255783823686550659)
    ·
      refine ⟨659878158383675735529825989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439918772255783823686550659 659878158383675735529825989)
      ·
        refine ⟨123727154696939200411842373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659878158383675735529825989 123727154696939200411842373)
        ·
          refine ⟨23198841505676100077220445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123727154696939200411842373 23198841505676100077220445)
          ·
            refine ⟨8699565564628537528957667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23198841505676100077220445 8699565564628537528957667)
            ·
              refine ⟨13049348346942806293436501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8699565564628537528957667 13049348346942806293436501)
              ·
                refine ⟨152922050940736011251209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13049348346942806293436501 152922050940736011251209)
                ·
                  rfl

theorem cell23_8040995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 8].length) (baseStart_8040995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040995 prefixEnd_8040995 := by exact prefixLift 8040995
  have htrace : WordTrace (prefixWord ++ tailWord_8040995) baseStart_8040995 baseEnd_8040995 := by
    simpa [prefixWord, tailWord_8040995, baseEnd_8040995] using wordTrace_append hprefix tailTrace_8040995
  have hstable : (prefixWord ++ tailWord_8040995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040995).length < 2 ^ (prefixWord ++ tailWord_8040995).sum := by decide
  have hdescent : baseEnd_8040995 < baseStart_8040995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8040999 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 6]
def baseStart_8040999 : Nat := 118140960795 + 8040999 * 2 ^ 59
def prefixEnd_8040999 : Nat := 4983230072969 + 3 ^ 40 * 8040999 * 2
def baseEnd_8040999 : Nat := 1376299143107496762710875

theorem tailTrace_8040999 : CollatzResearch.WordTrace tailWord_8040999 prefixEnd_8040999 1376299143107496762710875 := by
  unfold tailWord_8040999
  simp only [CollatzResearch.WordTrace]
  refine ⟨293279327395841391140846051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195519551597227594093897367 293279327395841391140846051)
  ·
    refine ⟨439918991093762086711269077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293279327395841391140846051 439918991093762086711269077)
    ·
      refine ⟨10310601353760048907295369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 439918991093762086711269077 10310601353760048907295369)
      ·
        refine ⟨7732951015320036680471527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10310601353760048907295369 7732951015320036680471527)
        ·
          refine ⟨11599426522980055020707291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7732951015320036680471527 11599426522980055020707291)
          ·
            refine ⟨17399139784470082531060937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599426522980055020707291 17399139784470082531060937)
            ·
              refine ⟨13049354838352561898295703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17399139784470082531060937 13049354838352561898295703)
              ·
                refine ⟨19574032257528842847443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13049354838352561898295703 19574032257528842847443555)
                ·
                  refine ⟨29361048386293264271165333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19574032257528842847443555 29361048386293264271165333)
                  ·
                    refine ⟨1376299143107496762710875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29361048386293264271165333 1376299143107496762710875)
                    ·
                      rfl

theorem cell23_8040999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_8040999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8040999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8040999 prefixEnd_8040999 := by exact prefixLift 8040999
  have htrace : WordTrace (prefixWord ++ tailWord_8040999) baseStart_8040999 baseEnd_8040999 := by
    simpa [prefixWord, tailWord_8040999, baseEnd_8040999] using wordTrace_append hprefix tailTrace_8040999
  have hstable : (prefixWord ++ tailWord_8040999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8040999).length < 2 ^ (prefixWord ++ tailWord_8040999).sum := by decide
  have hdescent : baseEnd_8040999 < baseStart_8040999 := by decide
  rcases family_descends (prefixWord ++ tailWord_8040999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041002 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_8041002 : Nat := 118140960795 + 8041002 * 2 ^ 59
def prefixEnd_8041002 : Nat := 4983230072969 + 3 ^ 40 * 8041002 * 2
def baseEnd_8041002 : Nat := 4128898969764453776395111

theorem tailTrace_8041002 : CollatzResearch.WordTrace tailWord_8041002 prefixEnd_8041002 4128898969764453776395111 := by
  unfold tailWord_8041002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73319859203707630663301315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195519624543220348435470173 73319859203707630663301315)
  ·
    refine ⟨109979788805561445994951973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73319859203707630663301315 109979788805561445994951973)
    ·
      refine ⟨20621210401042771124053495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 109979788805561445994951973 20621210401042771124053495)
      ·
        refine ⟨30931815601564156686080243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20621210401042771124053495 30931815601564156686080243)
        ·
          refine ⟨46397723402346235029120365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30931815601564156686080243 46397723402346235029120365)
          ·
            refine ⟨17399146275879838135920137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46397723402346235029120365 17399146275879838135920137)
            ·
              refine ⟨13049359706909878601940103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17399146275879838135920137 13049359706909878601940103)
              ·
                refine ⟨19574039560364817902910155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13049359706909878601940103 19574039560364817902910155)
                ·
                  refine ⟨29361059340547226854365233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19574039560364817902910155 29361059340547226854365233)
                  ·
                    refine ⟨22020794505410420140773925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29361059340547226854365233 22020794505410420140773925)
                    ·
                      refine ⟨4128898969764453776395111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22020794505410420140773925 4128898969764453776395111)
                      ·
                        rfl

theorem cell23_8041002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_8041002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041002 prefixEnd_8041002 := by exact prefixLift 8041002
  have htrace : WordTrace (prefixWord ++ tailWord_8041002) baseStart_8041002 baseEnd_8041002 := by
    simpa [prefixWord, tailWord_8041002, baseEnd_8041002] using wordTrace_append hprefix tailTrace_8041002
  have hstable : (prefixWord ++ tailWord_8041002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041002).length < 2 ^ (prefixWord ++ tailWord_8041002).sum := by decide
  have hdescent : baseEnd_8041002 < baseStart_8041002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041006 : List Nat := [4, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_8041006 : Nat := 118140960795 + 8041006 * 2 ^ 59
def prefixEnd_8041006 : Nat := 4983230072969 + 3 ^ 40 * 8041006 * 2
def baseEnd_8041006 : Nat := 4128901023687071760745093

theorem tailTrace_8041006 : CollatzResearch.WordTrace tailWord_8041006 prefixEnd_8041006 4128901023687071760745093 := by
  unfold tailWord_8041006
  simp only [CollatzResearch.WordTrace]
  refine ⟨36659947838352003917043859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195519721804544020890900581 36659947838352003917043859)
  ·
    refine ⟨54989921757528005875565789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36659947838352003917043859 54989921757528005875565789)
    ·
      refine ⟨20621220659073002203337171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54989921757528005875565789 20621220659073002203337171)
      ·
        refine ⟨30931830988609503305005757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20621220659073002203337171 30931830988609503305005757)
        ·
          refine ⟨11599436620728563739377159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30931830988609503305005757 11599436620728563739377159)
          ·
            refine ⟨17399154931092845609065739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11599436620728563739377159 17399154931092845609065739)
            ·
              refine ⟨26098732396639268413598609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17399154931092845609065739 26098732396639268413598609)
              ·
                refine ⟨19574049297479451310198957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26098732396639268413598609 19574049297479451310198957)
                ·
                  refine ⟨7340268486554794241324609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19574049297479451310198957 7340268486554794241324609)
                  ·
                    refine ⟨5505201364916095680993457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7340268486554794241324609 5505201364916095680993457)
                    ·
                      refine ⟨4128901023687071760745093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505201364916095680993457 4128901023687071760745093)
                      ·
                        rfl

theorem cell23_8041006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_8041006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041006 prefixEnd_8041006 := by exact prefixLift 8041006
  have htrace : WordTrace (prefixWord ++ tailWord_8041006) baseStart_8041006 baseEnd_8041006 := by
    simpa [prefixWord, tailWord_8041006, baseEnd_8041006] using wordTrace_append hprefix tailTrace_8041006
  have hstable : (prefixWord ++ tailWord_8041006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041006).length < 2 ^ (prefixWord ++ tailWord_8041006).sum := by decide
  have hdescent : baseEnd_8041006 < baseStart_8041006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041152 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_8041152 : Nat := 118140960795 + 8041152 * 2 ^ 59
def prefixEnd_8041152 : Nat := 4983230072969 + 3 ^ 40 * 8041152 * 2
def baseEnd_8041152 : Nat := 4128975991862628189519421

theorem tailTrace_8041152 : CollatzResearch.WordTrace tailWord_8041152 prefixEnd_8041152 4128975991862628189519421 := by
  unfold tailWord_8041152
  simp only [CollatzResearch.WordTrace]
  refine ⟨146642453882143549135582855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195523271842858065514110473 146642453882143549135582855)
  ·
    refine ⟨219963680823215323703374283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146642453882143549135582855 219963680823215323703374283)
    ·
      refine ⟨329945521234822985555061425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219963680823215323703374283 329945521234822985555061425)
      ·
        refine ⟨247459140926117239166296069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329945521234822985555061425 247459140926117239166296069)
        ·
          refine ⟨46398588923646982343680513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247459140926117239166296069 46398588923646982343680513)
          ·
            refine ⟨34798941692735236757760385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46398588923646982343680513 34798941692735236757760385)
            ·
              refine ⟨26099206269551427568320289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34798941692735236757760385 26099206269551427568320289)
              ·
                refine ⟨19574404702163570676240217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26099206269551427568320289 19574404702163570676240217)
                ·
                  refine ⟨14680803526622678007180163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19574404702163570676240217 14680803526622678007180163)
                  ·
                    refine ⟨22021205289934017010770245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14680803526622678007180163 22021205289934017010770245)
                    ·
                      refine ⟨4128975991862628189519421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22021205289934017010770245 4128975991862628189519421)
                      ·
                        rfl

theorem cell23_8041152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_8041152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041152 prefixEnd_8041152 := by exact prefixLift 8041152
  have htrace : WordTrace (prefixWord ++ tailWord_8041152) baseStart_8041152 baseEnd_8041152 := by
    simpa [prefixWord, tailWord_8041152, baseEnd_8041152] using wordTrace_append hprefix tailTrace_8041152
  have hstable : (prefixWord ++ tailWord_8041152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041152).length < 2 ^ (prefixWord ++ tailWord_8041152).sum := by decide
  have hdescent : baseEnd_8041152 < baseStart_8041152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041189 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 3]
def baseStart_8041189 : Nat := 118140960795 + 8041189 * 2 ^ 59
def prefixEnd_8041189 : Nat := 4983230072969 + 3 ^ 40 * 8041189 * 2
def baseEnd_8041189 : Nat := 4128994990646844544756751

theorem tailTrace_8041189 : CollatzResearch.WordTrace tailWord_8041189 prefixEnd_8041189 4128994990646844544756751 := by
  unfold tailWord_8041189
  simp only [CollatzResearch.WordTrace]
  refine ⟨293286257265153053590262621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195524171510102035726841747 293286257265153053590262621)
  ·
    refine ⟨109982346474432395096348483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293286257265153053590262621 109982346474432395096348483)
    ·
      refine ⟨164973519711648592644522725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109982346474432395096348483 164973519711648592644522725)
      ·
        refine ⟨30932534945934111120848011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 164973519711648592644522725 30932534945934111120848011)
        ·
          refine ⟨46398802418901166681272017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30932534945934111120848011 46398802418901166681272017)
          ·
            refine ⟨34799101814175875010954013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46398802418901166681272017 34799101814175875010954013)
            ·
              refine ⟨13049663180315953129107755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34799101814175875010954013 13049663180315953129107755)
              ·
                refine ⟨19574494770473929693661633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13049663180315953129107755 19574494770473929693661633)
                ·
                  refine ⟨14680871077855447270246225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19574494770473929693661633 14680871077855447270246225)
                  ·
                    refine ⟨11010653308391585452684669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14680871077855447270246225 11010653308391585452684669)
                    ·
                      refine ⟨4128994990646844544756751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11010653308391585452684669 4128994990646844544756751)
                      ·
                        rfl

theorem cell23_8041189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_8041189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041189 prefixEnd_8041189 := by exact prefixLift 8041189
  have htrace : WordTrace (prefixWord ++ tailWord_8041189) baseStart_8041189 baseEnd_8041189 := by
    simpa [prefixWord, tailWord_8041189, baseEnd_8041189] using wordTrace_append hprefix tailTrace_8041189
  have hstable : (prefixWord ++ tailWord_8041189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041189).length < 2 ^ (prefixWord ++ tailWord_8041189).sum := by decide
  have hdescent : baseEnd_8041189 < baseStart_8041189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041259 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 7, 2, 2]
def baseStart_8041259 : Nat := 118140960795 + 8041259 * 2 ^ 59
def prefixEnd_8041259 : Nat := 4983230072969 + 3 ^ 40 * 8041259 * 2
def baseEnd_8041259 : Nat := 4129030934292659270881429

theorem tailTrace_8041259 : CollatzResearch.WordTrace tailWord_8041259 prefixEnd_8041259 4129030934292659270881429 := by
  unfold tailWord_8041259
  simp only [CollatzResearch.WordTrace]
  refine ⟨293288810374899455545310831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195525873583266303696873887 293288810374899455545310831)
  ·
    refine ⟨439933215562349183317966247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293288810374899455545310831 439933215562349183317966247)
    ·
      refine ⟨659899823343523774976949371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439933215562349183317966247 659899823343523774976949371)
      ·
        refine ⟨989849735015285662465424057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659899823343523774976949371 989849735015285662465424057)
        ·
          refine ⟨742387301261464246849068043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989849735015285662465424057 742387301261464246849068043)
          ·
            refine ⟨1113580951892196370273602065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742387301261464246849068043 1113580951892196370273602065)
            ·
              refine ⟨835185713919147277705201549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113580951892196370273602065 835185713919147277705201549)
              ·
                refine ⟨313194642719680229139450581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835185713919147277705201549 313194642719680229139450581)
                ·
                  refine ⟨7340499438742505370455873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 313194642719680229139450581 7340499438742505370455873)
                  ·
                    refine ⟨5505374579056879027841905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7340499438742505370455873 5505374579056879027841905)
                    ·
                      refine ⟨4129030934292659270881429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505374579056879027841905 4129030934292659270881429)
                      ·
                        rfl

theorem cell23_8041259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 2, 2].length) (baseStart_8041259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041259 prefixEnd_8041259 := by exact prefixLift 8041259
  have htrace : WordTrace (prefixWord ++ tailWord_8041259) baseStart_8041259 baseEnd_8041259 := by
    simpa [prefixWord, tailWord_8041259, baseEnd_8041259] using wordTrace_append hprefix tailTrace_8041259
  have hstable : (prefixWord ++ tailWord_8041259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041259).length < 2 ^ (prefixWord ++ tailWord_8041259).sum := by decide
  have hdescent : baseEnd_8041259 < baseStart_8041259 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041269 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_8041269 : Nat := 118140960795 + 8041269 * 2 ^ 59
def prefixEnd_8041269 : Nat := 4983230072969 + 3 ^ 40 * 8041269 * 2
def baseEnd_8041269 : Nat := 1376345356366401410585461

theorem tailTrace_8041269 : CollatzResearch.WordTrace tailWord_8041269 prefixEnd_8041269 1376345356366401410585461 := by
  unfold tailWord_8041269
  simp only [CollatzResearch.WordTrace]
  refine ⟨293289175104863227253174861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195526116736575484835449907 293289175104863227253174861)
  ·
    refine ⟨109983440664323710219940573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293289175104863227253174861 109983440664323710219940573)
    ·
      refine ⟨41243790249121391332477715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109983440664323710219940573 41243790249121391332477715)
      ·
        refine ⟨61865685373682086998716573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41243790249121391332477715 61865685373682086998716573)
        ·
          refine ⟨23199632015130782624518715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61865685373682086998716573 23199632015130782624518715)
          ·
            refine ⟨34799448022696173936778073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23199632015130782624518715 34799448022696173936778073)
            ·
              refine ⟨26099586017022130452583555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34799448022696173936778073 26099586017022130452583555)
              ·
                refine ⟨39149379025533195678875333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26099586017022130452583555 39149379025533195678875333)
                ·
                  refine ⟨7340508567287474189789125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39149379025533195678875333 7340508567287474189789125)
                  ·
                    refine ⟨1376345356366401410585461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7340508567287474189789125 1376345356366401410585461)
                    ·
                      rfl

theorem cell23_8041269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_8041269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041269 prefixEnd_8041269 := by exact prefixLift 8041269
  have htrace : WordTrace (prefixWord ++ tailWord_8041269) baseStart_8041269 baseEnd_8041269 := by
    simpa [prefixWord, tailWord_8041269, baseEnd_8041269] using wordTrace_append hprefix tailTrace_8041269
  have hstable : (prefixWord ++ tailWord_8041269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041269).length < 2 ^ (prefixWord ++ tailWord_8041269).sum := by decide
  have hdescent : baseEnd_8041269 < baseStart_8041269 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041270 : List Nat := [5, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_8041270 : Nat := 118140960795 + 8041270 * 2 ^ 59
def prefixEnd_8041270 : Nat := 4983230072969 + 3 ^ 40 * 8041270 * 2
def baseEnd_8041270 : Nat := 4129036582579858727843879

theorem tailTrace_8041270 : CollatzResearch.WordTrace tailWord_8041270 prefixEnd_8041270 4129036582579858727843879 := by
  unfold tailWord_8041270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330575723616225276497579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195526141051906402949307509 18330575723616225276497579)
  ·
    refine ⟨27495863585424337914746369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18330575723616225276497579 27495863585424337914746369)
    ·
      refine ⟨20621897689068253436059777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27495863585424337914746369 20621897689068253436059777)
      ·
        refine ⟨15466423266801190077044833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20621897689068253436059777 15466423266801190077044833)
        ·
          refine ⟨11599817450100892557783625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15466423266801190077044833 11599817450100892557783625)
          ·
            refine ⟨8699863087575669418337719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11599817450100892557783625 8699863087575669418337719)
            ·
              refine ⟨13049794631363504127506579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8699863087575669418337719 13049794631363504127506579)
              ·
                refine ⟨19574691947045256191259869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13049794631363504127506579 19574691947045256191259869)
                ·
                  refine ⟨7340509480141971071722451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19574691947045256191259869 7340509480141971071722451)
                  ·
                    refine ⟨11010764220212956607583677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340509480141971071722451 11010764220212956607583677)
                    ·
                      refine ⟨4129036582579858727843879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11010764220212956607583677 4129036582579858727843879)
                      ·
                        rfl

theorem cell23_8041270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_8041270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041270 prefixEnd_8041270 := by exact prefixLift 8041270
  have htrace : WordTrace (prefixWord ++ tailWord_8041270) baseStart_8041270 baseEnd_8041270 := by
    simpa [prefixWord, tailWord_8041270, baseEnd_8041270] using wordTrace_append hprefix tailTrace_8041270
  have hstable : (prefixWord ++ tailWord_8041270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041270).length < 2 ^ (prefixWord ++ tailWord_8041270).sum := by decide
  have hdescent : baseEnd_8041270 < baseStart_8041270 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041399 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3]
def baseStart_8041399 : Nat := 118140960795 + 8041399 * 2 ^ 59
def prefixEnd_8041399 : Nat := 4983230072969 + 3 ^ 40 * 8041399 * 2
def baseEnd_8041399 : Nat := 4129102821584288723130785

theorem tailTrace_8041399 : CollatzResearch.WordTrace tailWord_8041399 prefixEnd_8041399 4129102821584288723130785 := by
  unfold tailWord_8041399
  simp only [CollatzResearch.WordTrace]
  refine ⟨293293916594392259455407251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195529277729594839636938167 293293916594392259455407251)
  ·
    refine ⟨439940874891588389183110877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293293916594392259455407251 439940874891588389183110877)
    ·
      refine ⟨164977828084345645943666579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439940874891588389183110877 164977828084345645943666579)
      ·
        refine ⟨247466742126518468915499869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164977828084345645943666579 247466742126518468915499869)
        ·
          refine ⟨92800028297444425843312451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247466742126518468915499869 92800028297444425843312451)
          ·
            refine ⟨139200042446166638764968677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92800028297444425843312451 139200042446166638764968677)
            ·
              refine ⟨26100007958656244768431627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139200042446166638764968677 26100007958656244768431627)
              ·
                refine ⟨39150011937984367152647441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26100007958656244768431627 39150011937984367152647441)
                ·
                  refine ⟨29362508953488275364485581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39150011937984367152647441 29362508953488275364485581)
                  ·
                    refine ⟨11010940857558103261682093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29362508953488275364485581 11010940857558103261682093)
                    ·
                      refine ⟨4129102821584288723130785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11010940857558103261682093 4129102821584288723130785)
                      ·
                        rfl

theorem cell23_8041399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_8041399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041399 prefixEnd_8041399 := by exact prefixLift 8041399
  have htrace : WordTrace (prefixWord ++ tailWord_8041399) baseStart_8041399 baseEnd_8041399 := by
    simpa [prefixWord, tailWord_8041399, baseEnd_8041399] using wordTrace_append hprefix tailTrace_8041399
  have hstable : (prefixWord ++ tailWord_8041399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041399).length < 2 ^ (prefixWord ++ tailWord_8041399).sum := by decide
  have hdescent : baseEnd_8041399 < baseStart_8041399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041400 : List Nat := [2, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_8041400 : Nat := 118140960795 + 8041400 * 2 ^ 59
def prefixEnd_8041400 : Nat := 4983230072969 + 3 ^ 40 * 8041400 * 2
def baseEnd_8041400 : Nat := 4129103335064943219218281

theorem tailTrace_8041400 : CollatzResearch.WordTrace tailWord_8041400 prefixEnd_8041400 4129103335064943219218281 := by
  unfold tailWord_8041400
  simp only [CollatzResearch.WordTrace]
  refine ⟨146646976533694318313096827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195529302044925757750795769 146646976533694318313096827)
  ·
    refine ⟨219970464800541477469645241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146646976533694318313096827 219970464800541477469645241)
    ·
      refine ⟨164977848600406108102233931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219970464800541477469645241 164977848600406108102233931)
      ·
        refine ⟨247466772900609162153350897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164977848600406108102233931 247466772900609162153350897)
        ·
          refine ⟨185600079675456871615013173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247466772900609162153350897 185600079675456871615013173)
          ·
            refine ⟨17400007469574081713907485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185600079675456871615013173 17400007469574081713907485)
            ·
              refine ⟨6525002801090280642715307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17400007469574081713907485 6525002801090280642715307)
              ·
                refine ⟨9787504201635420964072961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525002801090280642715307 9787504201635420964072961)
                ·
                  refine ⟨7340628151226565723054721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9787504201635420964072961 7340628151226565723054721)
                  ·
                    refine ⟨5505471113419924292291041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7340628151226565723054721 5505471113419924292291041)
                    ·
                      refine ⟨4129103335064943219218281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505471113419924292291041 4129103335064943219218281)
                      ·
                        rfl

theorem cell23_8041400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_8041400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041400 prefixEnd_8041400 := by exact prefixLift 8041400
  have htrace : WordTrace (prefixWord ++ tailWord_8041400) baseStart_8041400 baseEnd_8041400 := by
    simpa [prefixWord, tailWord_8041400, baseEnd_8041400] using wordTrace_append hprefix tailTrace_8041400
  have hstable : (prefixWord ++ tailWord_8041400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041400).length < 2 ^ (prefixWord ++ tailWord_8041400).sum := by decide
  have hdescent : baseEnd_8041400 < baseStart_8041400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041402 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_8041402 : Nat := 118140960795 + 8041402 * 2 ^ 59
def prefixEnd_8041402 : Nat := 4983230072969 + 3 ^ 40 * 8041402 * 2
def baseEnd_8041402 : Nat := 1376368120675417403797757

theorem tailTrace_8041402 : CollatzResearch.WordTrace tailWord_8041402 prefixEnd_8041402 1376368120675417403797757 := by
  unfold tailWord_8041402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73323506503345347741941615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195529350675587593978510973 73323506503345347741941615)
  ·
    refine ⟨109985259755018021612912423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73323506503345347741941615 109985259755018021612912423)
    ·
      refine ⟨164977889632527032419368635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109985259755018021612912423 164977889632527032419368635)
      ·
        refine ⟨247466834448790548629052953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164977889632527032419368635 247466834448790548629052953)
        ·
          refine ⟨185600125836592911471789715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247466834448790548629052953 185600125836592911471789715)
          ·
            refine ⟨278400188754889367207684573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185600125836592911471789715 278400188754889367207684573)
            ·
              refine ⟨104400070783083512702881715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278400188754889367207684573 104400070783083512702881715)
              ·
                refine ⟨156600106174625269054322573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104400070783083512702881715 156600106174625269054322573)
                ·
                  refine ⟨58725039815484475895370965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156600106174625269054322573 58725039815484475895370965)
                  ·
                    refine ⟨1376368120675417403797757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58725039815484475895370965 1376368120675417403797757)
                    ·
                      rfl

theorem cell23_8041402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_8041402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041402 prefixEnd_8041402 := by exact prefixLift 8041402
  have htrace : WordTrace (prefixWord ++ tailWord_8041402) baseStart_8041402 baseEnd_8041402 := by
    simpa [prefixWord, tailWord_8041402, baseEnd_8041402] using wordTrace_append hprefix tailTrace_8041402
  have hstable : (prefixWord ++ tailWord_8041402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041402).length < 2 ^ (prefixWord ++ tailWord_8041402).sum := by decide
  have hdescent : baseEnd_8041402 < baseStart_8041402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041496 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 6]
def baseStart_8041496 : Nat := 118140960795 + 8041496 * 2 ^ 59
def prefixEnd_8041496 : Nat := 4983230072969 + 3 ^ 40 * 8041496 * 2
def baseEnd_8041496 : Nat := 458794736578641649290871

theorem tailTrace_8041496 : CollatzResearch.WordTrace tailWord_8041496 prefixEnd_8041496 458794736578641649290871 := by
  unfold tailWord_8041496
  simp only [CollatzResearch.WordTrace]
  refine ⟨146648727237520422510844171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195531636316693896681125561 146648727237520422510844171)
  ·
    refine ⟨219973090856280633766266257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146648727237520422510844171 219973090856280633766266257)
    ·
      refine ⟨164979818142210475324699693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 219973090856280633766266257 164979818142210475324699693)
      ·
        refine ⟨61867431803328928246762385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164979818142210475324699693 61867431803328928246762385)
        ·
          refine ⟨46400573852496696185071789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61867431803328928246762385 46400573852496696185071789)
          ·
            refine ⟨17400215194686261069401921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46400573852496696185071789 17400215194686261069401921)
            ·
              refine ⟨13050161396014695802051441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17400215194686261069401921 13050161396014695802051441)
              ·
                refine ⟨9787621047011021851538581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13050161396014695802051441 9787621047011021851538581)
                ·
                  refine ⟨458794736578641649290871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9787621047011021851538581 458794736578641649290871)
                  ·
                    rfl

theorem cell23_8041496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_8041496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041496 prefixEnd_8041496 := by exact prefixLift 8041496
  have htrace : WordTrace (prefixWord ++ tailWord_8041496) baseStart_8041496 baseEnd_8041496 := by
    simpa [prefixWord, tailWord_8041496, baseEnd_8041496] using wordTrace_append hprefix tailTrace_8041496
  have hstable : (prefixWord ++ tailWord_8041496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041496).length < 2 ^ (prefixWord ++ tailWord_8041496).sum := by decide
  have hdescent : baseEnd_8041496 < baseStart_8041496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041500 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_8041500 : Nat := 118140960795 + 8041500 * 2 ^ 59
def prefixEnd_8041500 : Nat := 4983230072969 + 3 ^ 40 * 8041500 * 2
def baseEnd_8041500 : Nat := 1376384894376797609322607

theorem tailTrace_8041500 : CollatzResearch.WordTrace tailWord_8041500 prefixEnd_8041500 1376384894376797609322607 := by
  unfold tailWord_8041500
  simp only [CollatzResearch.WordTrace]
  refine ⟨146648800183513176852416977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195531733578017569136555969 146648800183513176852416977)
  ·
    refine ⟨109986600137634882639312733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146648800183513176852416977 109986600137634882639312733)
    ·
      refine ⟨41244975051613080989742275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109986600137634882639312733 41244975051613080989742275)
      ·
        refine ⟨61867462577419621484613413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41244975051613080989742275 61867462577419621484613413)
        ·
          refine ⟨11600149233266179028365015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61867462577419621484613413 11600149233266179028365015)
          ·
            refine ⟨17400223849899268542547523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600149233266179028365015 17400223849899268542547523)
            ·
              refine ⟨26100335774848902813821285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17400223849899268542547523 26100335774848902813821285)
              ·
                refine ⟨4893812957784169277591491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26100335774848902813821285 4893812957784169277591491)
                ·
                  refine ⟨7340719436676253916387237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893812957784169277591491 7340719436676253916387237)
                  ·
                    refine ⟨1376384894376797609322607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7340719436676253916387237 1376384894376797609322607)
                    ·
                      rfl

theorem cell23_8041500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_8041500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041500 prefixEnd_8041500 := by exact prefixLift 8041500
  have htrace : WordTrace (prefixWord ++ tailWord_8041500) baseStart_8041500 baseEnd_8041500 := by
    simpa [prefixWord, tailWord_8041500, baseEnd_8041500] using wordTrace_append hprefix tailTrace_8041500
  have hstable : (prefixWord ++ tailWord_8041500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041500).length < 2 ^ (prefixWord ++ tailWord_8041500).sum := by decide
  have hdescent : baseEnd_8041500 < baseStart_8041500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041509 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_8041509 : Nat := 118140960795 + 8041509 * 2 ^ 59
def prefixEnd_8041509 : Nat := 4983230072969 + 3 ^ 40 * 8041509 * 2
def baseEnd_8041509 : Nat := 1376386434818761097585093

theorem tailTrace_8041509 : CollatzResearch.WordTrace tailWord_8041509 prefixEnd_8041509 1376386434818761097585093 := by
  unfold tailWord_8041509
  simp only [CollatzResearch.WordTrace]
  refine ⟨293297928623993748241911581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195531952415995832161274387 293297928623993748241911581)
  ·
    refine ⟨109986723233997655590716843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293297928623993748241911581 109986723233997655590716843)
    ·
      refine ⟨164980084850996483386075265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109986723233997655590716843 164980084850996483386075265)
      ·
        refine ⟨123735063638247362539556449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164980084850996483386075265 123735063638247362539556449)
        ·
          refine ⟨92801297728685521904667337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123735063638247362539556449 92801297728685521904667337)
          ·
            refine ⟨69600973296514141428500503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92801297728685521904667337 69600973296514141428500503)
            ·
              refine ⟨104401459944771212142750755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69600973296514141428500503 104401459944771212142750755)
              ·
                refine ⟨156602189917156818214126133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104401459944771212142750755 156602189917156818214126133)
                ·
                  refine ⟨14681455304733451707574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156602189917156818214126133 14681455304733451707574325)
                  ·
                    refine ⟨1376386434818761097585093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14681455304733451707574325 1376386434818761097585093)
                    ·
                      rfl

theorem cell23_8041509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_8041509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041509 prefixEnd_8041509 := by exact prefixLift 8041509
  have htrace : WordTrace (prefixWord ++ tailWord_8041509) baseStart_8041509 baseEnd_8041509 := by
    simpa [prefixWord, tailWord_8041509, baseEnd_8041509] using wordTrace_append hprefix tailTrace_8041509
  have hstable : (prefixWord ++ tailWord_8041509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041509).length < 2 ^ (prefixWord ++ tailWord_8041509).sum := by decide
  have hdescent : baseEnd_8041509 < baseStart_8041509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041516 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_8041516 : Nat := 118140960795 + 8041516 * 2 ^ 59
def prefixEnd_8041516 : Nat := 4983230072969 + 3 ^ 40 * 8041516 * 2
def baseEnd_8041516 : Nat := 4129162898820864765367747

theorem tailTrace_8041516 : CollatzResearch.WordTrace tailWord_8041516 prefixEnd_8041516 4129162898820864765367747 := by
  unfold tailWord_8041516
  simp only [CollatzResearch.WordTrace]
  refine ⟨146649091967484194218708201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195532122623312258958277601 146649091967484194218708201)
  ·
    refine ⟨109986818975613145664031151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146649091967484194218708201 109986818975613145664031151)
    ·
      refine ⟨164980228463419718496046727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109986818975613145664031151 164980228463419718496046727)
      ·
        refine ⟨247470342695129577744070091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164980228463419718496046727 247470342695129577744070091)
        ·
          refine ⟨371205514042694366616105137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247470342695129577744070091 371205514042694366616105137)
          ·
            refine ⟨278404135532020774962078853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371205514042694366616105137 278404135532020774962078853)
            ·
              refine ⟨52200775412253895305389785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278404135532020774962078853 52200775412253895305389785)
              ·
                refine ⟨39150581559190421479042339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52200775412253895305389785 39150581559190421479042339)
                ·
                  refine ⟨58725872338785632218563509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39150581559190421479042339 58725872338785632218563509)
                  ·
                    refine ⟨5505550531761153020490329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58725872338785632218563509 5505550531761153020490329)
                    ·
                      refine ⟨4129162898820864765367747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505550531761153020490329 4129162898820864765367747)
                      ·
                        rfl

theorem cell23_8041516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_8041516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041516 prefixEnd_8041516 := by exact prefixLift 8041516
  have htrace : WordTrace (prefixWord ++ tailWord_8041516) baseStart_8041516 baseEnd_8041516 := by
    simpa [prefixWord, tailWord_8041516, baseEnd_8041516] using wordTrace_append hprefix tailTrace_8041516
  have hstable : (prefixWord ++ tailWord_8041516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041516).length < 2 ^ (prefixWord ++ tailWord_8041516).sum := by decide
  have hdescent : baseEnd_8041516 < baseStart_8041516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041533 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 1, 5, 2]
def baseStart_8041533 : Nat := 118140960795 + 8041533 * 2 ^ 59
def prefixEnd_8041533 : Nat := 4983230072969 + 3 ^ 40 * 8041533 * 2
def baseEnd_8041533 : Nat := 4129171627991991198855169

theorem tailTrace_8041533 : CollatzResearch.WordTrace tailWord_8041533 prefixEnd_8041533 4129171627991991198855169 := by
  unfold tailWord_8041533
  simp only [CollatzResearch.WordTrace]
  refine ⟨293298803975906800340785253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195532535983937866893856835 293298803975906800340785253)
  ·
    refine ⟨54993525745482525063897235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293298803975906800340785253 54993525745482525063897235)
    ·
      refine ⟨82490288618223787595845853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54993525745482525063897235 82490288618223787595845853)
      ·
        refine ⟨30933858231833920348442195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82490288618223787595845853 30933858231833920348442195)
        ·
          refine ⟨46400787347750880522663293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30933858231833920348442195 46400787347750880522663293)
          ·
            refine ⟨17400295255406580195998735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46400787347750880522663293 17400295255406580195998735)
            ·
              refine ⟨26100442883109870293998103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17400295255406580195998735 26100442883109870293998103)
              ·
                refine ⟨39150664324664805440997155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26100442883109870293998103 39150664324664805440997155)
                ·
                  refine ⟨58725996486997208161495733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39150664324664805440997155 58725996486997208161495733)
                  ·
                    refine ⟨5505562170655988265140225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58725996486997208161495733 5505562170655988265140225)
                    ·
                      refine ⟨4129171627991991198855169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505562170655988265140225 4129171627991991198855169)
                      ·
                        rfl

theorem cell23_8041533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_8041533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041533 prefixEnd_8041533 := by exact prefixLift 8041533
  have htrace : WordTrace (prefixWord ++ tailWord_8041533) baseStart_8041533 baseEnd_8041533 := by
    simpa [prefixWord, tailWord_8041533, baseEnd_8041533] using wordTrace_append hprefix tailTrace_8041533
  have hstable : (prefixWord ++ tailWord_8041533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041533).length < 2 ^ (prefixWord ++ tailWord_8041533).sum := by decide
  have hdescent : baseEnd_8041533 < baseStart_8041533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041539 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 6]
def baseStart_8041539 : Nat := 118140960795 + 8041539 * 2 ^ 59
def prefixEnd_8041539 : Nat := 4983230072969 + 3 ^ 40 * 8041539 * 2
def baseEnd_8041539 : Nat := 1376391569625306058460047

theorem tailTrace_8041539 : CollatzResearch.WordTrace tailWord_8041539 prefixEnd_8041539 1376391569625306058460047 := by
  unfold tailWord_8041539
  simp only [CollatzResearch.WordTrace]
  refine ⟨293299022813885063365503671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195532681875923375577002447 293299022813885063365503671)
  ·
    refine ⟨439948534220827595048255507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293299022813885063365503671 439948534220827595048255507)
    ·
      refine ⟨659922801331241392572383261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439948534220827595048255507 659922801331241392572383261)
      ·
        refine ⟨247471050499215522214643723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659922801331241392572383261 247471050499215522214643723)
        ·
          refine ⟨371206575748823283321965585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247471050499215522214643723 371206575748823283321965585)
          ·
            refine ⟨278404931811617462491474189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371206575748823283321965585 278404931811617462491474189)
            ·
              refine ⟨104401849429356548434302821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278404931811617462491474189 104401849429356548434302821)
              ·
                refine ⟨19575346768004352831431779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104401849429356548434302821 19575346768004352831431779)
                ·
                  refine ⟨29363020152006529247147669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19575346768004352831431779 29363020152006529247147669)
                  ·
                    refine ⟨1376391569625306058460047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29363020152006529247147669 1376391569625306058460047)
                    ·
                      rfl

theorem cell23_8041539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 6].length) (baseStart_8041539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041539 prefixEnd_8041539 := by exact prefixLift 8041539
  have htrace : WordTrace (prefixWord ++ tailWord_8041539) baseStart_8041539 baseEnd_8041539 := by
    simpa [prefixWord, tailWord_8041539, baseEnd_8041539] using wordTrace_append hprefix tailTrace_8041539
  have hstable : (prefixWord ++ tailWord_8041539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041539).length < 2 ^ (prefixWord ++ tailWord_8041539).sum := by decide
  have hdescent : baseEnd_8041539 < baseStart_8041539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041543 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 1, 5]
def baseStart_8041543 : Nat := 118140960795 + 8041543 * 2 ^ 59
def prefixEnd_8041543 : Nat := 4983230072969 + 3 ^ 40 * 8041543 * 2
def baseEnd_8041543 : Nat := 1376392254266178719910041

theorem tailTrace_8041543 : CollatzResearch.WordTrace tailWord_8041543 prefixEnd_8041543 1376392254266178719910041 := by
  unfold tailWord_8041543
  simp only [CollatzResearch.WordTrace]
  refine ⟨293299168705870572048649283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195532779137247048032432855 293299168705870572048649283)
  ·
    refine ⟨439948753058805858072973925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293299168705870572048649283 439948753058805858072973925)
    ·
      refine ⟨82490391198526098388682611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 439948753058805858072973925 82490391198526098388682611)
      ·
        refine ⟨123735586797789147583023917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82490391198526098388682611 123735586797789147583023917)
        ·
          refine ⟨46400845049170930343633969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123735586797789147583023917 46400845049170930343633969)
          ·
            refine ⟨34800633786878197757725477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46400845049170930343633969 34800633786878197757725477)
            ·
              refine ⟨6525118835039662079573527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34800633786878197757725477 6525118835039662079573527)
              ·
                refine ⟨9787678252559493119360291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525118835039662079573527 9787678252559493119360291)
                ·
                  refine ⟨14681517378839239679040437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787678252559493119360291 14681517378839239679040437)
                  ·
                    refine ⟨1376392254266178719910041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14681517378839239679040437 1376392254266178719910041)
                    ·
                      rfl

theorem cell23_8041543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_8041543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041543 prefixEnd_8041543 := by exact prefixLift 8041543
  have htrace : WordTrace (prefixWord ++ tailWord_8041543) baseStart_8041543 baseEnd_8041543 := by
    simpa [prefixWord, tailWord_8041543, baseEnd_8041543] using wordTrace_append hprefix tailTrace_8041543
  have hstable : (prefixWord ++ tailWord_8041543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041543).length < 2 ^ (prefixWord ++ tailWord_8041543).sum := by decide
  have hdescent : baseEnd_8041543 < baseStart_8041543 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041559 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6]
def baseStart_8041559 : Nat := 118140960795 + 8041559 * 2 ^ 59
def prefixEnd_8041559 : Nat := 4983230072969 + 3 ^ 40 * 8041559 * 2
def baseEnd_8041559 : Nat := 4129184978489008097130049

theorem tailTrace_8041559 : CollatzResearch.WordTrace tailWord_8041559 prefixEnd_8041559 4129184978489008097130049 := by
  unfold tailWord_8041559
  simp only [CollatzResearch.WordTrace]
  refine ⟨293299752273812606781231731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195533168182541737854154487 293299752273812606781231731)
  ·
    refine ⟨439949628410718910171847597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293299752273812606781231731 439949628410718910171847597)
    ·
      refine ⟨164981110654019591314442849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439949628410718910171847597 164981110654019591314442849)
      ·
        refine ⟨123735832990514693485832137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164981110654019591314442849 123735832990514693485832137)
        ·
          refine ⟨92801874742886020114374103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123735832990514693485832137 92801874742886020114374103)
          ·
            refine ⟨139202812114329030171561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92801874742886020114374103 139202812114329030171561155)
            ·
              refine ⟨208804218171493545257341733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139202812114329030171561155 208804218171493545257341733)
              ·
                refine ⟨39150790907155039735751575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208804218171493545257341733 39150790907155039735751575)
                ·
                  refine ⟨58726186360732559603627363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39150790907155039735751575 58726186360732559603627363)
                  ·
                    refine ⟨88089279541098839405441045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58726186360732559603627363 88089279541098839405441045)
                    ·
                      refine ⟨4129184978489008097130049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88089279541098839405441045 4129184978489008097130049)
                      ·
                        rfl

theorem cell23_8041559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_8041559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041559 prefixEnd_8041559 := by exact prefixLift 8041559
  have htrace : WordTrace (prefixWord ++ tailWord_8041559) baseStart_8041559 baseEnd_8041559 := by
    simpa [prefixWord, tailWord_8041559, baseEnd_8041559] using wordTrace_append hprefix tailTrace_8041559
  have hstable : (prefixWord ++ tailWord_8041559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041559).length < 2 ^ (prefixWord ++ tailWord_8041559).sum := by decide
  have hdescent : baseEnd_8041559 < baseStart_8041559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041583 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 3]
def baseStart_8041583 : Nat := 118140960795 + 8041583 * 2 ^ 59
def prefixEnd_8041583 : Nat := 4983230072969 + 3 ^ 40 * 8041583 * 2
def baseEnd_8041583 : Nat := 4129197302024716003229939

theorem tailTrace_8041583 : CollatzResearch.WordTrace tailWord_8041583 prefixEnd_8041583 4129197302024716003229939 := by
  unfold tailWord_8041583
  simp only [CollatzResearch.WordTrace]
  refine ⟨293300627625725658880105403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195533751750483772586736935 293300627625725658880105403)
  ·
    refine ⟨439950941438588488320158105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293300627625725658880105403 439950941438588488320158105)
    ·
      refine ⟨329963206078941366240118579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439950941438588488320158105 329963206078941366240118579)
      ·
        refine ⟨494944809118412049360177869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329963206078941366240118579 494944809118412049360177869)
        ·
          refine ⟨185604303419404518510066701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 494944809118412049360177869 185604303419404518510066701)
          ·
            refine ⟨69601613782276694441275013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185604303419404518510066701 69601613782276694441275013)
            ·
              refine ⟨13050302584176880207739065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69601613782276694441275013 13050302584176880207739065)
              ·
                refine ⟨9787726938132660155804299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13050302584176880207739065 9787726938132660155804299)
                ·
                  refine ⟨14681590407198990233706449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787726938132660155804299 14681590407198990233706449)
                  ·
                    refine ⟨11011192805399242675279837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14681590407198990233706449 11011192805399242675279837)
                    ·
                      refine ⟨4129197302024716003229939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011192805399242675279837 4129197302024716003229939)
                      ·
                        rfl

theorem cell23_8041583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 2, 3].length) (baseStart_8041583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041583 prefixEnd_8041583 := by exact prefixLift 8041583
  have htrace : WordTrace (prefixWord ++ tailWord_8041583) baseStart_8041583 baseEnd_8041583 := by
    simpa [prefixWord, tailWord_8041583, baseEnd_8041583] using wordTrace_append hprefix tailTrace_8041583
  have hstable : (prefixWord ++ tailWord_8041583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041583).length < 2 ^ (prefixWord ++ tailWord_8041583).sum := by decide
  have hdescent : baseEnd_8041583 < baseStart_8041583 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041596 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_8041596 : Nat := 118140960795 + 8041596 * 2 ^ 59
def prefixEnd_8041596 : Nat := 4983230072969 + 3 ^ 40 * 8041596 * 2
def baseEnd_8041596 : Nat := 4129203977273224452367379

theorem tailTrace_8041596 : CollatzResearch.WordTrace tailWord_8041596 prefixEnd_8041596 4129203977273224452367379 := by
  unfold tailWord_8041596
  simp only [CollatzResearch.WordTrace]
  refine ⟨146650550887339281050164321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195534067849785708066885761 146650550887339281050164321)
  ·
    refine ⟨109987913165504460787623241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146650550887339281050164321 109987913165504460787623241)
    ·
      refine ⟨82490934874128345590717431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109987913165504460787623241 82490934874128345590717431)
      ·
        refine ⟨123736402311192518386076147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82490934874128345590717431 123736402311192518386076147)
        ·
          refine ⟨185604603466788777579114221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123736402311192518386076147 185604603466788777579114221)
          ·
            refine ⟨69601726300045791592167833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185604603466788777579114221 69601726300045791592167833)
            ·
              refine ⟨52201294725034343694125875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69601726300045791592167833 52201294725034343694125875)
              ·
                refine ⟨78301942087551515541188813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52201294725034343694125875 78301942087551515541188813)
                ·
                  refine ⟨29363228282831818327945805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78301942087551515541188813 29363228282831818327945805)
                  ·
                    refine ⟨11011210606061931872979677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29363228282831818327945805 11011210606061931872979677)
                    ·
                      refine ⟨4129203977273224452367379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011210606061931872979677 4129203977273224452367379)
                      ·
                        rfl

theorem cell23_8041596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_8041596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041596 prefixEnd_8041596 := by exact prefixLift 8041596
  have htrace : WordTrace (prefixWord ++ tailWord_8041596) baseStart_8041596 baseEnd_8041596 := by
    simpa [prefixWord, tailWord_8041596, baseEnd_8041596] using wordTrace_append hprefix tailTrace_8041596
  have hstable : (prefixWord ++ tailWord_8041596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041596).length < 2 ^ (prefixWord ++ tailWord_8041596).sum := by decide
  have hdescent : baseEnd_8041596 < baseStart_8041596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041634 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 1, 2, 3]
def baseStart_8041634 : Nat := 118140960795 + 8041634 * 2 ^ 59
def prefixEnd_8041634 : Nat := 4983230072969 + 3 ^ 40 * 8041634 * 2
def baseEnd_8041634 : Nat := 4129223489538095303692205

theorem tailTrace_8041634 : CollatzResearch.WordTrace tailWord_8041634 prefixEnd_8041634 4129223489538095303692205 := by
  unfold tailWord_8041634
  simp only [CollatzResearch.WordTrace]
  refine ⟨73325621937135223647552989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195534991832360596393474637 73325621937135223647552989)
  ·
    refine ⟨27497108226425708867832371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73325621937135223647552989 27497108226425708867832371)
    ·
      refine ⟨41245662339638563301748557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27497108226425708867832371 41245662339638563301748557)
      ·
        refine ⟨15467123377364461238155709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41245662339638563301748557 15467123377364461238155709)
        ·
          refine ⟨5800171266511672964308391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15467123377364461238155709 5800171266511672964308391)
          ·
            refine ⟨8700256899767509446462587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800171266511672964308391 8700256899767509446462587)
            ·
              refine ⟨13050385349651264169693881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700256899767509446462587 13050385349651264169693881)
              ·
                refine ⟨9787789012238448127270411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13050385349651264169693881 9787789012238448127270411)
                ·
                  refine ⟨14681683518357672190905617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787789012238448127270411 14681683518357672190905617)
                  ·
                    refine ⟨11011262638768254143179213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14681683518357672190905617 11011262638768254143179213)
                    ·
                      refine ⟨4129223489538095303692205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011262638768254143179213 4129223489538095303692205)
                      ·
                        rfl

theorem cell23_8041634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_8041634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041634 prefixEnd_8041634 := by exact prefixLift 8041634
  have htrace : WordTrace (prefixWord ++ tailWord_8041634) baseStart_8041634 baseEnd_8041634 := by
    simpa [prefixWord, tailWord_8041634, baseEnd_8041634] using wordTrace_append hprefix tailTrace_8041634
  have hstable : (prefixWord ++ tailWord_8041634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041634).length < 2 ^ (prefixWord ++ tailWord_8041634).sum := by decide
  have hdescent : baseEnd_8041634 < baseStart_8041634 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041657 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 1, 3, 2]
def baseStart_8041657 : Nat := 118140960795 + 8041657 * 2 ^ 59
def prefixEnd_8041657 : Nat := 4983230072969 + 3 ^ 40 * 8041657 * 2
def baseEnd_8041657 : Nat := 4129235299593148713704599

theorem tailTrace_8041657 : CollatzResearch.WordTrace tailWord_8041657 prefixEnd_8041657 4129235299593148713704599 := by
  unfold tailWord_8041657
  simp only [CollatzResearch.WordTrace]
  refine ⟨293303326627457569518299225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195535551084971713012199483 293303326627457569518299225)
  ·
    refine ⟨219977494970593177138724419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293303326627457569518299225 219977494970593177138724419)
    ·
      refine ⟨329966242455889765708086629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219977494970593177138724419 329966242455889765708086629)
      ·
        refine ⟨61868670460479331070266243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 329966242455889765708086629 61868670460479331070266243)
        ·
          refine ⟨92803005690718996605399365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61868670460479331070266243 92803005690718996605399365)
          ·
            refine ⟨17400563567009811863512381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92803005690718996605399365 17400563567009811863512381)
            ·
              refine ⟨6525211337628679448817143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17400563567009811863512381 6525211337628679448817143)
              ·
                refine ⟨9787817006443019173225715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525211337628679448817143 9787817006443019173225715)
                ·
                  refine ⟨14681725509664528759838573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9787817006443019173225715 14681725509664528759838573)
                  ·
                    refine ⟨5505647066124198284939465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14681725509664528759838573 5505647066124198284939465)
                    ·
                      refine ⟨4129235299593148713704599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505647066124198284939465 4129235299593148713704599)
                      ·
                        rfl

theorem cell23_8041657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_8041657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041657 prefixEnd_8041657 := by exact prefixLift 8041657
  have htrace : WordTrace (prefixWord ++ tailWord_8041657) baseStart_8041657 baseEnd_8041657 := by
    simpa [prefixWord, tailWord_8041657, baseEnd_8041657] using wordTrace_append hprefix tailTrace_8041657
  have hstable : (prefixWord ++ tailWord_8041657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041657).length < 2 ^ (prefixWord ++ tailWord_8041657).sum := by decide
  have hdescent : baseEnd_8041657 < baseStart_8041657 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041659 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 11]
def baseStart_8041659 : Nat := 118140960795 + 8041659 * 2 ^ 59
def prefixEnd_8041659 : Nat := 4983230072969 + 3 ^ 40 * 8041659 * 2
def baseEnd_8041659 : Nat := 458804036283828633986621

theorem tailTrace_8041659 : CollatzResearch.WordTrace tailWord_8041659 prefixEnd_8041659 458804036283828633986621 := by
  unfold tailWord_8041659
  simp only [CollatzResearch.WordTrace]
  refine ⟨293303399573450323859872031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195535599715633549239914687 293303399573450323859872031)
  ·
    refine ⟨439955099360175485789808047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293303399573450323859872031 439955099360175485789808047)
    ·
      refine ⟨659932649040263228684712071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439955099360175485789808047 659932649040263228684712071)
      ·
        refine ⟨989898973560394843027068107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659932649040263228684712071 989898973560394843027068107)
        ·
          refine ⟨1484848460340592264540602161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989898973560394843027068107 1484848460340592264540602161)
          ·
            refine ⟨1113636345255444198405451621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1484848460340592264540602161 1113636345255444198405451621)
            ·
              refine ⟨208806814735395787201022179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1113636345255444198405451621 208806814735395787201022179)
              ·
                refine ⟨313210222103093680801533269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208806814735395787201022179 313210222103093680801533269)
                ·
                  refine ⟨458804036283828633986621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 313210222103093680801533269 458804036283828633986621)
                  ·
                    rfl

theorem cell23_8041659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 11].length) (baseStart_8041659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041659 prefixEnd_8041659 := by exact prefixLift 8041659
  have htrace : WordTrace (prefixWord ++ tailWord_8041659) baseStart_8041659 baseEnd_8041659 := by
    simpa [prefixWord, tailWord_8041659, baseEnd_8041659] using wordTrace_append hprefix tailTrace_8041659
  have hstable : (prefixWord ++ tailWord_8041659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041659).length < 2 ^ (prefixWord ++ tailWord_8041659).sum := by decide
  have hdescent : baseEnd_8041659 < baseStart_8041659 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041763 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3]
def baseStart_8041763 : Nat := 118140960795 + 8041763 * 2 ^ 59
def prefixEnd_8041763 : Nat := 4983230072969 + 3 ^ 40 * 8041763 * 2
def baseEnd_8041763 : Nat := 4129289728542525298979111

theorem tailTrace_8041763 : CollatzResearch.WordTrace tailWord_8041763 prefixEnd_8041763 4129289728542525298979111 := by
  unfold tailWord_8041763
  simp only [CollatzResearch.WordTrace]
  refine ⟨293307192765073549621657943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195538128510049033081105295 293307192765073549621657943)
  ·
    refine ⟨439960789147610324432486915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293307192765073549621657943 439960789147610324432486915)
    ·
      refine ⟨659941183721415486648730373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439960789147610324432486915 659941183721415486648730373)
      ·
        refine ⟨123738971947765403746636945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 659941183721415486648730373 123738971947765403746636945)
        ·
          refine ⟨92804228960824052809977709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123738971947765403746636945 92804228960824052809977709)
          ·
            refine ⟨34801585860309019803741641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92804228960824052809977709 34801585860309019803741641)
            ·
              refine ⟨26101189395231764852806231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34801585860309019803741641 26101189395231764852806231)
              ·
                refine ⟨39151784092847647279209347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26101189395231764852806231 39151784092847647279209347)
                ·
                  refine ⟨58727676139271470918814021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39151784092847647279209347 58727676139271470918814021)
                  ·
                    refine ⟨11011439276113400797277629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58727676139271470918814021 11011439276113400797277629)
                    ·
                      refine ⟨4129289728542525298979111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011439276113400797277629 4129289728542525298979111)
                      ·
                        rfl

theorem cell23_8041763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_8041763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041763 prefixEnd_8041763 := by exact prefixLift 8041763
  have htrace : WordTrace (prefixWord ++ tailWord_8041763) baseStart_8041763 baseEnd_8041763 := by
    simpa [prefixWord, tailWord_8041763, baseEnd_8041763] using wordTrace_append hprefix tailTrace_8041763
  have hstable : (prefixWord ++ tailWord_8041763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041763).length < 2 ^ (prefixWord ++ tailWord_8041763).sum := by decide
  have hdescent : baseEnd_8041763 < baseStart_8041763 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041810 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3]
def baseStart_8041810 : Nat := 118140960795 + 8041810 * 2 ^ 59
def prefixEnd_8041810 : Nat := 4983230072969 + 3 ^ 40 * 8041810 * 2
def baseEnd_8041810 : Nat := 4129313862133286615091395

theorem tailTrace_8041810 : CollatzResearch.WordTrace tailWord_8041810 prefixEnd_8041810 4129313862133286615091395 := by
  unfold tailWord_8041810
  simp only [CollatzResearch.WordTrace]
  refine ⟨73327226748975819162154721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195539271330602184432412589 73327226748975819162154721)
  ·
    refine ⟨54995420061731864371616041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73327226748975819162154721 54995420061731864371616041)
    ·
      refine ⟨41246565046298898278712031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54995420061731864371616041 41246565046298898278712031)
      ·
        refine ⟨61869847569448347418068047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41246565046298898278712031 61869847569448347418068047)
        ·
          refine ⟨92804771354172521127102071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61869847569448347418068047 92804771354172521127102071)
          ·
            refine ⟨139207157031258781690653107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92804771354172521127102071 139207157031258781690653107)
            ·
              refine ⟨208810735546888172535979661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139207157031258781690653107 208810735546888172535979661)
              ·
                refine ⟨78304025830083064700992373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208810735546888172535979661 78304025830083064700992373)
                ·
                  refine ⟨7341002421570287315718035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78304025830083064700992373 7341002421570287315718035)
                  ·
                    refine ⟨11011503632355430973577053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341002421570287315718035 11011503632355430973577053)
                    ·
                      refine ⟨4129313862133286615091395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011503632355430973577053 4129313862133286615091395)
                      ·
                        rfl

theorem cell23_8041810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3].length) (baseStart_8041810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041810 prefixEnd_8041810 := by exact prefixLift 8041810
  have htrace : WordTrace (prefixWord ++ tailWord_8041810) baseStart_8041810 baseEnd_8041810 := by
    simpa [prefixWord, tailWord_8041810, baseEnd_8041810] using wordTrace_append hprefix tailTrace_8041810
  have hstable : (prefixWord ++ tailWord_8041810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041810).length < 2 ^ (prefixWord ++ tailWord_8041810).sum := by decide
  have hdescent : baseEnd_8041810 < baseStart_8041810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041837 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_8041837 : Nat := 118140960795 + 8041837 * 2 ^ 59
def prefixEnd_8041837 : Nat := 4983230072969 + 3 ^ 40 * 8041837 * 2
def baseEnd_8041837 : Nat := 4129327726110958009453771

theorem tailTrace_8041837 : CollatzResearch.WordTrace tailWord_8041837 prefixEnd_8041837 4129327726110958009453771 := by
  unfold tailWord_8041837
  simp only [CollatzResearch.WordTrace]
  refine ⟨293309891766805460259851765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195539927844536973506567843 293309891766805460259851765)
  ·
    refine ⟨27497802353138011899361103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293309891766805460259851765 27497802353138011899361103)
    ·
      refine ⟨41246703529707017849041655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27497802353138011899361103 41246703529707017849041655)
      ·
        refine ⟨61870055294560526773562483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41246703529707017849041655 61870055294560526773562483)
        ·
          refine ⟨92805082941840790160343725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61870055294560526773562483 92805082941840790160343725)
          ·
            refine ⟨34801906103190296310128897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92805082941840790160343725 34801906103190296310128897)
            ·
              refine ⟨26101429577392722232596673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34801906103190296310128897 26101429577392722232596673)
              ·
                refine ⟨19576072183044541674447505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26101429577392722232596673 19576072183044541674447505)
                ·
                  refine ⟨14682054137283406255835629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576072183044541674447505 14682054137283406255835629)
                  ·
                    refine ⟨5505770301481277345938361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14682054137283406255835629 5505770301481277345938361)
                    ·
                      refine ⟨4129327726110958009453771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505770301481277345938361 4129327726110958009453771)
                      ·
                        rfl

theorem cell23_8041837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_8041837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041837 prefixEnd_8041837 := by exact prefixLift 8041837
  have htrace : WordTrace (prefixWord ++ tailWord_8041837) baseStart_8041837 baseEnd_8041837 := by
    simpa [prefixWord, tailWord_8041837, baseEnd_8041837] using wordTrace_append hprefix tailTrace_8041837
  have hstable : (prefixWord ++ tailWord_8041837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041837).length < 2 ^ (prefixWord ++ tailWord_8041837).sum := by decide
  have hdescent : baseEnd_8041837 < baseStart_8041837 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041838 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 1, 4]
def baseStart_8041838 : Nat := 118140960795 + 8041838 * 2 ^ 59
def prefixEnd_8041838 : Nat := 4983230072969 + 3 ^ 40 * 8041838 * 2
def baseEnd_8041838 : Nat := 1376442746530537501847089

theorem tailTrace_8041838 : CollatzResearch.WordTrace tailWord_8041838 prefixEnd_8041838 1376442746530537501847089 := by
  unfold tailWord_8041838
  simp only [CollatzResearch.WordTrace]
  refine ⟨36663741029975229678829771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195539952159867891620425445 36663741029975229678829771)
  ·
    refine ⟨54995611544962844518244657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36663741029975229678829771 54995611544962844518244657)
    ·
      refine ⟨41246708658722133388683493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54995611544962844518244657 41246708658722133388683493)
      ·
        refine ⟨7733757873510400010378155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41246708658722133388683493 7733757873510400010378155)
        ·
          refine ⟨11600636810265600015567233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733757873510400010378155 11600636810265600015567233)
          ·
            refine ⟨8700477607699200011675425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600636810265600015567233 8700477607699200011675425)
            ·
              refine ⟨6525358205774400008756569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700477607699200011675425 6525358205774400008756569)
              ·
                refine ⟨4894018654330800006567427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525358205774400008756569 4894018654330800006567427)
                ·
                  refine ⟨7341027981496200009851141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894018654330800006567427 7341027981496200009851141)
                  ·
                    refine ⟨1376442746530537501847089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341027981496200009851141 1376442746530537501847089)
                    ·
                      rfl

theorem cell23_8041838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_8041838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041838 prefixEnd_8041838 := by exact prefixLift 8041838
  have htrace : WordTrace (prefixWord ++ tailWord_8041838) baseStart_8041838 baseEnd_8041838 := by
    simpa [prefixWord, tailWord_8041838, baseEnd_8041838] using wordTrace_append hprefix tailTrace_8041838
  have hstable : (prefixWord ++ tailWord_8041838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041838).length < 2 ^ (prefixWord ++ tailWord_8041838).sum := by decide
  have hdescent : baseEnd_8041838 < baseStart_8041838 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041853 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_8041853 : Nat := 118140960795 + 8041853 * 2 ^ 59
def prefixEnd_8041853 : Nat := 4983230072969 + 3 ^ 40 * 8041853 * 2
def baseEnd_8041853 : Nat := 4129335941801429946853697

theorem tailTrace_8041853 : CollatzResearch.WordTrace tailWord_8041853 prefixEnd_8041853 4129335941801429946853697 := by
  unfold tailWord_8041853
  simp only [CollatzResearch.WordTrace]
  refine ⟨293310475334747494992434213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195540316889831663328289475 293310475334747494992434213)
  ·
    refine ⟨54995714125265155311081415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293310475334747494992434213 54995714125265155311081415)
    ·
      refine ⟨82493571187897732966622123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54995714125265155311081415 82493571187897732966622123)
      ·
        refine ⟨123740356781846599449933185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82493571187897732966622123 123740356781846599449933185)
        ·
          refine ⟨92805267586384949587449889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123740356781846599449933185 92805267586384949587449889)
          ·
            refine ⟨69603950689788712190587417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92805267586384949587449889 69603950689788712190587417)
            ·
              refine ⟨52202963017341534142940563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69603950689788712190587417 52202963017341534142940563)
              ·
                refine ⟨78304444526012301214410845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52202963017341534142940563 78304444526012301214410845)
                ·
                  refine ⟨29364166697254612955404067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78304444526012301214410845 29364166697254612955404067)
                  ·
                    refine ⟨44046250045881919433106101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29364166697254612955404067 44046250045881919433106101)
                    ·
                      refine ⟨4129335941801429946853697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44046250045881919433106101 4129335941801429946853697)
                      ·
                        rfl

theorem cell23_8041853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_8041853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041853 prefixEnd_8041853 := by exact prefixLift 8041853
  have htrace : WordTrace (prefixWord ++ tailWord_8041853) baseStart_8041853 baseEnd_8041853 := by
    simpa [prefixWord, tailWord_8041853, baseEnd_8041853] using wordTrace_append hprefix tailTrace_8041853
  have hstable : (prefixWord ++ tailWord_8041853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041853).length < 2 ^ (prefixWord ++ tailWord_8041853).sum := by decide
  have hdescent : baseEnd_8041853 < baseStart_8041853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041860 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_8041860 : Nat := 118140960795 + 8041860 * 2 ^ 59
def prefixEnd_8041860 : Nat := 4983230072969 + 3 ^ 40 * 8041860 * 2
def baseEnd_8041860 : Nat := 1376446512055337139822055

theorem tailTrace_8041860 : CollatzResearch.WordTrace tailWord_8041860 prefixEnd_8041860 1376446512055337139822055 := by
  unfold tailWord_8041860
  simp only [CollatzResearch.WordTrace]
  refine ⟨146655365322861067593969517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195540487097148090125292689 146655365322861067593969517)
  ·
    refine ⟨54995761996072900347738569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146655365322861067593969517 54995761996072900347738569)
    ·
      refine ⟨41246821497054675260803927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54995761996072900347738569 41246821497054675260803927)
      ·
        refine ⟨61870232245582012891205891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41246821497054675260803927 61870232245582012891205891)
        ·
          refine ⟨92805348368373019336808837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61870232245582012891205891 92805348368373019336808837)
          ·
            refine ⟨17401002819069941125651657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92805348368373019336808837 17401002819069941125651657)
            ·
              refine ⟨13050752114302455844238743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401002819069941125651657 13050752114302455844238743)
              ·
                refine ⟨19576128171453683766358115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050752114302455844238743 19576128171453683766358115)
                ·
                  refine ⟨29364192257180525649537173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19576128171453683766358115 29364192257180525649537173)
                  ·
                    refine ⟨1376446512055337139822055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29364192257180525649537173 1376446512055337139822055)
                    ·
                      rfl

theorem cell23_8041860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_8041860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041860 prefixEnd_8041860 := by exact prefixLift 8041860
  have htrace : WordTrace (prefixWord ++ tailWord_8041860) baseStart_8041860 baseEnd_8041860 := by
    simpa [prefixWord, tailWord_8041860, baseEnd_8041860] using wordTrace_append hprefix tailTrace_8041860
  have hstable : (prefixWord ++ tailWord_8041860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041860).length < 2 ^ (prefixWord ++ tailWord_8041860).sum := by decide
  have hdescent : baseEnd_8041860 < baseStart_8041860 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041867 : List Nat := [1, 1, 1, 1, 4, 3, 3, 2, 3, 2, 2]
def baseStart_8041867 : Nat := 118140960795 + 8041867 * 2 ^ 59
def prefixEnd_8041867 : Nat := 4983230072969 + 3 ^ 40 * 8041867 * 2
def baseEnd_8041867 : Nat := 4129343130530592892078633

theorem tailTrace_8041867 : CollatzResearch.WordTrace tailWord_8041867 prefixEnd_8041867 4129343130530592892078633 := by
  unfold tailWord_8041867
  simp only [CollatzResearch.WordTrace]
  refine ⟨293310985956696775383443855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195540657304464516922295903 293310985956696775383443855)
  ·
    refine ⟨439966478935045163075165783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293310985956696775383443855 439966478935045163075165783)
    ·
      refine ⟨659949718402567744612748675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439966478935045163075165783 659949718402567744612748675)
      ·
        refine ⟨989924577603851616919123013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659949718402567744612748675 989924577603851616919123013)
        ·
          refine ⟨185610858300722178172335565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 989924577603851616919123013 185610858300722178172335565)
          ·
            refine ⟨69604071862770816814625837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185610858300722178172335565 69604071862770816814625837)
            ·
              refine ⟨26101526948539056305484689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69604071862770816814625837 26101526948539056305484689)
              ·
                refine ⟨19576145211404292229113517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26101526948539056305484689 19576145211404292229113517)
                ·
                  refine ⟨7341054454276609585917569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19576145211404292229113517 7341054454276609585917569)
                  ·
                    refine ⟨5505790840707457189438177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7341054454276609585917569 5505790840707457189438177)
                    ·
                      refine ⟨4129343130530592892078633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505790840707457189438177 4129343130530592892078633)
                      ·
                        rfl

theorem cell23_8041867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 3, 2, 2].length) (baseStart_8041867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041867 prefixEnd_8041867 := by exact prefixLift 8041867
  have htrace : WordTrace (prefixWord ++ tailWord_8041867) baseStart_8041867 baseEnd_8041867 := by
    simpa [prefixWord, tailWord_8041867, baseEnd_8041867] using wordTrace_append hprefix tailTrace_8041867
  have hstable : (prefixWord ++ tailWord_8041867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041867).length < 2 ^ (prefixWord ++ tailWord_8041867).sum := by decide
  have hdescent : baseEnd_8041867 < baseStart_8041867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041884 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_8041884 : Nat := 118140960795 + 8041884 * 2 ^ 59
def prefixEnd_8041884 : Nat := 4983230072969 + 3 ^ 40 * 8041884 * 2
def baseEnd_8041884 : Nat := 4129351859701719325566055

theorem tailTrace_8041884 : CollatzResearch.WordTrace tailWord_8041884 prefixEnd_8041884 4129351859701719325566055 := by
  unfold tailWord_8041884
  simp only [CollatzResearch.WordTrace]
  refine ⟨146655802998817593643406353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195541070665090124857875137 146655802998817593643406353)
  ·
    refine ⟨109991852249113195232554765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146655802998817593643406353 109991852249113195232554765)
    ·
      refine ⟨41246944593417448212208037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 109991852249113195232554765 41246944593417448212208037)
      ·
        refine ⟨7733802111265771539789007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41246944593417448212208037 7733802111265771539789007)
        ·
          refine ⟨11600703166898657309683511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7733802111265771539789007 11600703166898657309683511)
          ·
            refine ⟨17401054750347985964525267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600703166898657309683511 17401054750347985964525267)
            ·
              refine ⟨26101582125521978946787901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401054750347985964525267 26101582125521978946787901)
              ·
                refine ⟨9788093297070742105045463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26101582125521978946787901 9788093297070742105045463)
                ·
                  refine ⟨14682139945606113157568195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788093297070742105045463 14682139945606113157568195)
                  ·
                    refine ⟨22023209918409169736352293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14682139945606113157568195 22023209918409169736352293)
                    ·
                      refine ⟨4129351859701719325566055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22023209918409169736352293 4129351859701719325566055)
                      ·
                        rfl

theorem cell23_8041884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_8041884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041884 prefixEnd_8041884 := by exact prefixLift 8041884
  have htrace : WordTrace (prefixWord ++ tailWord_8041884) baseStart_8041884 baseEnd_8041884 := by
    simpa [prefixWord, tailWord_8041884, baseEnd_8041884] using wordTrace_append hprefix tailTrace_8041884
  have hstable : (prefixWord ++ tailWord_8041884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041884).length < 2 ^ (prefixWord ++ tailWord_8041884).sum := by decide
  have hdescent : baseEnd_8041884 < baseStart_8041884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041887 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 3]
def baseStart_8041887 : Nat := 118140960795 + 8041887 * 2 ^ 59
def prefixEnd_8041887 : Nat := 4983230072969 + 3 ^ 40 * 8041887 * 2
def baseEnd_8041887 : Nat := 4129353400143682813828541

theorem tailTrace_8041887 : CollatzResearch.WordTrace tailWord_8041887 prefixEnd_8041887 4129353400143682813828541 := by
  unfold tailWord_8041887
  simp only [CollatzResearch.WordTrace]
  refine ⟨293311715416624318799171915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195541143611082879199447943 293311715416624318799171915)
  ·
    refine ⟨439967573124936478198757873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293311715416624318799171915 439967573124936478198757873)
    ·
      refine ⟨329975679843702358649068405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439967573124936478198757873 329975679843702358649068405)
      ·
        refine ⟨30935219985347096123350163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 329975679843702358649068405 30935219985347096123350163)
        ·
          refine ⟨46402829978020644185025245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30935219985347096123350163 46402829978020644185025245)
          ·
            refine ⟨17401061241757741569384467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46402829978020644185025245 17401061241757741569384467)
            ·
              refine ⟨26101591862636612354076701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401061241757741569384467 26101591862636612354076701)
              ·
                refine ⟨9788096948488729632778763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26101591862636612354076701 9788096948488729632778763)
                ·
                  refine ⟨14682145422733094449168145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788096948488729632778763 14682145422733094449168145)
                  ·
                    refine ⟨11011609067049820836876109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14682145422733094449168145 11011609067049820836876109)
                    ·
                      refine ⟨4129353400143682813828541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011609067049820836876109 4129353400143682813828541)
                      ·
                        rfl

theorem cell23_8041887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_8041887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041887 prefixEnd_8041887 := by exact prefixLift 8041887
  have htrace : WordTrace (prefixWord ++ tailWord_8041887) baseStart_8041887 baseEnd_8041887 := by
    simpa [prefixWord, tailWord_8041887, baseEnd_8041887] using wordTrace_append hprefix tailTrace_8041887
  have hstable : (prefixWord ++ tailWord_8041887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041887).length < 2 ^ (prefixWord ++ tailWord_8041887).sum := by decide
  have hdescent : baseEnd_8041887 < baseStart_8041887 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041901 : List Nat := [1, 5, 2, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_8041901 : Nat := 118140960795 + 8041901 * 2 ^ 59
def prefixEnd_8041901 : Nat := 4983230072969 + 3 ^ 40 * 8041901 * 2
def baseEnd_8041901 : Nat := 4129360588872845759053477

theorem tailTrace_8041901 : CollatzResearch.WordTrace tailWord_8041901 prefixEnd_8041901 4129360588872845759053477 := by
  unfold tailWord_8041901
  simp only [CollatzResearch.WordTrace]
  refine ⟨293312226038573599190181557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195541484025715732793454371 293312226038573599190181557)
  ·
    refine ⟨27498021191116274924079521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293312226038573599190181557 27498021191116274924079521)
    ·
      refine ⟨20623515893337206193059641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27498021191116274924079521 20623515893337206193059641)
      ·
        refine ⟨15467636920002904644794731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20623515893337206193059641 15467636920002904644794731)
        ·
          refine ⟨23201455380004356967192097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467636920002904644794731 23201455380004356967192097)
          ·
            refine ⟨17401091535003267725394073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23201455380004356967192097 17401091535003267725394073)
            ·
              refine ⟨13050818651252450794045555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401091535003267725394073 13050818651252450794045555)
              ·
                refine ⟨19576227976878676191068333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13050818651252450794045555 19576227976878676191068333)
                ·
                  refine ⟨7341085491329503571650625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19576227976878676191068333 7341085491329503571650625)
                  ·
                    refine ⟨5505814118497127678737969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7341085491329503571650625 5505814118497127678737969)
                    ·
                      refine ⟨4129360588872845759053477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505814118497127678737969 4129360588872845759053477)
                      ·
                        rfl

theorem cell23_8041901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_8041901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041901 prefixEnd_8041901 := by exact prefixLift 8041901
  have htrace : WordTrace (prefixWord ++ tailWord_8041901) baseStart_8041901 baseEnd_8041901 := by
    simpa [prefixWord, tailWord_8041901, baseEnd_8041901] using wordTrace_append hprefix tailTrace_8041901
  have hstable : (prefixWord ++ tailWord_8041901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041901).length < 2 ^ (prefixWord ++ tailWord_8041901).sum := by decide
  have hdescent : baseEnd_8041901 < baseStart_8041901 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041923 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4]
def baseStart_8041923 : Nat := 118140960795 + 8041923 * 2 ^ 59
def prefixEnd_8041923 : Nat := 4983230072969 + 3 ^ 40 * 8041923 * 2
def baseEnd_8041923 : Nat := 4129371885447244672978375

theorem tailTrace_8041923 : CollatzResearch.WordTrace tailWord_8041923 prefixEnd_8041923 4129371885447244672978375 := by
  unfold tailWord_8041923
  simp only [CollatzResearch.WordTrace]
  refine ⟨293313028444493896947482423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195542018962995931298321615 293313028444493896947482423)
  ·
    refine ⟨439969542666740845421223635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293313028444493896947482423 439969542666740845421223635)
    ·
      refine ⟨659954314000111268131835453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439969542666740845421223635 659954314000111268131835453)
      ·
        refine ⟨247482867750041725549438295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659954314000111268131835453 247482867750041725549438295)
        ·
          refine ⟨371224301625062588324157443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247482867750041725549438295 371224301625062588324157443)
          ·
            refine ⟨556836452437593882486236165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371224301625062588324157443 556836452437593882486236165)
            ·
              refine ⟨104406834832048852966169281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 556836452437593882486236165 104406834832048852966169281)
              ·
                refine ⟨78305126124036639724626961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104406834832048852966169281 78305126124036639724626961)
                ·
                  refine ⟨58728844593027479793470221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78305126124036639724626961 58728844593027479793470221)
                  ·
                    refine ⟨22023316722385304922551333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58728844593027479793470221 22023316722385304922551333)
                    ·
                      refine ⟨4129371885447244672978375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22023316722385304922551333 4129371885447244672978375)
                      ·
                        rfl

theorem cell23_8041923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_8041923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041923 prefixEnd_8041923 := by exact prefixLift 8041923
  have htrace : WordTrace (prefixWord ++ tailWord_8041923) baseStart_8041923 baseEnd_8041923 := by
    simpa [prefixWord, tailWord_8041923, baseEnd_8041923] using wordTrace_append hprefix tailTrace_8041923
  have hstable : (prefixWord ++ tailWord_8041923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041923).length < 2 ^ (prefixWord ++ tailWord_8041923).sum := by decide
  have hdescent : baseEnd_8041923 < baseStart_8041923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041960 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_8041960 : Nat := 118140960795 + 8041960 * 2 ^ 59
def prefixEnd_8041960 : Nat := 4983230072969 + 3 ^ 40 * 8041960 * 2
def baseEnd_8041960 : Nat := 4129390884231461028215705

theorem tailTrace_8041960 : CollatzResearch.WordTrace tailWord_8041960 prefixEnd_8041960 4129390884231461028215705 := by
  unfold tailWord_8041960
  simp only [CollatzResearch.WordTrace]
  refine ⟨146657188972679926133289667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195542918630239901511052889 146657188972679926133289667)
  ·
    refine ⟨219985783459019889199934501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146657188972679926133289667 219985783459019889199934501)
    ·
      refine ⟨41247334398566229224987719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 219985783459019889199934501 41247334398566229224987719)
      ·
        refine ⟨61871001597849343837481579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41247334398566229224987719 61871001597849343837481579)
        ·
          refine ⟨92806502396774015756222369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61871001597849343837481579 92806502396774015756222369)
          ·
            refine ⟨69604876797580511817166777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92806502396774015756222369 69604876797580511817166777)
            ·
              refine ⟨52203657598185383862875083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69604876797580511817166777 52203657598185383862875083)
              ·
                refine ⟨78305486397278075794312625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52203657598185383862875083 78305486397278075794312625)
                ·
                  refine ⟨58729114797958556845734469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78305486397278075794312625 58729114797958556845734469)
                  ·
                    refine ⟨11011709024617229408575213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58729114797958556845734469 11011709024617229408575213)
                    ·
                      refine ⟨4129390884231461028215705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011709024617229408575213 4129390884231461028215705)
                      ·
                        rfl

theorem cell23_8041960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_8041960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041960 prefixEnd_8041960 := by exact prefixLift 8041960
  have htrace : WordTrace (prefixWord ++ tailWord_8041960) baseStart_8041960 baseEnd_8041960 := by
    simpa [prefixWord, tailWord_8041960, baseEnd_8041960] using wordTrace_append hprefix tailTrace_8041960
  have hstable : (prefixWord ++ tailWord_8041960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041960).length < 2 ^ (prefixWord ++ tailWord_8041960).sum := by decide
  have hdescent : baseEnd_8041960 < baseStart_8041960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8041963 : List Nat := [1, 1, 1, 1, 2, 3, 2, 5, 7]
def baseStart_8041963 : Nat := 118140960795 + 8041963 * 2 ^ 59
def prefixEnd_8041963 : Nat := 4983230072969 + 3 ^ 40 * 8041963 * 2
def baseEnd_8041963 : Nat := 458821380519269390719799

theorem tailTrace_8041963 : CollatzResearch.WordTrace tailWord_8041963 prefixEnd_8041963 458821380519269390719799 := by
  unfold tailWord_8041963
  simp only [CollatzResearch.WordTrace]
  refine ⟨293314487364348983778938543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195542991576232655852625695 293314487364348983778938543)
  ·
    refine ⟨439971731046523475668407815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293314487364348983778938543 439971731046523475668407815)
    ·
      refine ⟨659957596569785213502611723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439971731046523475668407815 659957596569785213502611723)
      ·
        refine ⟨989936394854677820253917585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659957596569785213502611723 989936394854677820253917585)
        ·
          refine ⟨742452296141008365190438189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989936394854677820253917585 742452296141008365190438189)
          ·
            refine ⟨278419611052878136946414321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742452296141008365190438189 278419611052878136946414321)
            ·
              refine ⟨208814708289658602709810741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278419611052878136946414321 208814708289658602709810741)
              ·
                refine ⟨19576378902155494004044757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208814708289658602709810741 19576378902155494004044757)
                ·
                  refine ⟨458821380519269390719799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19576378902155494004044757 458821380519269390719799)
                  ·
                    rfl

theorem cell23_8041963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 7].length) (baseStart_8041963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8041963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8041963 prefixEnd_8041963 := by exact prefixLift 8041963
  have htrace : WordTrace (prefixWord ++ tailWord_8041963) baseStart_8041963 baseEnd_8041963 := by
    simpa [prefixWord, tailWord_8041963, baseEnd_8041963] using wordTrace_append hprefix tailTrace_8041963
  have hstable : (prefixWord ++ tailWord_8041963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8041963).length < 2 ^ (prefixWord ++ tailWord_8041963).sum := by decide
  have hdescent : baseEnd_8041963 < baseStart_8041963 := by decide
  rcases family_descends (prefixWord ++ tailWord_8041963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042017 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 2, 5, 2]
def baseStart_8042017 : Nat := 118140960795 + 8042017 * 2 ^ 59
def prefixEnd_8042017 : Nat := 4983230072969 + 3 ^ 40 * 8042017 * 2
def baseEnd_8042017 : Nat := 4129420152628767305202943

theorem tailTrace_8042017 : CollatzResearch.WordTrace tailWord_8042017 prefixEnd_8042017 4129420152628767305202943 := by
  unfold tailWord_8042017
  simp only [CollatzResearch.WordTrace]
  refine ⟨293316456906153351001404305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195544304604102234000936203 293316456906153351001404305)
  ·
    refine ⟨219987342679615013251053229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293316456906153351001404305 219987342679615013251053229)
    ·
      refine ⟨82495253504855629969144961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 219987342679615013251053229 82495253504855629969144961)
      ·
        refine ⟨61871440128641722476858721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82495253504855629969144961 61871440128641722476858721)
        ·
          refine ⟨46403580096481291857644041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61871440128641722476858721 46403580096481291857644041)
          ·
            refine ⟨34802685072360968893233031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46403580096481291857644041 34802685072360968893233031)
            ·
              refine ⟨52204027608541453339849547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34802685072360968893233031 52204027608541453339849547)
              ·
                refine ⟨78306041412812180009774321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52204027608541453339849547 78306041412812180009774321)
                ·
                  refine ⟨58729531059609135007330741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78306041412812180009774321 58729531059609135007330741)
                  ·
                    refine ⟨5505893536838356406937257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58729531059609135007330741 5505893536838356406937257)
                    ·
                      refine ⟨4129420152628767305202943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505893536838356406937257 4129420152628767305202943)
                      ·
                        rfl

theorem cell23_8042017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_8042017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042017 prefixEnd_8042017 := by exact prefixLift 8042017
  have htrace : WordTrace (prefixWord ++ tailWord_8042017) baseStart_8042017 baseEnd_8042017 := by
    simpa [prefixWord, tailWord_8042017, baseEnd_8042017] using wordTrace_append hprefix tailTrace_8042017
  have hstable : (prefixWord ++ tailWord_8042017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042017).length < 2 ^ (prefixWord ++ tailWord_8042017).sum := by decide
  have hdescent : baseEnd_8042017 < baseStart_8042017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042024 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_8042024 : Nat := 118140960795 + 8042024 * 2 ^ 59
def prefixEnd_8042024 : Nat := 4983230072969 + 3 ^ 40 * 8042024 * 2
def baseEnd_8042024 : Nat := 4129423746993348777815411

theorem tailTrace_8042024 : CollatzResearch.WordTrace tailWord_8042024 prefixEnd_8042024 4129423746993348777815411 := by
  unfold tailWord_8042024
  simp only [CollatzResearch.WordTrace]
  refine ⟨146658356108563995598454563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195544474811418660797939417 146658356108563995598454563)
  ·
    refine ⟨219987534162845993397681845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146658356108563995598454563 219987534162845993397681845)
    ·
      refine ⟨20623831327766811881032673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 219987534162845993397681845 20623831327766811881032673)
      ·
        refine ⟨15467873495825108910774505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20623831327766811881032673 15467873495825108910774505)
        ·
          refine ⟨11600905121868831683080879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15467873495825108910774505 11600905121868831683080879)
          ·
            refine ⟨17401357682803247524621319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600905121868831683080879 17401357682803247524621319)
            ·
              refine ⟨26102036524204871286931979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401357682803247524621319 26102036524204871286931979)
              ·
                refine ⟨39153054786307306930397969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26102036524204871286931979 39153054786307306930397969)
                ·
                  refine ⟨29364791089730480197798477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39153054786307306930397969 29364791089730480197798477)
                  ·
                    refine ⟨11011796658648930074174429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29364791089730480197798477 11011796658648930074174429)
                    ·
                      refine ⟨4129423746993348777815411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11011796658648930074174429 4129423746993348777815411)
                      ·
                        rfl

theorem cell23_8042024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_8042024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042024 prefixEnd_8042024 := by exact prefixLift 8042024
  have htrace : WordTrace (prefixWord ++ tailWord_8042024) baseStart_8042024 baseEnd_8042024 := by
    simpa [prefixWord, tailWord_8042024, baseEnd_8042024] using wordTrace_append hprefix tailTrace_8042024
  have hstable : (prefixWord ++ tailWord_8042024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042024).length < 2 ^ (prefixWord ++ tailWord_8042024).sum := by decide
  have hdescent : baseEnd_8042024 < baseStart_8042024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042044 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_8042044 : Nat := 118140960795 + 8042044 * 2 ^ 59
def prefixEnd_8042044 : Nat := 4983230072969 + 3 ^ 40 * 8042044 * 2
def baseEnd_8042044 : Nat := 1376478005535479566521773

theorem tailTrace_8042044 : CollatzResearch.WordTrace tailWord_8042044 prefixEnd_8042044 1376478005535479566521773 := by
  unfold tailWord_8042044
  simp only [CollatzResearch.WordTrace]
  refine ⟨146658720838527767306318593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195544961118037023075091457 146658720838527767306318593)
  ·
    refine ⟨109994040628895825479738945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146658720838527767306318593 109994040628895825479738945)
    ·
      refine ⟨82495530471671869109804209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109994040628895825479738945 82495530471671869109804209)
      ·
        refine ⟨61871647853753901832353157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82495530471671869109804209 61871647853753901832353157)
        ·
          refine ⟨11600933972578856593566217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61871647853753901832353157 11600933972578856593566217)
          ·
            refine ⟨8700700479434142445174663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11600933972578856593566217 8700700479434142445174663)
            ·
              refine ⟨13051050719151213667761995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700700479434142445174663 13051050719151213667761995)
              ·
                refine ⟨19576576078726820501642993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051050719151213667761995 19576576078726820501642993)
                ·
                  refine ⟨14682432059045115376232245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576576078726820501642993 14682432059045115376232245)
                  ·
                    refine ⟨1376478005535479566521773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14682432059045115376232245 1376478005535479566521773)
                    ·
                      rfl

theorem cell23_8042044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_8042044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042044 prefixEnd_8042044 := by exact prefixLift 8042044
  have htrace : WordTrace (prefixWord ++ tailWord_8042044) baseStart_8042044 baseEnd_8042044 := by
    simpa [prefixWord, tailWord_8042044, baseEnd_8042044] using wordTrace_append hprefix tailTrace_8042044
  have hstable : (prefixWord ++ tailWord_8042044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042044).length < 2 ^ (prefixWord ++ tailWord_8042044).sum := by decide
  have hdescent : baseEnd_8042044 < baseStart_8042044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042047 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4]
def baseStart_8042047 : Nat := 118140960795 + 8042047 * 2 ^ 59
def prefixEnd_8042047 : Nat := 4983230072969 + 3 ^ 40 * 8042047 * 2
def baseEnd_8042047 : Nat := 4129435557048402187827805

theorem tailTrace_8042047 : CollatzResearch.WordTrace tailWord_8042047 prefixEnd_8042047 4129435557048402187827805 := by
  unfold tailWord_8042047
  simp only [CollatzResearch.WordTrace]
  refine ⟨293317551096044666124996395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195545034064029777416664263 293317551096044666124996395)
  ·
    refine ⟨439976326644066999187494593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293317551096044666124996395 439976326644066999187494593)
    ·
      refine ⟨329982244983050249390620945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 439976326644066999187494593 329982244983050249390620945)
      ·
        refine ⟨247486683737287687042965709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329982244983050249390620945 247486683737287687042965709)
        ·
          refine ⟨92807506401482882641112141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247486683737287687042965709 92807506401482882641112141)
          ·
            refine ⟨34802814900556080990417053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92807506401482882641112141 34802814900556080990417053)
            ·
              refine ⟨13051055587708530371406395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34802814900556080990417053 13051055587708530371406395)
              ·
                refine ⟨19576583381562795557109593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051055587708530371406395 19576583381562795557109593)
                ·
                  refine ⟨14682437536172096667832195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576583381562795557109593 14682437536172096667832195)
                  ·
                    refine ⟨22023656304258145001748293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14682437536172096667832195 22023656304258145001748293)
                    ·
                      refine ⟨4129435557048402187827805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22023656304258145001748293 4129435557048402187827805)
                      ·
                        rfl

theorem cell23_8042047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 1, 4].length) (baseStart_8042047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042047 prefixEnd_8042047 := by exact prefixLift 8042047
  have htrace : WordTrace (prefixWord ++ tailWord_8042047) baseStart_8042047 baseEnd_8042047 := by
    simpa [prefixWord, tailWord_8042047, baseEnd_8042047] using wordTrace_append hprefix tailTrace_8042047
  have hstable : (prefixWord ++ tailWord_8042047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042047).length < 2 ^ (prefixWord ++ tailWord_8042047).sum := by decide
  have hdescent : baseEnd_8042047 < baseStart_8042047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042060 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_8042060 : Nat := 118140960795 + 8042060 * 2 ^ 59
def prefixEnd_8042060 : Nat := 4983230072969 + 3 ^ 40 * 8042060 * 2
def baseEnd_8042060 : Nat := 4129442232296910636965245

theorem tailTrace_8042060 : CollatzResearch.WordTrace tailWord_8042060 prefixEnd_8042060 4129442232296910636965245 := by
  unfold tailWord_8042060
  simp only [CollatzResearch.WordTrace]
  refine ⟨146659012622498784672609817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195545350163331712896813089 146659012622498784672609817)
  ·
    refine ⟨109994259466874088504457363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146659012622498784672609817 109994259466874088504457363)
    ·
      refine ⟨164991389200311132756686045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109994259466874088504457363 164991389200311132756686045)
      ·
        refine ⟨61871770950116674783757267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 164991389200311132756686045 61871770950116674783757267)
        ·
          refine ⟨92807656425175012175635901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61871770950116674783757267 92807656425175012175635901)
          ·
            refine ⟨34802871159440629565863463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92807656425175012175635901 34802871159440629565863463)
            ·
              refine ⟨52204306739160944348795195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34802871159440629565863463 52204306739160944348795195)
              ·
                refine ⟨78306460108741416523192793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52204306739160944348795195 78306460108741416523192793)
                ·
                  refine ⟨58729845081556062392394595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78306460108741416523192793 58729845081556062392394595)
                  ·
                    refine ⟨88094767622334093588591893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58729845081556062392394595 88094767622334093588591893)
                    ·
                      refine ⟨4129442232296910636965245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88094767622334093588591893 4129442232296910636965245)
                      ·
                        rfl

theorem cell23_8042060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_8042060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042060 prefixEnd_8042060 := by exact prefixLift 8042060
  have htrace : WordTrace (prefixWord ++ tailWord_8042060) baseStart_8042060 baseEnd_8042060 := by
    simpa [prefixWord, tailWord_8042060, baseEnd_8042060] using wordTrace_append hprefix tailTrace_8042060
  have hstable : (prefixWord ++ tailWord_8042060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042060).length < 2 ^ (prefixWord ++ tailWord_8042060).sum := by decide
  have hdescent : baseEnd_8042060 < baseStart_8042060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042107 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 1, 5, 2]
def baseStart_8042107 : Nat := 118140960795 + 8042107 * 2 ^ 59
def prefixEnd_8042107 : Nat := 4983230072969 + 3 ^ 40 * 8042107 * 2
def baseEnd_8042107 : Nat := 4129466365887671953077529

theorem tailTrace_8042107 : CollatzResearch.WordTrace tailWord_8042107 prefixEnd_8042107 4129466365887671953077529 := by
  unfold tailWord_8042107
  simp only [CollatzResearch.WordTrace]
  refine ⟨293319739475827296372180575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195546492983884864248120383 293319739475827296372180575)
  ·
    refine ⟨439979609213740944558270863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293319739475827296372180575 439979609213740944558270863)
    ·
      refine ⟨659969413820611416837406295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439979609213740944558270863 659969413820611416837406295)
      ·
        refine ⟨989954120730917125256109443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659969413820611416837406295 989954120730917125256109443)
        ·
          refine ⟨1484931181096375687884164165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 989954120730917125256109443 1484931181096375687884164165)
          ·
            refine ⟨278424596455570441478280781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1484931181096375687884164165 278424596455570441478280781)
            ·
              refine ⟨104409223670838915554355293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278424596455570441478280781 104409223670838915554355293)
              ·
                refine ⟨39153458876564593332883235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104409223670838915554355293 39153458876564593332883235)
                ·
                  refine ⟨58730188314846889999324853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39153458876564593332883235 58730188314846889999324853)
                  ·
                    refine ⟨5505955154516895937436705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58730188314846889999324853 5505955154516895937436705)
                    ·
                      refine ⟨4129466365887671953077529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505955154516895937436705 4129466365887671953077529)
                      ·
                        rfl

theorem cell23_8042107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 5, 2].length) (baseStart_8042107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042107 prefixEnd_8042107 := by exact prefixLift 8042107
  have htrace : WordTrace (prefixWord ++ tailWord_8042107) baseStart_8042107 baseEnd_8042107 := by
    simpa [prefixWord, tailWord_8042107, baseEnd_8042107] using wordTrace_append hprefix tailTrace_8042107
  have hstable : (prefixWord ++ tailWord_8042107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042107).length < 2 ^ (prefixWord ++ tailWord_8042107).sum := by decide
  have hdescent : baseEnd_8042107 < baseStart_8042107 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042117 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_8042117 : Nat := 118140960795 + 8042117 * 2 ^ 59
def prefixEnd_8042117 : Nat := 4983230072969 + 3 ^ 40 * 8042117 * 2
def baseEnd_8042117 : Nat := 1376490500231405637984161

theorem tailTrace_8042117 : CollatzResearch.WordTrace tailWord_8042117 prefixEnd_8042117 1376490500231405637984161 := by
  unfold tailWord_8042117
  simp only [CollatzResearch.WordTrace]
  refine ⟨293320104205791068080044605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195546736137194045386696403 293320104205791068080044605)
  ·
    refine ⟨109995039077171650530016727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293320104205791068080044605 109995039077171650530016727)
    ·
      refine ⟨164992558615757475795025091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109995039077171650530016727 164992558615757475795025091)
      ·
        refine ⟨247488837923636213692537637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164992558615757475795025091 247488837923636213692537637)
        ·
          refine ⟨46404157110681790067350807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247488837923636213692537637 46404157110681790067350807)
          ·
            refine ⟨69606235666022685101026211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46404157110681790067350807 69606235666022685101026211)
            ·
              refine ⟨104409353499034027651539317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69606235666022685101026211 104409353499034027651539317)
              ·
                refine ⟨9788376890534440092331811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104409353499034027651539317 9788376890534440092331811)
                ·
                  refine ⟨14682565335801660138497717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788376890534440092331811 14682565335801660138497717)
                  ·
                    refine ⟨1376490500231405637984161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14682565335801660138497717 1376490500231405637984161)
                    ·
                      rfl

theorem cell23_8042117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_8042117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042117 prefixEnd_8042117 := by exact prefixLift 8042117
  have htrace : WordTrace (prefixWord ++ tailWord_8042117) baseStart_8042117 baseEnd_8042117 := by
    simpa [prefixWord, tailWord_8042117, baseEnd_8042117] using wordTrace_append hprefix tailTrace_8042117
  have hstable : (prefixWord ++ tailWord_8042117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042117).length < 2 ^ (prefixWord ++ tailWord_8042117).sum := by decide
  have hdescent : baseEnd_8042117 < baseStart_8042117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042124 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_8042124 : Nat := 118140960795 + 8042124 * 2 ^ 59
def prefixEnd_8042124 : Nat := 4983230072969 + 3 ^ 40 * 8042124 * 2
def baseEnd_8042124 : Nat := 4129475095058798386564951

theorem tailTrace_8042124 : CollatzResearch.WordTrace tailWord_8042124 prefixEnd_8042124 4129475095058798386564951 := by
  unfold tailWord_8042124
  simp only [CollatzResearch.WordTrace]
  refine ⟨146660179758382854137774713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195546906344510472183699617 146660179758382854137774713)
  ·
    refine ⟨109995134818787140603331035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146660179758382854137774713 109995134818787140603331035)
    ·
      refine ⟨164992702228180710904996553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 109995134818787140603331035 164992702228180710904996553)
      ·
        refine ⟨123744526671135533178747415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 164992702228180710904996553 123744526671135533178747415)
        ·
          refine ⟨185616790006703299768121123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123744526671135533178747415 185616790006703299768121123)
          ·
            refine ⟨278425185010054949652181685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185616790006703299768121123 278425185010054949652181685)
            ·
              refine ⟨26102361094692651529892033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 278425185010054949652181685 26102361094692651529892033)
              ·
                refine ⟨19576770821019488647419025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26102361094692651529892033 19576770821019488647419025)
                ·
                  refine ⟨14682578115764616485564269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19576770821019488647419025 14682578115764616485564269)
                  ·
                    refine ⟨5505966793411731182086601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14682578115764616485564269 5505966793411731182086601)
                    ·
                      refine ⟨4129475095058798386564951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505966793411731182086601 4129475095058798386564951)
                      ·
                        rfl

theorem cell23_8042124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_8042124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042124 prefixEnd_8042124 := by exact prefixLift 8042124
  have htrace : WordTrace (prefixWord ++ tailWord_8042124) baseStart_8042124 baseEnd_8042124 := by
    simpa [prefixWord, tailWord_8042124, baseEnd_8042124] using wordTrace_append hprefix tailTrace_8042124
  have hstable : (prefixWord ++ tailWord_8042124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042124).length < 2 ^ (prefixWord ++ tailWord_8042124).sum := by decide
  have hdescent : baseEnd_8042124 < baseStart_8042124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042137 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 2, 6, 2]
def baseStart_8042137 : Nat := 118140960795 + 8042137 * 2 ^ 59
def prefixEnd_8042137 : Nat := 4983230072969 + 3 ^ 40 * 8042137 * 2
def baseEnd_8042137 : Nat := 4129481770307306835702391

theorem tailTrace_8042137 : CollatzResearch.WordTrace tailWord_8042137 prefixEnd_8042137 4129481770307306835702391 := by
  unfold tailWord_8042137
  simp only [CollatzResearch.WordTrace]
  refine ⟨293320833665718611495772665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195547222443812407663848443 293320833665718611495772665)
  ·
    refine ⟨219990625249288958621829499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293320833665718611495772665 219990625249288958621829499)
    ·
      refine ⟨329985937873933437932744249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219990625249288958621829499 329985937873933437932744249)
      ·
        refine ⟨247489453405450078449558187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329985937873933437932744249 247489453405450078449558187)
        ·
          refine ⟨371234180108175117674337281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247489453405450078449558187 371234180108175117674337281)
          ·
            refine ⟨278425635081131338255752961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371234180108175117674337281 278425635081131338255752961)
            ·
              refine ⟨208819226310848503691814721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278425635081131338255752961 208819226310848503691814721)
              ·
                refine ⟨156614419733136377768861041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208819226310848503691814721 156614419733136377768861041)
                ·
                  refine ⟨117460814799852283326645781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156614419733136377768861041 117460814799852283326645781)
                  ·
                    refine ⟨5505975693743075780936521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117460814799852283326645781 5505975693743075780936521)
                    ·
                      refine ⟨4129481770307306835702391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5505975693743075780936521 4129481770307306835702391)
                      ·
                        rfl

theorem cell23_8042137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_8042137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042137 prefixEnd_8042137 := by exact prefixLift 8042137
  have htrace : WordTrace (prefixWord ++ tailWord_8042137) baseStart_8042137 baseEnd_8042137 := by
    simpa [prefixWord, tailWord_8042137, baseEnd_8042137] using wordTrace_append hprefix tailTrace_8042137
  have hstable : (prefixWord ++ tailWord_8042137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042137).length < 2 ^ (prefixWord ++ tailWord_8042137).sum := by decide
  have hdescent : baseEnd_8042137 < baseStart_8042137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042160 : List Nat := [2, 1, 1, 1, 2, 1, 6, 9]
def baseStart_8042160 : Nat := 118140960795 + 8042160 * 2 ^ 59
def prefixEnd_8042160 : Nat := 4983230072969 + 3 ^ 40 * 8042160 * 2
def baseEnd_8042160 : Nat := 152944206680087416507955

theorem tailTrace_8042160 : CollatzResearch.WordTrace tailWord_8042160 prefixEnd_8042160 152944206680087416507955 := by
  unfold tailWord_8042160
  simp only [CollatzResearch.WordTrace]
  refine ⟨146660836272317643211929967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195547781696423524282573289 146660836272317643211929967)
  ·
    refine ⟨219991254408476464817894951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146660836272317643211929967 219991254408476464817894951)
    ·
      refine ⟨329986881612714697226842427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219991254408476464817894951 329986881612714697226842427)
      ·
        refine ⟨494980322419072045840263641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329986881612714697226842427 494980322419072045840263641)
        ·
          refine ⟨371235241814304034380197731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494980322419072045840263641 371235241814304034380197731)
          ·
            refine ⟨556852862721456051570296597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371235241814304034380197731 556852862721456051570296597)
            ·
              refine ⟨26102477940068252417357653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 556852862721456051570296597 26102477940068252417357653)
              ·
                refine ⟨152944206680087416507955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26102477940068252417357653 152944206680087416507955)
                ·
                  rfl

theorem cell23_8042160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 9].length) (baseStart_8042160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042160 prefixEnd_8042160 := by exact prefixLift 8042160
  have htrace : WordTrace (prefixWord ++ tailWord_8042160) baseStart_8042160 baseEnd_8042160 := by
    simpa [prefixWord, tailWord_8042160, baseEnd_8042160] using wordTrace_append hprefix tailTrace_8042160
  have hstable : (prefixWord ++ tailWord_8042160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042160).length < 2 ^ (prefixWord ++ tailWord_8042160).sum := by decide
  have hdescent : baseEnd_8042160 < baseStart_8042160 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042167 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4]
def baseStart_8042167 : Nat := 118140960795 + 8042167 * 2 ^ 59
def prefixEnd_8042167 : Nat := 4983230072969 + 3 ^ 40 * 8042167 * 2
def baseEnd_8042167 : Nat := 4129497174726941718327253

theorem tailTrace_8042167 : CollatzResearch.WordTrace tailWord_8042167 prefixEnd_8042167 4129497174726941718327253 := by
  unfold tailWord_8042167
  simp only [CollatzResearch.WordTrace]
  refine ⟨293321927855609926619364755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195547951903739951079576503 293321927855609926619364755)
  ·
    refine ⟨439982891783414889929047133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293321927855609926619364755 439982891783414889929047133)
    ·
      refine ⟨164993584418780583723392675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 439982891783414889929047133 164993584418780583723392675)
      ·
        refine ⟨247490376628170875585089013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 164993584418780583723392675 247490376628170875585089013)
        ·
          refine ⟨23202222808891019586102095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247490376628170875585089013 23202222808891019586102095)
          ·
            refine ⟨34803334213336529379153143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23202222808891019586102095 34803334213336529379153143)
            ·
              refine ⟨52205001320004794068729715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34803334213336529379153143 52205001320004794068729715)
              ·
                refine ⟨78307501980007191103094573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52205001320004794068729715 78307501980007191103094573)
                ·
                  refine ⟨29365313242502696663660465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78307501980007191103094573 29365313242502696663660465)
                  ·
                    refine ⟨22023984931877022497745349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29365313242502696663660465 22023984931877022497745349)
                    ·
                      refine ⟨4129497174726941718327253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22023984931877022497745349 4129497174726941718327253)
                      ·
                        rfl

theorem cell23_8042167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_8042167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042167 prefixEnd_8042167 := by exact prefixLift 8042167
  have htrace : WordTrace (prefixWord ++ tailWord_8042167) baseStart_8042167 baseEnd_8042167 := by
    simpa [prefixWord, tailWord_8042167, baseEnd_8042167] using wordTrace_append hprefix tailTrace_8042167
  have hstable : (prefixWord ++ tailWord_8042167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042167).length < 2 ^ (prefixWord ++ tailWord_8042167).sum := by decide
  have hdescent : baseEnd_8042167 < baseStart_8042167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
