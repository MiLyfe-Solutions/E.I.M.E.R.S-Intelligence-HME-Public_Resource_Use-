import V185TrunkScan23Chunk0949

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5623710 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5623710 : Nat := 118140960795 + 5623710 * 2 ^ 59
def prefixEnd_5623710 : Nat := 4983230072969 + 3 ^ 40 * 5623710 * 2
def baseEnd_5623710 : Nat := 2887666291496297442462035

theorem tailTrace_5623710 : CollatzResearch.WordTrace tailWord_5623710 prefixEnd_5623710 2887666291496297442462035 := by
  unfold tailWord_5623710
  simp only [CollatzResearch.WordTrace]
  refine ⟨25639194307033324755940573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136742369637511065365016389 25639194307033324755940573)
  ·
    refine ⟨9614697865137496783477715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25639194307033324755940573 9614697865137496783477715)
    ·
      refine ⟨14422046797706245175216573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9614697865137496783477715 14422046797706245175216573)
      ·
        refine ⟨5408267549139841940706215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14422046797706245175216573 5408267549139841940706215)
        ·
          refine ⟨8112401323709762911059323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408267549139841940706215 8112401323709762911059323)
          ·
            refine ⟨12168601985564644366588985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8112401323709762911059323 12168601985564644366588985)
            ·
              refine ⟨9126451489173483274941739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12168601985564644366588985 9126451489173483274941739)
              ·
                refine ⟨13689677233760224912412609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126451489173483274941739 13689677233760224912412609)
                ·
                  refine ⟨10267257925320168684309457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13689677233760224912412609 10267257925320168684309457)
                  ·
                    refine ⟨7700443443990126513232093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10267257925320168684309457 7700443443990126513232093)
                    ·
                      refine ⟨2887666291496297442462035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700443443990126513232093 2887666291496297442462035)
                      ·
                        rfl

theorem cell23_5623710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5623710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623710 prefixEnd_5623710 := by exact prefixLift 5623710
  have htrace : WordTrace (prefixWord ++ tailWord_5623710) baseStart_5623710 baseEnd_5623710 := by
    simpa [prefixWord, tailWord_5623710, baseEnd_5623710] using wordTrace_append hprefix tailTrace_5623710
  have hstable : (prefixWord ++ tailWord_5623710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623710).length < 2 ^ (prefixWord ++ tailWord_5623710).sum := by decide
  have hdescent : baseEnd_5623710 < baseStart_5623710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623716 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_5623716 : Nat := 118140960795 + 5623716 * 2 ^ 59
def prefixEnd_5623716 : Nat := 4983230072969 + 3 ^ 40 * 5623716 * 2
def baseEnd_5623716 : Nat := 2887669372380224418987007

theorem tailTrace_5623716 : CollatzResearch.WordTrace tailWord_5623716 prefixEnd_5623716 2887669372380224418987007 := by
  unfold tailWord_5623716
  simp only [CollatzResearch.WordTrace]
  refine ⟨102556886647122430536121501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136742515529496574048162001 102556886647122430536121501)
  ·
    refine ⟨38458832492670911451045563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102556886647122430536121501 38458832492670911451045563)
    ·
      refine ⟨57688248739006367176568345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38458832492670911451045563 57688248739006367176568345)
      ·
        refine ⟨43266186554254775382426259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57688248739006367176568345 43266186554254775382426259)
        ·
          refine ⟨64899279831382163073639389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43266186554254775382426259 64899279831382163073639389)
          ·
            refine ⟨24337229936768311152614771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64899279831382163073639389 24337229936768311152614771)
            ·
              refine ⟨36505844905152466728922157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24337229936768311152614771 36505844905152466728922157)
              ·
                refine ⟨13689691839432175023345809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36505844905152466728922157 13689691839432175023345809)
                ·
                  refine ⟨10267268879574131267509357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13689691839432175023345809 10267268879574131267509357)
                  ·
                    refine ⟨3850225829840299225316009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10267268879574131267509357 3850225829840299225316009)
                    ·
                      refine ⟨2887669372380224418987007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850225829840299225316009 2887669372380224418987007)
                      ·
                        rfl

theorem cell23_5623716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_5623716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623716 prefixEnd_5623716 := by exact prefixLift 5623716
  have htrace : WordTrace (prefixWord ++ tailWord_5623716) baseStart_5623716 baseEnd_5623716 := by
    simpa [prefixWord, tailWord_5623716, baseEnd_5623716] using wordTrace_append hprefix tailTrace_5623716
  have hstable : (prefixWord ++ tailWord_5623716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623716).length < 2 ^ (prefixWord ++ tailWord_5623716).sum := by decide
  have hdescent : baseEnd_5623716 < baseStart_5623716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623739 : List Nat := [1, 1, 1, 1, 1, 2, 2, 8, 2, 4]
def baseStart_5623739 : Nat := 118140960795 + 5623739 * 2 ^ 59
def prefixEnd_5623739 : Nat := 4983230072969 + 3 ^ 40 * 5623739 * 2
def baseEnd_5623739 : Nat := 962560394145092609666467

theorem tailTrace_5623739 : CollatzResearch.WordTrace tailWord_5623739 prefixEnd_5623739 962560394145092609666467 := by
  unfold tailWord_5623739
  simp only [CollatzResearch.WordTrace]
  refine ⟨205114612173161536000330271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136743074782107690666886847 205114612173161536000330271)
  ·
    refine ⟨307671918259742304000495407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205114612173161536000330271 307671918259742304000495407)
    ·
      refine ⟨461507877389613456000743111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307671918259742304000495407 461507877389613456000743111)
      ·
        refine ⟨692261816084420184001114667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461507877389613456000743111 692261816084420184001114667)
        ·
          refine ⟨1038392724126630276001672001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692261816084420184001114667 1038392724126630276001672001)
          ·
            refine ⟨778794543094972707001254001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1038392724126630276001672001 778794543094972707001254001)
            ·
              refine ⟨584095907321229530250940501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778794543094972707001254001 584095907321229530250940501)
              ·
                refine ⟨6844873913920658557628209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 584095907321229530250940501 6844873913920658557628209)
                ·
                  refine ⟨5133655435440493918221157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844873913920658557628209 5133655435440493918221157)
                  ·
                    refine ⟨962560394145092609666467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133655435440493918221157 962560394145092609666467)
                    ·
                      rfl

theorem cell23_5623739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 8, 2, 4].length) (baseStart_5623739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623739 prefixEnd_5623739 := by exact prefixLift 5623739
  have htrace : WordTrace (prefixWord ++ tailWord_5623739) baseStart_5623739 baseEnd_5623739 := by
    simpa [prefixWord, tailWord_5623739, baseEnd_5623739] using wordTrace_append hprefix tailTrace_5623739
  have hstable : (prefixWord ++ tailWord_5623739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623739).length < 2 ^ (prefixWord ++ tailWord_5623739).sum := by decide
  have hdescent : baseEnd_5623739 < baseStart_5623739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623756 : List Nat := [2, 2, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_5623756 : Nat := 118140960795 + 5623756 * 2 ^ 59
def prefixEnd_5623756 : Nat := 4983230072969 + 3 ^ 40 * 5623756 * 2
def baseEnd_5623756 : Nat := 962563303868801420828941

theorem tailTrace_5623756 : CollatzResearch.WordTrace tailWord_5623756 prefixEnd_5623756 962563303868801420828941 := by
  unfold tailWord_5623756
  simp only [CollatzResearch.WordTrace]
  refine ⟨102557616107049973951849561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136743488142733298602466081 102557616107049973951849561)
  ·
    refine ⟨76918212080287480463887171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102557616107049973951849561 76918212080287480463887171)
    ·
      refine ⟨115377318120431220695830757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76918212080287480463887171 115377318120431220695830757)
      ·
        refine ⟨21633247147580853880468267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115377318120431220695830757 21633247147580853880468267)
        ·
          refine ⟨32449870721371280820702401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21633247147580853880468267 32449870721371280820702401)
          ·
            refine ⟨24337403041028460615526801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32449870721371280820702401 24337403041028460615526801)
            ·
              refine ⟨18253052280771345461645101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24337403041028460615526801 18253052280771345461645101)
              ·
                refine ⟨6844894605289254548116913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18253052280771345461645101 6844894605289254548116913)
                ·
                  refine ⟨5133670953966940911087685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6844894605289254548116913 5133670953966940911087685)
                  ·
                    refine ⟨962563303868801420828941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133670953966940911087685 962563303868801420828941)
                    ·
                      rfl

theorem cell23_5623756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_5623756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623756 prefixEnd_5623756 := by exact prefixLift 5623756
  have htrace : WordTrace (prefixWord ++ tailWord_5623756) baseStart_5623756 baseEnd_5623756 := by
    simpa [prefixWord, tailWord_5623756, baseEnd_5623756] using wordTrace_append hprefix tailTrace_5623756
  have hstable : (prefixWord ++ tailWord_5623756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623756).length < 2 ^ (prefixWord ++ tailWord_5623756).sum := by decide
  have hdescent : baseEnd_5623756 < baseStart_5623756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623759 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4]
def baseStart_5623759 : Nat := 118140960795 + 5623759 * 2 ^ 59
def prefixEnd_5623759 : Nat := 4983230072969 + 3 ^ 40 * 5623759 * 2
def baseEnd_5623759 : Nat := 2887691452048367750749309

theorem tailTrace_5623759 : CollatzResearch.WordTrace tailWord_5623759 prefixEnd_5623759 2887691452048367750749309 := by
  unfold tailWord_5623759
  simp only [CollatzResearch.WordTrace]
  refine ⟨205115341633089079416058331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136743561088726052944038887 205115341633089079416058331)
  ·
    refine ⟨307673012449633619124087497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205115341633089079416058331 307673012449633619124087497)
    ·
      refine ⟨230754759337225214343065623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307673012449633619124087497 230754759337225214343065623)
      ·
        refine ⟨346132139005837821514598435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230754759337225214343065623 346132139005837821514598435)
        ·
          refine ⟨519198208508756732271897653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346132139005837821514598435 519198208508756732271897653)
          ·
            refine ⟨48674832047695943650490405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 519198208508756732271897653 48674832047695943650490405)
            ·
              refine ⟨9126531008942989434466951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48674832047695943650490405 9126531008942989434466951)
              ·
                refine ⟨13689796513414484151700427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126531008942989434466951 13689796513414484151700427)
                ·
                  refine ⟨20534694770121726227550641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13689796513414484151700427 20534694770121726227550641)
                  ·
                    refine ⟨15401021077591294670662981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20534694770121726227550641 15401021077591294670662981)
                    ·
                      refine ⟨2887691452048367750749309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15401021077591294670662981 2887691452048367750749309)
                      ·
                        rfl

theorem cell23_5623759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 4].length) (baseStart_5623759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623759 prefixEnd_5623759 := by exact prefixLift 5623759
  have htrace : WordTrace (prefixWord ++ tailWord_5623759) baseStart_5623759 baseEnd_5623759 := by
    simpa [prefixWord, tailWord_5623759, baseEnd_5623759] using wordTrace_append hprefix tailTrace_5623759
  have hstable : (prefixWord ++ tailWord_5623759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623759).length < 2 ^ (prefixWord ++ tailWord_5623759).sum := by decide
  have hdescent : baseEnd_5623759 < baseStart_5623759 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623780 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_5623780 : Nat := 118140960795 + 5623780 * 2 ^ 59
def prefixEnd_5623780 : Nat := 4983230072969 + 3 ^ 40 * 5623780 * 2
def baseEnd_5623780 : Nat := 2887702235142112168586713

theorem tailTrace_5623780 : CollatzResearch.WordTrace tailWord_5623780 prefixEnd_5623780 2887702235142112168586713 := by
  unfold tailWord_5623780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102558053783006500001286397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136744071710675333335048529 102558053783006500001286397)
  ·
    refine ⟨38459270168627437500482399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102558053783006500001286397 38459270168627437500482399)
    ·
      refine ⟨57688905252941156250723599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38459270168627437500482399 57688905252941156250723599)
      ·
        refine ⟨86533357879411734376085399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57688905252941156250723599 86533357879411734376085399)
        ·
          refine ⟨129800036819117601564128099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86533357879411734376085399 129800036819117601564128099)
          ·
            refine ⟨194700055228676402346192149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129800036819117601564128099 194700055228676402346192149)
            ·
              refine ⟨9126565088844206359977757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194700055228676402346192149 9126565088844206359977757)
              ·
                refine ⟨3422461908316577384991659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9126565088844206359977757 3422461908316577384991659)
                ·
                  refine ⟨5133692862474866077487489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422461908316577384991659 5133692862474866077487489)
                  ·
                    refine ⟨3850269646856149558115617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133692862474866077487489 3850269646856149558115617)
                    ·
                      refine ⟨2887702235142112168586713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850269646856149558115617 2887702235142112168586713)
                      ·
                        rfl

theorem cell23_5623780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_5623780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623780 prefixEnd_5623780 := by exact prefixLift 5623780
  have htrace : WordTrace (prefixWord ++ tailWord_5623780) baseStart_5623780 baseEnd_5623780 := by
    simpa [prefixWord, tailWord_5623780, baseEnd_5623780] using wordTrace_append hprefix tailTrace_5623780
  have hstable : (prefixWord ++ tailWord_5623780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623780).length < 2 ^ (prefixWord ++ tailWord_5623780).sum := by decide
  have hdescent : baseEnd_5623780 < baseStart_5623780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623783 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 3]
def baseStart_5623783 : Nat := 118140960795 + 5623783 * 2 ^ 59
def prefixEnd_5623783 : Nat := 4983230072969 + 3 ^ 40 * 5623783 * 2
def baseEnd_5623783 : Nat := 2887703775584075656849199

theorem tailTrace_5623783 : CollatzResearch.WordTrace tailWord_5623783 prefixEnd_5623783 2887703775584075656849199 := by
  unfold tailWord_5623783
  simp only [CollatzResearch.WordTrace]
  refine ⟨205116216985002131514932003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136744144656668087676621335 205116216985002131514932003)
  ·
    refine ⟨307674325477503197272398005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205116216985002131514932003 307674325477503197272398005)
    ·
      refine ⟨28844468013515924744287313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 307674325477503197272398005 28844468013515924744287313)
      ·
        refine ⟨21633351010136943558215485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28844468013515924744287313 21633351010136943558215485)
        ·
          refine ⟨8112506628801353834330807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21633351010136943558215485 8112506628801353834330807)
          ·
            refine ⟨12168759943202030751496211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8112506628801353834330807 12168759943202030751496211)
            ·
              refine ⟨18253139914803046127244317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12168759943202030751496211 18253139914803046127244317)
              ·
                refine ⟨6844927468051142297716619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18253139914803046127244317 6844927468051142297716619)
                ·
                  refine ⟨10267391202076713446574929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844927468051142297716619 10267391202076713446574929)
                  ·
                    refine ⟨7700543401557535084931197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10267391202076713446574929 7700543401557535084931197)
                    ·
                      refine ⟨2887703775584075656849199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700543401557535084931197 2887703775584075656849199)
                      ·
                        rfl

theorem cell23_5623783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_5623783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623783 prefixEnd_5623783 := by exact prefixLift 5623783
  have htrace : WordTrace (prefixWord ++ tailWord_5623783) baseStart_5623783 baseEnd_5623783 := by
    simpa [prefixWord, tailWord_5623783, baseEnd_5623783] using wordTrace_append hprefix tailTrace_5623783
  have hstable : (prefixWord ++ tailWord_5623783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623783).length < 2 ^ (prefixWord ++ tailWord_5623783).sum := by decide
  have hdescent : baseEnd_5623783 < baseStart_5623783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623814 : List Nat := [6, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5623814 : Nat := 118140960795 + 5623814 * 2 ^ 59
def prefixEnd_5623814 : Nat := 4983230072969 + 3 ^ 40 * 5623814 * 2
def baseEnd_5623814 : Nat := 2887719693484365035561557

theorem tailTrace_5623814 : CollatzResearch.WordTrace tailWord_5623814 prefixEnd_5623814 2887719693484365035561557 := by
  unfold tailWord_5623814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409917113996556994040953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136744898431926549206206997 6409917113996556994040953)
  ·
    refine ⟨4807437835497417745530715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409917113996556994040953 4807437835497417745530715)
    ·
      refine ⟨7211156753246126618296073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807437835497417745530715 7211156753246126618296073)
      ·
        refine ⟨5408367564934594963722055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7211156753246126618296073 5408367564934594963722055)
        ·
          refine ⟨8112551347401892445583083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408367564934594963722055 8112551347401892445583083)
          ·
            refine ⟨12168827021102838668374625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8112551347401892445583083 12168827021102838668374625)
            ·
              refine ⟨9126620265827129001280969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12168827021102838668374625 9126620265827129001280969)
              ·
                refine ⟨6844965199370346750960727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9126620265827129001280969 6844965199370346750960727)
                ·
                  refine ⟨10267447799055520126441091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6844965199370346750960727 10267447799055520126441091)
                  ·
                    refine ⟨15401171698583280189661637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10267447799055520126441091 15401171698583280189661637)
                    ·
                      refine ⟨2887719693484365035561557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15401171698583280189661637 2887719693484365035561557)
                      ·
                        rfl

theorem cell23_5623814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5623814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623814 prefixEnd_5623814 := by exact prefixLift 5623814
  have htrace : WordTrace (prefixWord ++ tailWord_5623814) baseStart_5623814 baseEnd_5623814 := by
    simpa [prefixWord, tailWord_5623814, baseEnd_5623814] using wordTrace_append hprefix tailTrace_5623814
  have hstable : (prefixWord ++ tailWord_5623814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623814).length < 2 ^ (prefixWord ++ tailWord_5623814).sum := by decide
  have hdescent : baseEnd_5623814 < baseStart_5623814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623839 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5]
def baseStart_5623839 : Nat := 118140960795 + 5623839 * 2 ^ 59
def prefixEnd_5623839 : Nat := 4983230072969 + 3 ^ 40 * 5623839 * 2
def baseEnd_5623839 : Nat := 2887732530500727437748941

theorem tailTrace_5623839 : CollatzResearch.WordTrace tailWord_5623839 prefixEnd_5623839 2887732530500727437748941 := by
  unfold tailWord_5623839
  simp only [CollatzResearch.WordTrace]
  refine ⟨205118259472799253078970571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136745506315199502052647047 205118259472799253078970571)
  ·
    refine ⟨307677389209198879618455857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205118259472799253078970571 307677389209198879618455857)
    ·
      refine ⟨230758041906899159713841893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307677389209198879618455857 230758041906899159713841893)
      ·
        refine ⟨43267132857543592446345355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230758041906899159713841893 43267132857543592446345355)
        ·
          refine ⟨64900699286315388669518033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43267132857543592446345355 64900699286315388669518033)
          ·
            refine ⟨48675524464736541502138525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64900699286315388669518033 48675524464736541502138525)
            ·
              refine ⟨18253321674276203063301947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48675524464736541502138525 18253321674276203063301947)
              ·
                refine ⟨27379982511414304594952921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18253321674276203063301947 27379982511414304594952921)
                ·
                  refine ⟨20534986883560728446214691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27379982511414304594952921 20534986883560728446214691)
                  ·
                    refine ⟨30802480325341092669322037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20534986883560728446214691 30802480325341092669322037)
                    ·
                      refine ⟨2887732530500727437748941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30802480325341092669322037 2887732530500727437748941)
                      ·
                        rfl

theorem cell23_5623839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_5623839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623839 prefixEnd_5623839 := by exact prefixLift 5623839
  have htrace : WordTrace (prefixWord ++ tailWord_5623839) baseStart_5623839 baseEnd_5623839 := by
    simpa [prefixWord, tailWord_5623839, baseEnd_5623839] using wordTrace_append hprefix tailTrace_5623839
  have hstable : (prefixWord ++ tailWord_5623839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623839).length < 2 ^ (prefixWord ++ tailWord_5623839).sum := by decide
  have hdescent : baseEnd_5623839 < baseStart_5623839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623859 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 7]
def baseStart_5623859 : Nat := 118140960795 + 5623859 * 2 ^ 59
def prefixEnd_5623859 : Nat := 4983230072969 + 3 ^ 40 * 5623859 * 2
def baseEnd_5623859 : Nat := 320860311123757484388761

theorem tailTrace_5623859 : CollatzResearch.WordTrace tailWord_5623859 prefixEnd_5623859 320860311123757484388761 := by
  unfold tailWord_5623859
  simp only [CollatzResearch.WordTrace]
  refine ⟨205118988932726796494698631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136745992621817864329799087 205118988932726796494698631)
  ·
    refine ⟨307678483399090194742047947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205118988932726796494698631 307678483399090194742047947)
    ·
      refine ⟨461517725098635292113071921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307678483399090194742047947 461517725098635292113071921)
      ·
        refine ⟨346138293823976469084803941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461517725098635292113071921 346138293823976469084803941)
        ·
          refine ⟨64900930091995587953400739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346138293823976469084803941 64900930091995587953400739)
          ·
            refine ⟨97351395137993381930101109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64900930091995587953400739 97351395137993381930101109)
            ·
              refine ⟨9126693294186879555946979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97351395137993381930101109 9126693294186879555946979)
              ·
                refine ⟨13690039941280319333920469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126693294186879555946979 13690039941280319333920469)
                ·
                  refine ⟨320860311123757484388761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13690039941280319333920469 320860311123757484388761)
                  ·
                    rfl

theorem cell23_5623859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 7].length) (baseStart_5623859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623859 prefixEnd_5623859 := by exact prefixLift 5623859
  have htrace : WordTrace (prefixWord ++ tailWord_5623859) baseStart_5623859 baseEnd_5623859 := by
    simpa [prefixWord, tailWord_5623859, baseEnd_5623859] using wordTrace_append hprefix tailTrace_5623859
  have hstable : (prefixWord ++ tailWord_5623859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623859).length < 2 ^ (prefixWord ++ tailWord_5623859).sum := by decide
  have hdescent : baseEnd_5623859 < baseStart_5623859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623970 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_5623970 : Nat := 118140960795 + 5623970 * 2 ^ 59
def prefixEnd_5623970 : Nat := 4983230072969 + 3 ^ 40 * 5623970 * 2
def baseEnd_5623970 : Nat := 962599932155488808403613

theorem tailTrace_5623970 : CollatzResearch.WordTrace tailWord_5623970 prefixEnd_5623970 962599932155488808403613 := by
  unfold tailWord_5623970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51280759358831165612997341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136748691623549774967992909 51280759358831165612997341)
  ·
    refine ⟨19230284759561687104874003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51280759358831165612997341 19230284759561687104874003)
    ·
      refine ⟨28845427139342530657311005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19230284759561687104874003 28845427139342530657311005)
      ·
        refine ⟨10817035177253448996491627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28845427139342530657311005 10817035177253448996491627)
        ·
          refine ⟨16225552765880173494737441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817035177253448996491627 16225552765880173494737441)
          ·
            refine ⟨12169164574410130121053081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16225552765880173494737441 12169164574410130121053081)
            ·
              refine ⟨9126873430807597590789811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12169164574410130121053081 9126873430807597590789811)
              ·
                refine ⟨13690310146211396386184717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9126873430807597590789811 13690310146211396386184717)
                ·
                  refine ⟨5133866304829273644819269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13690310146211396386184717 5133866304829273644819269)
                  ·
                    refine ⟨962599932155488808403613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133866304829273644819269 962599932155488808403613)
                    ·
                      rfl

theorem cell23_5623970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_5623970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623970 prefixEnd_5623970 := by exact prefixLift 5623970
  have htrace : WordTrace (prefixWord ++ tailWord_5623970) baseStart_5623970 baseEnd_5623970 := by
    simpa [prefixWord, tailWord_5623970, baseEnd_5623970] using wordTrace_append hprefix tailTrace_5623970
  have hstable : (prefixWord ++ tailWord_5623970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623970).length < 2 ^ (prefixWord ++ tailWord_5623970).sum := by decide
  have hdescent : baseEnd_5623970 < baseStart_5623970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5623993 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_5623993 : Nat := 118140960795 + 5623993 * 2 ^ 59
def prefixEnd_5623993 : Nat := 4983230072969 + 3 ^ 40 * 5623993 * 2
def baseEnd_5623993 : Nat := 2887811606521519835223233

theorem tailTrace_5623993 : CollatzResearch.WordTrace tailWord_5623993 prefixEnd_5623993 2887811606521519835223233 := by
  unfold tailWord_5623993
  simp only [CollatzResearch.WordTrace]
  refine ⟨205123876314241337380076633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136749250876160891586717755 205123876314241337380076633)
  ·
    refine ⟨153842907235681003035057475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205123876314241337380076633 153842907235681003035057475)
    ·
      refine ⟨230764360853521504552586213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153842907235681003035057475 230764360853521504552586213)
      ·
        refine ⟨43268317660035282103609915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230764360853521504552586213 43268317660035282103609915)
        ·
          refine ⟨64902476490052923155414873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43268317660035282103609915 64902476490052923155414873)
          ·
            refine ⟨48676857367539692366561155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64902476490052923155414873 48676857367539692366561155)
            ·
              refine ⟨73015286051309538549841733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48676857367539692366561155 73015286051309538549841733)
              ·
                refine ⟨13690366134620538478095325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73015286051309538549841733 13690366134620538478095325)
                ·
                  refine ⟨5133887300482701929285747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13690366134620538478095325 5133887300482701929285747)
                  ·
                    refine ⟨7700830950724052893928621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133887300482701929285747 7700830950724052893928621)
                    ·
                      refine ⟨2887811606521519835223233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700830950724052893928621 2887811606521519835223233)
                      ·
                        rfl

theorem cell23_5623993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_5623993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5623993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5623993 prefixEnd_5623993 := by exact prefixLift 5623993
  have htrace : WordTrace (prefixWord ++ tailWord_5623993) baseStart_5623993 baseEnd_5623993 := by
    simpa [prefixWord, tailWord_5623993, baseEnd_5623993] using wordTrace_append hprefix tailTrace_5623993
  have hstable : (prefixWord ++ tailWord_5623993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5623993).length < 2 ^ (prefixWord ++ tailWord_5623993).sum := by decide
  have hdescent : baseEnd_5623993 < baseStart_5623993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5623993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624036 : List Nat := [2, 3, 1, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_5624036 : Nat := 118140960795 + 5624036 * 2 ^ 59
def prefixEnd_5624036 : Nat := 4983230072969 + 3 ^ 40 * 5624036 * 2
def baseEnd_5624036 : Nat := 2887833686189663166985535

theorem tailTrace_5624036 : CollatzResearch.WordTrace tailWord_5624036 prefixEnd_5624036 2887833686189663166985535 := by
  unfold tailWord_5624036
  simp only [CollatzResearch.WordTrace]
  refine ⟨102562722326542777861945981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136750296435390370482594641 102562722326542777861945981)
  ·
    refine ⟨38461020872453541698229743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102562722326542777861945981 38461020872453541698229743)
    ·
      refine ⟨57691531308680312547344615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38461020872453541698229743 57691531308680312547344615)
      ·
        refine ⟨86537296963020468821016923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57691531308680312547344615 86537296963020468821016923)
        ·
          refine ⟨129805945444530703231525385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86537296963020468821016923 129805945444530703231525385)
          ·
            refine ⟨97354459083398027423644039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129805945444530703231525385 97354459083398027423644039)
            ·
              refine ⟨146031688625097041135466059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97354459083398027423644039 146031688625097041135466059)
              ·
                refine ⟨219047532937645561703199089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146031688625097041135466059 219047532937645561703199089)
                ·
                  refine ⟨164285649703234171277399317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219047532937645561703199089 164285649703234171277399317)
                  ·
                    refine ⟨7700889829839101778628093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164285649703234171277399317 7700889829839101778628093)
                    ·
                      refine ⟨2887833686189663166985535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700889829839101778628093 2887833686189663166985535)
                      ·
                        rfl

theorem cell23_5624036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_5624036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624036 prefixEnd_5624036 := by exact prefixLift 5624036
  have htrace : WordTrace (prefixWord ++ tailWord_5624036) baseStart_5624036 baseEnd_5624036 := by
    simpa [prefixWord, tailWord_5624036, baseEnd_5624036] using wordTrace_append hprefix tailTrace_5624036
  have hstable : (prefixWord ++ tailWord_5624036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624036).length < 2 ^ (prefixWord ++ tailWord_5624036).sum := by decide
  have hdescent : baseEnd_5624036 < baseStart_5624036 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624043 : List Nat := [1, 1, 1, 1, 2, 5, 3, 3, 2, 4]
def baseStart_5624043 : Nat := 118140960795 + 5624043 * 2 ^ 59
def prefixEnd_5624043 : Nat := 4983230072969 + 3 ^ 40 * 5624043 * 2
def baseEnd_5624043 : Nat := 962612426851414879866001

theorem tailTrace_5624043 : CollatzResearch.WordTrace tailWord_5624043 prefixEnd_5624043 962612426851414879866001 := by
  unfold tailWord_5624043
  simp only [CollatzResearch.WordTrace]
  refine ⟨205125699964060195919396783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136750466642706797279597855 205125699964060195919396783)
  ·
    refine ⟨307688549946090293879095175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205125699964060195919396783 307688549946090293879095175)
    ·
      refine ⟨461532824919135440818642763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307688549946090293879095175 461532824919135440818642763)
      ·
        refine ⟨692299237378703161227964145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461532824919135440818642763 692299237378703161227964145)
        ·
          refine ⟨519224428034027370920973109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692299237378703161227964145 519224428034027370920973109)
          ·
            refine ⟨48677290128190066023841229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 519224428034027370920973109 48677290128190066023841229)
            ·
              refine ⟨18253983798071274758940461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48677290128190066023841229 18253983798071274758940461)
              ·
                refine ⟨6845243924276728034602673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18253983798071274758940461 6845243924276728034602673)
                ·
                  refine ⟨5133932943207546025952005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6845243924276728034602673 5133932943207546025952005)
                  ·
                    refine ⟨962612426851414879866001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5133932943207546025952005 962612426851414879866001)
                    ·
                      rfl

theorem cell23_5624043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 3, 2, 4].length) (baseStart_5624043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624043 prefixEnd_5624043 := by exact prefixLift 5624043
  have htrace : WordTrace (prefixWord ++ tailWord_5624043) baseStart_5624043 baseEnd_5624043 := by
    simpa [prefixWord, tailWord_5624043, baseEnd_5624043] using wordTrace_append hprefix tailTrace_5624043
  have hstable : (prefixWord ++ tailWord_5624043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624043).length < 2 ^ (prefixWord ++ tailWord_5624043).sum := by decide
  have hdescent : baseEnd_5624043 < baseStart_5624043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624050 : List Nat := [3, 2, 1, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_5624050 : Nat := 118140960795 + 5624050 * 2 ^ 59
def prefixEnd_5624050 : Nat := 4983230072969 + 3 ^ 40 * 5624050 * 2
def baseEnd_5624050 : Nat := 2887840874918826112210471

theorem tailTrace_5624050 : CollatzResearch.WordTrace tailWord_5624050 prefixEnd_5624050 2887840874918826112210471 := by
  unfold tailWord_5624050
  simp only [CollatzResearch.WordTrace]
  refine ⟨51281488818758709028725401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136750636850023224076601069 51281488818758709028725401)
  ·
    refine ⟨38461116614069031771544051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51281488818758709028725401 38461116614069031771544051)
    ·
      refine ⟨57691674921103547657316077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38461116614069031771544051 57691674921103547657316077)
      ·
        refine ⟨21634378095413830371493529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57691674921103547657316077 21634378095413830371493529)
        ·
          refine ⟨16225783571560372778620147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21634378095413830371493529 16225783571560372778620147)
          ·
            refine ⟨24338675357340559167930221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16225783571560372778620147 24338675357340559167930221)
            ·
              refine ⟨9127003259002709687973833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24338675357340559167930221 9127003259002709687973833)
              ·
                refine ⟨6845252444252032265980375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9127003259002709687973833 6845252444252032265980375)
                ·
                  refine ⟨10267878666378048398970563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6845252444252032265980375 10267878666378048398970563)
                  ·
                    refine ⟨15401817999567072598455845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10267878666378048398970563 15401817999567072598455845)
                    ·
                      refine ⟨2887840874918826112210471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15401817999567072598455845 2887840874918826112210471)
                      ·
                        rfl

theorem cell23_5624050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_5624050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624050 prefixEnd_5624050 := by exact prefixLift 5624050
  have htrace : WordTrace (prefixWord ++ tailWord_5624050) baseStart_5624050 baseEnd_5624050 := by
    simpa [prefixWord, tailWord_5624050, baseEnd_5624050] using wordTrace_append hprefix tailTrace_5624050
  have hstable : (prefixWord ++ tailWord_5624050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624050).length < 2 ^ (prefixWord ++ tailWord_5624050).sum := by decide
  have hdescent : baseEnd_5624050 < baseStart_5624050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624067 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 1, 2, 2]
def baseStart_5624067 : Nat := 118140960795 + 5624067 * 2 ^ 59
def prefixEnd_5624067 : Nat := 4983230072969 + 3 ^ 40 * 5624067 * 2
def baseEnd_5624067 : Nat := 2887849604089952545697893

theorem tailTrace_5624067 : CollatzResearch.WordTrace tailWord_5624067 prefixEnd_5624067 2887849604089952545697893 := by
  unfold tailWord_5624067
  simp only [CollatzResearch.WordTrace]
  refine ⟨205126575315973248018270455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136751050210648832012180303 205126575315973248018270455)
  ·
    refine ⟨307689862973959872027405683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205126575315973248018270455 307689862973959872027405683)
    ·
      refine ⟨461534794460939808041108525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307689862973959872027405683 461534794460939808041108525)
      ·
        refine ⟨173075547922852428015415697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461534794460939808041108525 173075547922852428015415697)
        ·
          refine ⟨129806660942139321011561773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173075547922852428015415697 129806660942139321011561773)
          ·
            refine ⟨48677497853302245379335665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129806660942139321011561773 48677497853302245379335665)
            ·
              refine ⟨36508123389976684034501749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48677497853302245379335665 36508123389976684034501749)
              ·
                refine ⟨3422636567810314128234539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36508123389976684034501749 3422636567810314128234539)
                ·
                  refine ⟨5133954851715471192351809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3422636567810314128234539 5133954851715471192351809)
                  ·
                    refine ⟨3850466138786603394263857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5133954851715471192351809 3850466138786603394263857)
                    ·
                      refine ⟨2887849604089952545697893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850466138786603394263857 2887849604089952545697893)
                      ·
                        rfl

theorem cell23_5624067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_5624067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624067 prefixEnd_5624067 := by exact prefixLift 5624067
  have htrace : WordTrace (prefixWord ++ tailWord_5624067) baseStart_5624067 baseEnd_5624067 := by
    simpa [prefixWord, tailWord_5624067, baseEnd_5624067] using wordTrace_append hprefix tailTrace_5624067
  have hstable : (prefixWord ++ tailWord_5624067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624067).length < 2 ^ (prefixWord ++ tailWord_5624067).sum := by decide
  have hdescent : baseEnd_5624067 < baseStart_5624067 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624083 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 3]
def baseStart_5624083 : Nat := 118140960795 + 5624083 * 2 ^ 59
def prefixEnd_5624083 : Nat := 4983230072969 + 3 ^ 40 * 5624083 * 2
def baseEnd_5624083 : Nat := 2887857819780424483097819

theorem tailTrace_5624083 : CollatzResearch.WordTrace tailWord_5624083 prefixEnd_5624083 2887857819780424483097819 := by
  unfold tailWord_5624083
  simp only [CollatzResearch.WordTrace]
  refine ⟨205127158883915282750852903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136751439255943521833901935 205127158883915282750852903)
  ·
    refine ⟨307690738325872924126279355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205127158883915282750852903 307690738325872924126279355)
    ·
      refine ⟨461536107488809386189419033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307690738325872924126279355 461536107488809386189419033)
      ·
        refine ⟨346152080616607039642064275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461536107488809386189419033 346152080616607039642064275)
        ·
          refine ⟨519228120924910559463096413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346152080616607039642064275 519228120924910559463096413)
          ·
            refine ⟨194710545346841459798661155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519228120924910559463096413 194710545346841459798661155)
            ·
              refine ⟨292065818020262189697991733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194710545346841459798661155 292065818020262189697991733)
              ·
                refine ⟨27381170439399580284186725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292065818020262189697991733 27381170439399580284186725)
                ·
                  refine ⟨5133969457387421303285011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27381170439399580284186725 5133969457387421303285011)
                  ·
                    refine ⟨7700954186081131954927517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5133969457387421303285011 7700954186081131954927517)
                    ·
                      refine ⟨2887857819780424483097819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700954186081131954927517 2887857819780424483097819)
                      ·
                        rfl

theorem cell23_5624083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_5624083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624083 prefixEnd_5624083 := by exact prefixLift 5624083
  have htrace : WordTrace (prefixWord ++ tailWord_5624083) baseStart_5624083 baseEnd_5624083 := by
    simpa [prefixWord, tailWord_5624083, baseEnd_5624083] using wordTrace_append hprefix tailTrace_5624083
  have hstable : (prefixWord ++ tailWord_5624083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624083).length < 2 ^ (prefixWord ++ tailWord_5624083).sum := by decide
  have hdescent : baseEnd_5624083 < baseStart_5624083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624090 : List Nat := [3, 1, 1, 3, 5, 1, 1, 8]
def baseStart_5624090 : Nat := 118140960795 + 5624090 * 2 ^ 59
def prefixEnd_5624090 : Nat := 4983230072969 + 3 ^ 40 * 5624090 * 2
def baseEnd_5624090 : Nat := 106957830153518739100381

theorem tailTrace_5624090 : CollatzResearch.WordTrace tailWord_5624090 prefixEnd_5624090 106957830153518739100381 := by
  unfold tailWord_5624090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51281853548722480736589431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136751609463259948630905149 51281853548722480736589431)
  ·
    refine ⟨76922780323083721104884147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51281853548722480736589431 76922780323083721104884147)
    ·
      refine ⟨115384170484625581657326221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76922780323083721104884147 115384170484625581657326221)
      ·
        refine ⟨43269063931734593121497333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115384170484625581657326221 43269063931734593121497333)
        ·
          refine ⟨4056474743600118105140375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43269063931734593121497333 4056474743600118105140375)
          ·
            refine ⟨6084712115400177157710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056474743600118105140375 6084712115400177157710563)
            ·
              refine ⟨9127068173100265736565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6084712115400177157710563 9127068173100265736565845)
              ·
                refine ⟨106957830153518739100381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9127068173100265736565845 106957830153518739100381)
                ·
                  rfl

theorem cell23_5624090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_5624090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624090 prefixEnd_5624090 := by exact prefixLift 5624090
  have htrace : WordTrace (prefixWord ++ tailWord_5624090) baseStart_5624090 baseEnd_5624090 := by
    simpa [prefixWord, tailWord_5624090, baseEnd_5624090] using wordTrace_append hprefix tailTrace_5624090
  have hstable : (prefixWord ++ tailWord_5624090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624090).length < 2 ^ (prefixWord ++ tailWord_5624090).sum := by decide
  have hdescent : baseEnd_5624090 < baseStart_5624090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624100 : List Nat := [2, 3, 1, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_5624100 : Nat := 118140960795 + 5624100 * 2 ^ 59
def prefixEnd_5624100 : Nat := 4983230072969 + 3 ^ 40 * 5624100 * 2
def baseEnd_5624100 : Nat := 2887866548951550916585241

theorem tailTrace_5624100 : CollatzResearch.WordTrace tailWord_5624100 prefixEnd_5624100 2887866548951550916585241 := by
  unfold tailWord_5624100
  simp only [CollatzResearch.WordTrace]
  refine ⟨102563889462426847327110877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136751852616569129769481169 102563889462426847327110877)
  ·
    refine ⟨38461458548410067747666579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102563889462426847327110877 38461458548410067747666579)
    ·
      refine ⟨57692187822615101621499869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38461458548410067747666579 57692187822615101621499869)
      ·
        refine ⟨21634570433480663108062451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57692187822615101621499869 21634570433480663108062451)
        ·
          refine ⟨32451855650220994662093677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21634570433480663108062451 32451855650220994662093677)
          ·
            refine ⟨12169445868832872998285129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32451855650220994662093677 12169445868832872998285129)
            ·
              refine ⟨9127084401624654748713847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12169445868832872998285129 9127084401624654748713847)
              ·
                refine ⟨13690626602436982123070771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9127084401624654748713847 13690626602436982123070771)
                ·
                  refine ⟨20535939903655473184606157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13690626602436982123070771 20535939903655473184606157)
                  ·
                    refine ⟨7700977463870802444227309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20535939903655473184606157 7700977463870802444227309)
                    ·
                      refine ⟨2887866548951550916585241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7700977463870802444227309 2887866548951550916585241)
                      ·
                        rfl

theorem cell23_5624100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_5624100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624100 prefixEnd_5624100 := by exact prefixLift 5624100
  have htrace : WordTrace (prefixWord ++ tailWord_5624100) baseStart_5624100 baseEnd_5624100 := by
    simpa [prefixWord, tailWord_5624100, baseEnd_5624100] using wordTrace_append hprefix tailTrace_5624100
  have hstable : (prefixWord ++ tailWord_5624100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624100).length < 2 ^ (prefixWord ++ tailWord_5624100).sum := by decide
  have hdescent : baseEnd_5624100 < baseStart_5624100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624158 : List Nat := [4, 4, 2, 1, 2, 1, 2, 7]
def baseStart_5624158 : Nat := 118140960795 + 5624158 * 2 ^ 59
def prefixEnd_5624158 : Nat := 4983230072969 + 3 ^ 40 * 5624158 * 2
def baseEnd_5624158 : Nat := 106959123364055988505925

theorem tailTrace_5624158 : CollatzResearch.WordTrace tailWord_5624158 prefixEnd_5624158 106959123364055988505925 := by
  unfold tailWord_5624158
  simp only [CollatzResearch.WordTrace]
  refine ⟨25641236794830446319979141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136753262905762380373222085 25641236794830446319979141)
  ·
    refine ⟨4807731899030708684996089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25641236794830446319979141 4807731899030708684996089)
    ·
      refine ⟨3605798924273031513747067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4807731899030708684996089 3605798924273031513747067)
      ·
        refine ⟨5408698386409547270620601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605798924273031513747067 5408698386409547270620601)
        ·
          refine ⟨4056523789807160452965451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5408698386409547270620601 4056523789807160452965451)
          ·
            refine ⟨6084785684710740679448177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4056523789807160452965451 6084785684710740679448177)
            ·
              refine ⟨4563589263533055509586133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6084785684710740679448177 4563589263533055509586133)
              ·
                refine ⟨106959123364055988505925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4563589263533055509586133 106959123364055988505925)
                ·
                  rfl

theorem cell23_5624158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_5624158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624158 prefixEnd_5624158 := by exact prefixLift 5624158
  have htrace : WordTrace (prefixWord ++ tailWord_5624158) baseStart_5624158 baseEnd_5624158 := by
    simpa [prefixWord, tailWord_5624158, baseEnd_5624158] using wordTrace_append hprefix tailTrace_5624158
  have hstable : (prefixWord ++ tailWord_5624158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624158).length < 2 ^ (prefixWord ++ tailWord_5624158).sum := by decide
  have hdescent : baseEnd_5624158 < baseStart_5624158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624200 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5624200 : Nat := 118140960795 + 5624200 * 2 ^ 59
def prefixEnd_5624200 : Nat := 4983230072969 + 3 ^ 40 * 5624200 * 2
def baseEnd_5624200 : Nat := 2887917897017000525334781

theorem tailTrace_5624200 : CollatzResearch.WordTrace tailWord_5624200 prefixEnd_5624200 2887917897017000525334781 := by
  unfold tailWord_5624200
  simp only [CollatzResearch.WordTrace]
  refine ⟨102565713112245705866431027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136754284149660941155241369 102565713112245705866431027)
  ·
    refine ⟨153848569668368558799646541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102565713112245705866431027 153848569668368558799646541)
    ·
      refine ⟨57693213625638209549867453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153848569668368558799646541 57693213625638209549867453)
      ·
        refine ⟨21634955109614328581200295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57693213625638209549867453 21634955109614328581200295)
        ·
          refine ⟨32452432664421492871800443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21634955109614328581200295 32452432664421492871800443)
          ·
            refine ⟨48678648996632239307700665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32452432664421492871800443 48678648996632239307700665)
            ·
              refine ⟨36508986747474179480775499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48678648996632239307700665 36508986747474179480775499)
              ·
                refine ⟨54763480121211269221163249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36508986747474179480775499 54763480121211269221163249)
                ·
                  refine ⟨41072610090908451915872437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54763480121211269221163249 41072610090908451915872437)
                  ·
                    refine ⟨3850557196022667367113041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41072610090908451915872437 3850557196022667367113041)
                    ·
                      refine ⟨2887917897017000525334781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850557196022667367113041 2887917897017000525334781)
                      ·
                        rfl

theorem cell23_5624200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5624200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624200 prefixEnd_5624200 := by exact prefixLift 5624200
  have htrace : WordTrace (prefixWord ++ tailWord_5624200) baseStart_5624200 baseEnd_5624200 := by
    simpa [prefixWord, tailWord_5624200, baseEnd_5624200] using wordTrace_append hprefix tailTrace_5624200
  have hstable : (prefixWord ++ tailWord_5624200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624200).length < 2 ^ (prefixWord ++ tailWord_5624200).sum := by decide
  have hdescent : baseEnd_5624200 < baseStart_5624200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624203 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5]
def baseStart_5624203 : Nat := 118140960795 + 5624203 * 2 ^ 59
def prefixEnd_5624203 : Nat := 4983230072969 + 3 ^ 40 * 5624203 * 2
def baseEnd_5624203 : Nat := 2887919437458964013597267

theorem tailTrace_5624203 : CollatzResearch.WordTrace tailWord_5624203 prefixEnd_5624203 2887919437458964013597267 := by
  unfold tailWord_5624203
  simp only [CollatzResearch.WordTrace]
  refine ⟨205131535643480543245221263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136754357095653695496814175 205131535643480543245221263)
  ·
    refine ⟨307697303465220814867831895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205131535643480543245221263 307697303465220814867831895)
    ·
      refine ⟨461545955197831222301747843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307697303465220814867831895 461545955197831222301747843)
      ·
        refine ⟨692318932796746833452621765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461545955197831222301747843 692318932796746833452621765)
        ·
          refine ⟨129809799899390031272366581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 692318932796746833452621765 129809799899390031272366581)
          ·
            refine ⟨12169668740567815431784367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129809799899390031272366581 12169668740567815431784367)
            ·
              refine ⟨18254503110851723147676551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12169668740567815431784367 18254503110851723147676551)
              ·
                refine ⟨27381754666277584721514827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18254503110851723147676551 27381754666277584721514827)
                ·
                  refine ⟨41072631999416377082272241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27381754666277584721514827 41072631999416377082272241)
                  ·
                    refine ⟨30804473999562282811704181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41072631999416377082272241 30804473999562282811704181)
                    ·
                      refine ⟨2887919437458964013597267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30804473999562282811704181 2887919437458964013597267)
                      ·
                        rfl

theorem cell23_5624203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_5624203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624203 prefixEnd_5624203 := by exact prefixLift 5624203
  have htrace : WordTrace (prefixWord ++ tailWord_5624203) baseStart_5624203 baseEnd_5624203 := by
    simpa [prefixWord, tailWord_5624203, baseEnd_5624203] using wordTrace_append hprefix tailTrace_5624203
  have hstable : (prefixWord ++ tailWord_5624203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624203).length < 2 ^ (prefixWord ++ tailWord_5624203).sum := by decide
  have hdescent : baseEnd_5624203 < baseStart_5624203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624213 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_5624213 : Nat := 118140960795 + 5624213 * 2 ^ 59
def prefixEnd_5624213 : Nat := 4983230072969 + 3 ^ 40 * 5624213 * 2
def baseEnd_5624213 : Nat := 2887924572265508974472221

theorem tailTrace_5624213 : CollatzResearch.WordTrace tailWord_5624213 prefixEnd_5624213 2887924572265508974472221 := by
  unfold tailWord_5624213
  simp only [CollatzResearch.WordTrace]
  refine ⟨205131900373444314953085293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136754600248962876635390195 205131900373444314953085293)
  ·
    refine ⟨76924462640041618107406985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205131900373444314953085293 76924462640041618107406985)
    ·
      refine ⟨57693346980031213580555239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76924462640041618107406985 57693346980031213580555239)
      ·
        refine ⟨86540020470046820370832859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57693346980031213580555239 86540020470046820370832859)
        ·
          refine ⟨129810030705070230556249289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86540020470046820370832859 129810030705070230556249289)
          ·
            refine ⟨97357523028802672917186967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129810030705070230556249289 97357523028802672917186967)
            ·
              refine ⟨146036284543204009375780451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97357523028802672917186967 146036284543204009375780451)
              ·
                refine ⟨219054426814806014063670677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146036284543204009375780451 219054426814806014063670677)
                ·
                  refine ⟨10268176256944031909234563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219054426814806014063670677 10268176256944031909234563)
                  ·
                    refine ⟨15402264385416047863851845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10268176256944031909234563 15402264385416047863851845)
                    ·
                      refine ⟨2887924572265508974472221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15402264385416047863851845 2887924572265508974472221)
                      ·
                        rfl

theorem cell23_5624213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_5624213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624213 prefixEnd_5624213 := by exact prefixLift 5624213
  have htrace : WordTrace (prefixWord ++ tailWord_5624213) baseStart_5624213 baseEnd_5624213 := by
    simpa [prefixWord, tailWord_5624213, baseEnd_5624213] using wordTrace_append hprefix tailTrace_5624213
  have hstable : (prefixWord ++ tailWord_5624213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624213).length < 2 ^ (prefixWord ++ tailWord_5624213).sum := by decide
  have hdescent : baseEnd_5624213 < baseStart_5624213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624233 : List Nat := [1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_5624233 : Nat := 118140960795 + 5624233 * 2 ^ 59
def prefixEnd_5624233 : Nat := 4983230072969 + 3 ^ 40 * 5624233 * 2
def baseEnd_5624233 : Nat := 2887934841878598896222129

theorem tailTrace_5624233 : CollatzResearch.WordTrace tailWord_5624233 prefixEnd_5624233 2887934841878598896222129 := by
  unfold tailWord_5624233
  simp only [CollatzResearch.WordTrace]
  refine ⟨205132629833371858368813353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136755086555581238912542235 205132629833371858368813353)
  ·
    refine ⟨153849472375028893776610015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205132629833371858368813353 153849472375028893776610015)
    ·
      refine ⟨230774208562543340664915023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153849472375028893776610015 230774208562543340664915023)
      ·
        refine ⟨346161312843815010997372535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230774208562543340664915023 346161312843815010997372535)
        ·
          refine ⟨519241969265722516496058803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346161312843815010997372535 519241969265722516496058803)
          ·
            refine ⟨778862953898583774744088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519241969265722516496058803 778862953898583774744088205)
            ·
              refine ⟨292073607711968915529033077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778862953898583774744088205 292073607711968915529033077)
              ·
                refine ⟨27381900722997085830846851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292073607711968915529033077 27381900722997085830846851)
                ·
                  refine ⟨41072851084495628746270277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27381900722997085830846851 41072851084495628746270277)
                  ·
                    refine ⟨7701159578342930389925677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41072851084495628746270277 7701159578342930389925677)
                    ·
                      refine ⟨2887934841878598896222129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701159578342930389925677 2887934841878598896222129)
                      ·
                        rfl

theorem cell23_5624233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_5624233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624233 prefixEnd_5624233 := by exact prefixLift 5624233
  have htrace : WordTrace (prefixWord ++ tailWord_5624233) baseStart_5624233 baseEnd_5624233 := by
    simpa [prefixWord, tailWord_5624233, baseEnd_5624233] using wordTrace_append hprefix tailTrace_5624233
  have hstable : (prefixWord ++ tailWord_5624233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624233).length < 2 ^ (prefixWord ++ tailWord_5624233).sum := by decide
  have hdescent : baseEnd_5624233 < baseStart_5624233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624274 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_5624274 : Nat := 118140960795 + 5624274 * 2 ^ 59
def prefixEnd_5624274 : Nat := 4983230072969 + 3 ^ 40 * 5624274 * 2
def baseEnd_5624274 : Nat := 962651964861811078603147

theorem tailTrace_5624274 : CollatzResearch.WordTrace tailWord_5624274 prefixEnd_5624274 962651964861811078603147 := by
  unfold tailWord_5624274
  simp only [CollatzResearch.WordTrace]
  refine ⟨51283531306555830592763969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136756083484148881580703917 51283531306555830592763969)
  ·
    refine ⟨38462648479916872944572977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51283531306555830592763969 38462648479916872944572977)
    ·
      refine ⟨28846986359937654708429733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38462648479916872944572977 28846986359937654708429733)
      ·
        refine ⟨5408809942488310257830575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28846986359937654708429733 5408809942488310257830575)
        ·
          refine ⟨8113214913732465386745863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408809942488310257830575 8113214913732465386745863)
          ·
            refine ⟨12169822370598698080118795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113214913732465386745863 12169822370598698080118795)
            ·
              refine ⟨18254733555898047120178193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12169822370598698080118795 18254733555898047120178193)
              ·
                refine ⟨13691050166923535340133645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18254733555898047120178193 13691050166923535340133645)
                ·
                  refine ⟨5134143812596325752550117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13691050166923535340133645 5134143812596325752550117)
                  ·
                    refine ⟨962651964861811078603147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134143812596325752550117 962651964861811078603147)
                    ·
                      rfl

theorem cell23_5624274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_5624274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624274 prefixEnd_5624274 := by exact prefixLift 5624274
  have htrace : WordTrace (prefixWord ++ tailWord_5624274) baseStart_5624274 baseEnd_5624274 := by
    simpa [prefixWord, tailWord_5624274, baseEnd_5624274] using wordTrace_append hprefix tailTrace_5624274
  have hstable : (prefixWord ++ tailWord_5624274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624274).length < 2 ^ (prefixWord ++ tailWord_5624274).sum := by decide
  have hdescent : baseEnd_5624274 < baseStart_5624274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624300 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_5624300 : Nat := 118140960795 + 5624300 * 2 ^ 59
def prefixEnd_5624300 : Nat := 4983230072969 + 3 ^ 40 * 5624300 * 2
def baseEnd_5624300 : Nat := 962656415027483378028107

theorem tailTrace_5624300 : CollatzResearch.WordTrace tailWord_5624300 prefixEnd_5624300 962656415027483378028107 := by
  unfold tailWord_5624300
  simp only [CollatzResearch.WordTrace]
  refine ⟨102567536762064564405751177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136756715682752752541001569 102567536762064564405751177)
  ·
    refine ⟨76925652571548423304313383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102567536762064564405751177 76925652571548423304313383)
    ·
      refine ⟨115388478857322634956470075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76925652571548423304313383 115388478857322634956470075)
      ·
        refine ⟨173082718285983952434705113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115388478857322634956470075 173082718285983952434705113)
        ·
          refine ⟨129812038714487964326028835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173082718285983952434705113 129812038714487964326028835)
          ·
            refine ⟨194718058071731946489043253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129812038714487964326028835 194718058071731946489043253)
            ·
              refine ⟨18254817944224869983347805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194718058071731946489043253 18254817944224869983347805)
              ·
                refine ⟨6845556729084326243755427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18254817944224869983347805 6845556729084326243755427)
                ·
                  refine ⟨10268335093626489365633141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6845556729084326243755427 10268335093626489365633141)
                  ·
                    refine ⟨962656415027483378028107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10268335093626489365633141 962656415027483378028107)
                    ·
                      rfl

theorem cell23_5624300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_5624300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624300 prefixEnd_5624300 := by exact prefixLift 5624300
  have htrace : WordTrace (prefixWord ++ tailWord_5624300) baseStart_5624300 baseEnd_5624300 := by
    simpa [prefixWord, tailWord_5624300, baseEnd_5624300] using wordTrace_append hprefix tailTrace_5624300
  have hstable : (prefixWord ++ tailWord_5624300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624300).length < 2 ^ (prefixWord ++ tailWord_5624300).sum := by decide
  have hdescent : baseEnd_5624300 < baseStart_5624300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624313 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_5624313 : Nat := 118140960795 + 5624313 * 2 ^ 59
def prefixEnd_5624313 : Nat := 4983230072969 + 3 ^ 40 * 5624313 * 2
def baseEnd_5624313 : Nat := 962658640110319527740587

theorem tailTrace_5624313 : CollatzResearch.WordTrace tailWord_5624313 prefixEnd_5624313 962658640110319527740587 := by
  unfold tailWord_5624313
  simp only [CollatzResearch.WordTrace]
  refine ⟨205135547673082032031725593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136757031782054688021150395 205135547673082032031725593)
  ·
    refine ⟨153851660754811524023794195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205135547673082032031725593 153851660754811524023794195)
    ·
      refine ⟨230777491132217286035691293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153851660754811524023794195 230777491132217286035691293)
      ·
        refine ⟨86541559174581482263384235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230777491132217286035691293 86541559174581482263384235)
        ·
          refine ⟨129812338761872223395076353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86541559174581482263384235 129812338761872223395076353)
          ·
            refine ⟨97359254071404167546307265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129812338761872223395076353 97359254071404167546307265)
            ·
              refine ⟨73019440553553125659730449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97359254071404167546307265 73019440553553125659730449)
              ·
                refine ⟨54764580415164844244797837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73019440553553125659730449 54764580415164844244797837)
                ·
                  refine ⟨20536717655686816591799189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54764580415164844244797837 20536717655686816591799189)
                  ·
                    refine ⟨962658640110319527740587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20536717655686816591799189 962658640110319527740587)
                    ·
                      rfl

theorem cell23_5624313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_5624313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624313 prefixEnd_5624313 := by exact prefixLift 5624313
  have htrace : WordTrace (prefixWord ++ tailWord_5624313) baseStart_5624313 baseEnd_5624313 := by
    simpa [prefixWord, tailWord_5624313, baseEnd_5624313] using wordTrace_append hprefix tailTrace_5624313
  have hstable : (prefixWord ++ tailWord_5624313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624313).length < 2 ^ (prefixWord ++ tailWord_5624313).sum := by decide
  have hdescent : baseEnd_5624313 < baseStart_5624313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624337 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_5624337 : Nat := 118140960795 + 5624337 * 2 ^ 59
def prefixEnd_5624337 : Nat := 4983230072969 + 3 ^ 40 * 5624337 * 2
def baseEnd_5624337 : Nat := 2887988243866666489321651

theorem tailTrace_5624337 : CollatzResearch.WordTrace tailWord_5624337 prefixEnd_5624337 2887988243866666489321651 := by
  unfold tailWord_5624337
  simp only [CollatzResearch.WordTrace]
  refine ⟨205136423024995084130599265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136757615349996722753732843 205136423024995084130599265)
  ·
    refine ⟨153852317268746313097949449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205136423024995084130599265 153852317268746313097949449)
    ·
      refine ⟨115389237951559734823462087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153852317268746313097949449 115389237951559734823462087)
      ·
        refine ⟨173083856927339602235193131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115389237951559734823462087 173083856927339602235193131)
        ·
          refine ⟨259625785391009403352789697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173083856927339602235193131 259625785391009403352789697)
          ·
            refine ⟨194719339043257052514592273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259625785391009403352789697 194719339043257052514592273)
            ·
              refine ⟨146039504282442789385944205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194719339043257052514592273 146039504282442789385944205)
              ·
                refine ⟨54764814105916046019729077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146039504282442789385944205 54764814105916046019729077)
                ·
                  refine ⟨5134201322429629314349601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54764814105916046019729077 5134201322429629314349601)
                  ·
                    refine ⟨3850650991822221985762201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5134201322429629314349601 3850650991822221985762201)
                    ·
                      refine ⟨2887988243866666489321651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850650991822221985762201 2887988243866666489321651)
                      ·
                        rfl

theorem cell23_5624337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_5624337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624337 prefixEnd_5624337 := by exact prefixLift 5624337
  have htrace : WordTrace (prefixWord ++ tailWord_5624337) baseStart_5624337 baseEnd_5624337 := by
    simpa [prefixWord, tailWord_5624337, baseEnd_5624337] using wordTrace_append hprefix tailTrace_5624337
  have hstable : (prefixWord ++ tailWord_5624337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624337).length < 2 ^ (prefixWord ++ tailWord_5624337).sum := by decide
  have hdescent : baseEnd_5624337 < baseStart_5624337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624357 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_5624357 : Nat := 118140960795 + 5624357 * 2 ^ 59
def prefixEnd_5624357 : Nat := 4983230072969 + 3 ^ 40 * 5624357 * 2
def baseEnd_5624357 : Nat := 2887998513479756411071559

theorem tailTrace_5624357 : CollatzResearch.WordTrace tailWord_5624357 prefixEnd_5624357 2887998513479756411071559 := by
  unfold tailWord_5624357
  simp only [CollatzResearch.WordTrace]
  refine ⟨205137152484922627546327325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136758101656615085030884883 205137152484922627546327325)
  ·
    refine ⟨76926432181845985329872747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205137152484922627546327325 76926432181845985329872747)
    ·
      refine ⟨115389648272768977994809121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76926432181845985329872747 115389648272768977994809121)
      ·
        refine ⟨86542236204576733496106841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115389648272768977994809121 86542236204576733496106841)
        ·
          refine ⟨64906677153432550122080131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86542236204576733496106841 64906677153432550122080131)
          ·
            refine ⟨97360015730148825183120197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64906677153432550122080131 97360015730148825183120197)
            ·
              refine ⟨18255002949402904721835037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97360015730148825183120197 18255002949402904721835037)
              ·
                refine ⟨6845626106026089270688139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18255002949402904721835037 6845626106026089270688139)
                ·
                  refine ⟨10268439159039133906032209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6845626106026089270688139 10268439159039133906032209)
                  ·
                    refine ⟨7701329369279350429524157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10268439159039133906032209 7701329369279350429524157)
                    ·
                      refine ⟨2887998513479756411071559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701329369279350429524157 2887998513479756411071559)
                      ·
                        rfl

theorem cell23_5624357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_5624357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624357 prefixEnd_5624357 := by exact prefixLift 5624357
  have htrace : WordTrace (prefixWord ++ tailWord_5624357) baseStart_5624357 baseEnd_5624357 := by
    simpa [prefixWord, tailWord_5624357, baseEnd_5624357] using wordTrace_append hprefix tailTrace_5624357
  have hstable : (prefixWord ++ tailWord_5624357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624357).length < 2 ^ (prefixWord ++ tailWord_5624357).sum := by decide
  have hdescent : baseEnd_5624357 < baseStart_5624357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624360 : List Nat := [2, 1, 5, 2, 1, 1, 11]
def baseStart_5624360 : Nat := 118140960795 + 5624360 * 2 ^ 59
def prefixEnd_5624360 : Nat := 4983230072969 + 3 ^ 40 * 5624360 * 2
def baseEnd_5624360 : Nat := 35654321653354566658445

theorem tailTrace_5624360 : CollatzResearch.WordTrace tailWord_5624360 prefixEnd_5624360 35654321653354566658445 := by
  unfold tailWord_5624360
  simp only [CollatzResearch.WordTrace]
  refine ⟨102568630951955879529343267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136758174602607839372457689 102568630951955879529343267)
  ·
    refine ⟨153852946427933819294014901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102568630951955879529343267 153852946427933819294014901)
    ·
      refine ⟨14423713727618795558813897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153852946427933819294014901 14423713727618795558813897)
      ·
        refine ⟨10817785295714096669110423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14423713727618795558813897 10817785295714096669110423)
        ·
          refine ⟨16226677943571145003665635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10817785295714096669110423 16226677943571145003665635)
          ·
            refine ⟨24340016915356717505498453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16226677943571145003665635 24340016915356717505498453)
            ·
              refine ⟨35654321653354566658445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24340016915356717505498453 35654321653354566658445)
              ·
                rfl

theorem cell23_5624360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 11].length) (baseStart_5624360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624360 prefixEnd_5624360 := by exact prefixLift 5624360
  have htrace : WordTrace (prefixWord ++ tailWord_5624360) baseStart_5624360 baseEnd_5624360 := by
    simpa [prefixWord, tailWord_5624360, baseEnd_5624360] using wordTrace_append hprefix tailTrace_5624360
  have hstable : (prefixWord ++ tailWord_5624360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624360).length < 2 ^ (prefixWord ++ tailWord_5624360).sum := by decide
  have hdescent : baseEnd_5624360 < baseStart_5624360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624365 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5624365 : Nat := 118140960795 + 5624365 * 2 ^ 59
def prefixEnd_5624365 : Nat := 4983230072969 + 3 ^ 40 * 5624365 * 2
def baseEnd_5624365 : Nat := 2888002621324992379771523

theorem tailTrace_5624365 : CollatzResearch.WordTrace tailWord_5624365 prefixEnd_5624365 2888002621324992379771523 := by
  unfold tailWord_5624365
  simp only [CollatzResearch.WordTrace]
  refine ⟨205137444268893644912618549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136758296179262429941745699 205137444268893644912618549)
  ·
    refine ⟨19231635400208779210557989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205137444268893644912618549 19231635400208779210557989)
    ·
      refine ⟨3605931637539146101979623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19231635400208779210557989 3605931637539146101979623)
      ·
        refine ⟨5408897456308719152969435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3605931637539146101979623 5408897456308719152969435)
        ·
          refine ⟨8113346184463078729454153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5408897456308719152969435 8113346184463078729454153)
          ·
            refine ⟨6085009638347309047090615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8113346184463078729454153 6085009638347309047090615)
            ·
              refine ⟨9127514457520963570635923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085009638347309047090615 9127514457520963570635923)
              ·
                refine ⟨13691271686281445355953885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9127514457520963570635923 13691271686281445355953885)
                ·
                  refine ⟨5134226882355542008482707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13691271686281445355953885 5134226882355542008482707)
                  ·
                    refine ⟨7701340323533313012724061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134226882355542008482707 7701340323533313012724061)
                    ·
                      refine ⟨2888002621324992379771523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701340323533313012724061 2888002621324992379771523)
                      ·
                        rfl

theorem cell23_5624365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5624365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624365 prefixEnd_5624365 := by exact prefixLift 5624365
  have htrace : WordTrace (prefixWord ++ tailWord_5624365) baseStart_5624365 baseEnd_5624365 := by
    simpa [prefixWord, tailWord_5624365, baseEnd_5624365] using wordTrace_append hprefix tailTrace_5624365
  have hstable : (prefixWord ++ tailWord_5624365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624365).length < 2 ^ (prefixWord ++ tailWord_5624365).sum := by decide
  have hdescent : baseEnd_5624365 < baseStart_5624365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624381 : List Nat := [1, 4, 1, 3, 2, 3, 2, 1, 2, 4]
def baseStart_5624381 : Nat := 118140960795 + 5624381 * 2 ^ 59
def prefixEnd_5624381 : Nat := 4983230072969 + 3 ^ 40 * 5624381 * 2
def baseEnd_5624381 : Nat := 962670279005154772390483

theorem tailTrace_5624381 : CollatzResearch.WordTrace tailWord_5624381 prefixEnd_5624381 962670279005154772390483 := by
  unfold tailWord_5624381
  simp only [CollatzResearch.WordTrace]
  refine ⟨205138027836835679645200997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136758685224557119763467331 205138027836835679645200997)
  ·
    refine ⟨38463380219406689933475187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205138027836835679645200997 38463380219406689933475187)
    ·
      refine ⟨57695070329110034900212781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38463380219406689933475187 57695070329110034900212781)
      ·
        refine ⟨21635651373416263087579793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57695070329110034900212781 21635651373416263087579793)
        ·
          refine ⟨16226738530062197315684845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21635651373416263087579793 16226738530062197315684845)
          ·
            refine ⟨6085026948773323993381817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16226738530062197315684845 6085026948773323993381817)
            ·
              refine ⟨4563770211579992995036363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6085026948773323993381817 4563770211579992995036363)
              ·
                refine ⟨6845655317369989492554545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4563770211579992995036363 6845655317369989492554545)
                ·
                  refine ⟨5134241488027492119415909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6845655317369989492554545 5134241488027492119415909)
                  ·
                    refine ⟨962670279005154772390483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134241488027492119415909 962670279005154772390483)
                    ·
                      rfl

theorem cell23_5624381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 2, 1, 2, 4].length) (baseStart_5624381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624381 prefixEnd_5624381 := by exact prefixLift 5624381
  have htrace : WordTrace (prefixWord ++ tailWord_5624381) baseStart_5624381 baseEnd_5624381 := by
    simpa [prefixWord, tailWord_5624381, baseEnd_5624381] using wordTrace_append hprefix tailTrace_5624381
  have hstable : (prefixWord ++ tailWord_5624381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624381).length < 2 ^ (prefixWord ++ tailWord_5624381).sum := by decide
  have hdescent : baseEnd_5624381 < baseStart_5624381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624393 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_5624393 : Nat := 118140960795 + 5624393 * 2 ^ 59
def prefixEnd_5624393 : Nat := 4983230072969 + 3 ^ 40 * 5624393 * 2
def baseEnd_5624393 : Nat := 2888016998783318270221393

theorem tailTrace_5624393 : CollatzResearch.WordTrace tailWord_5624393 prefixEnd_5624393 2888016998783318270221393 := by
  unfold tailWord_5624393
  simp only [CollatzResearch.WordTrace]
  refine ⟨205138465512792205694637833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136758977008528137129758555 205138465512792205694637833)
  ·
    refine ⟨153853849134594154270978375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205138465512792205694637833 153853849134594154270978375)
    ·
      refine ⟨230780773701891231406467563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153853849134594154270978375 230780773701891231406467563)
      ·
        refine ⟨346171160552836847109701345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230780773701891231406467563 346171160552836847109701345)
        ·
          refine ⟨259628370414627635332276009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346171160552836847109701345 259628370414627635332276009)
          ·
            refine ⟨194721277810970726499207007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259628370414627635332276009 194721277810970726499207007)
            ·
              refine ⟨292081916716456089748810511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194721277810970726499207007 292081916716456089748810511)
              ·
                refine ⟨438122875074684134623215767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292081916716456089748810511 438122875074684134623215767)
                ·
                  refine ⟨657184312612026201934823651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438122875074684134623215767 657184312612026201934823651)
                  ·
                    refine ⟨985776468918039302902235477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 657184312612026201934823651 985776468918039302902235477)
                    ·
                      refine ⟨2888016998783318270221393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 985776468918039302902235477 2888016998783318270221393)
                      ·
                        rfl

theorem cell23_5624393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_5624393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624393 prefixEnd_5624393 := by exact prefixLift 5624393
  have htrace : WordTrace (prefixWord ++ tailWord_5624393) baseStart_5624393 baseEnd_5624393 := by
    simpa [prefixWord, tailWord_5624393, baseEnd_5624393] using wordTrace_append hprefix tailTrace_5624393
  have hstable : (prefixWord ++ tailWord_5624393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624393).length < 2 ^ (prefixWord ++ tailWord_5624393).sum := by decide
  have hdescent : baseEnd_5624393 < baseStart_5624393 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624420 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_5624420 : Nat := 118140960795 + 5624420 * 2 ^ 59
def prefixEnd_5624420 : Nat := 4983230072969 + 3 ^ 40 * 5624420 * 2
def baseEnd_5624420 : Nat := 962676954253663221527923

theorem tailTrace_5624420 : CollatzResearch.WordTrace tailWord_5624420 prefixEnd_5624420 962676954253663221527923 := by
  unfold tailWord_5624420
  simp only [CollatzResearch.WordTrace]
  refine ⟨102569725141847194652935357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136759633522462926203913809 102569725141847194652935357)
  ·
    refine ⟨38463646928192697994850759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102569725141847194652935357 38463646928192697994850759)
    ·
      refine ⟨57695470392289046992276139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38463646928192697994850759 57695470392289046992276139)
      ·
        refine ⟨86543205588433570488414209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57695470392289046992276139 86543205588433570488414209)
        ·
          refine ⟨64907404191325177866310657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86543205588433570488414209 64907404191325177866310657)
          ·
            refine ⟨48680553143493883399732993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64907404191325177866310657 48680553143493883399732993)
            ·
              refine ⟨36510414857620412549799745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48680553143493883399732993 36510414857620412549799745)
              ·
                refine ⟨27382811143215309412349809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36510414857620412549799745 27382811143215309412349809)
                ·
                  refine ⟨20537108357411482059262357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27382811143215309412349809 20537108357411482059262357)
                  ·
                    refine ⟨962676954253663221527923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20537108357411482059262357 962676954253663221527923)
                    ·
                      rfl

theorem cell23_5624420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_5624420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624420 prefixEnd_5624420 := by exact prefixLift 5624420
  have htrace : WordTrace (prefixWord ++ tailWord_5624420) baseStart_5624420 baseEnd_5624420 := by
    simpa [prefixWord, tailWord_5624420, baseEnd_5624420] using wordTrace_append hprefix tailTrace_5624420
  have hstable : (prefixWord ++ tailWord_5624420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624420).length < 2 ^ (prefixWord ++ tailWord_5624420).sum := by decide
  have hdescent : baseEnd_5624420 < baseStart_5624420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624421 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_5624421 : Nat := 118140960795 + 5624421 * 2 ^ 59
def prefixEnd_5624421 : Nat := 4983230072969 + 3 ^ 40 * 5624421 * 2
def baseEnd_5624421 : Nat := 2888031376241644160671265

theorem tailTrace_5624421 : CollatzResearch.WordTrace tailWord_5624421 prefixEnd_5624421 2888031376241644160671265 := by
  unfold tailWord_5624421
  simp only [CollatzResearch.WordTrace]
  refine ⟨205139486756690766476657117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136759657837793844317771411 205139486756690766476657117)
  ·
    refine ⟨76927307533759037428746419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205139486756690766476657117 76927307533759037428746419)
    ·
      refine ⟨115390961300638556143119629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76927307533759037428746419 115390961300638556143119629)
      ·
        refine ⟨43271610487739458553669861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115390961300638556143119629 43271610487739458553669861)
        ·
          refine ⟨8113426966451148478813099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43271610487739458553669861 8113426966451148478813099)
          ·
            refine ⟨12170140449676722718219649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113426966451148478813099 12170140449676722718219649)
            ·
              refine ⟨9127605337257542038664737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12170140449676722718219649 9127605337257542038664737)
              ·
                refine ⟨6845704002943156528998553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9127605337257542038664737 6845704002943156528998553)
                ·
                  refine ⟨5134278002207367396748915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6845704002943156528998553 5134278002207367396748915)
                  ·
                    refine ⟨7701417003311051095123373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134278002207367396748915 7701417003311051095123373)
                    ·
                      refine ⟨2888031376241644160671265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701417003311051095123373 2888031376241644160671265)
                      ·
                        rfl

theorem cell23_5624421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_5624421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624421 prefixEnd_5624421 := by exact prefixLift 5624421
  have htrace : WordTrace (prefixWord ++ tailWord_5624421) baseStart_5624421 baseEnd_5624421 := by
    simpa [prefixWord, tailWord_5624421, baseEnd_5624421] using wordTrace_append hprefix tailTrace_5624421
  have hstable : (prefixWord ++ tailWord_5624421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624421).length < 2 ^ (prefixWord ++ tailWord_5624421).sum := by decide
  have hdescent : baseEnd_5624421 < baseStart_5624421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624440 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_5624440 : Nat := 118140960795 + 5624440 * 2 ^ 59
def prefixEnd_5624440 : Nat := 4983230072969 + 3 ^ 40 * 5624440 * 2
def baseEnd_5624440 : Nat := 2888041132374079586333677

theorem tailTrace_5624440 : CollatzResearch.WordTrace tailWord_5624440 prefixEnd_5624440 2888041132374079586333677 := by
  unfold tailWord_5624440
  simp only [CollatzResearch.WordTrace]
  refine ⟨102570089871810966360799387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136760119829081288481065849 102570089871810966360799387)
  ·
    refine ⟨153855134807716449541199081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102570089871810966360799387 153855134807716449541199081)
    ·
      refine ⟨115391351105787337155899311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153855134807716449541199081 115391351105787337155899311)
      ·
        refine ⟨173087026658681005733848967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115391351105787337155899311 173087026658681005733848967)
        ·
          refine ⟨259630539988021508600773451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173087026658681005733848967 259630539988021508600773451)
          ·
            refine ⟨389445809982032262901160177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259630539988021508600773451 389445809982032262901160177)
            ·
              refine ⟨292084357486524197175870133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389445809982032262901160177 292084357486524197175870133)
              ·
                refine ⟨27382908514361643485237825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 292084357486524197175870133 27382908514361643485237825)
                ·
                  refine ⟨20537181385771232613928369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27382908514361643485237825 20537181385771232613928369)
                  ·
                    refine ⟨15402886039328424460446277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20537181385771232613928369 15402886039328424460446277)
                    ·
                      refine ⟨2888041132374079586333677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15402886039328424460446277 2888041132374079586333677)
                      ·
                        rfl

theorem cell23_5624440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_5624440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624440 prefixEnd_5624440 := by exact prefixLift 5624440
  have htrace : WordTrace (prefixWord ++ tailWord_5624440) baseStart_5624440 baseEnd_5624440 := by
    simpa [prefixWord, tailWord_5624440, baseEnd_5624440] using wordTrace_append hprefix tailTrace_5624440
  have hstable : (prefixWord ++ tailWord_5624440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624440).length < 2 ^ (prefixWord ++ tailWord_5624440).sum := by decide
  have hdescent : baseEnd_5624440 < baseStart_5624440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624477 : List Nat := [1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_5624477 : Nat := 118140960795 + 5624477 * 2 ^ 59
def prefixEnd_5624477 : Nat := 4983230072969 + 3 ^ 40 * 5624477 * 2
def baseEnd_5624477 : Nat := 2888060131158295941571007

theorem tailTrace_5624477 : CollatzResearch.WordTrace tailWord_5624477 prefixEnd_5624477 2888060131158295941571007 := by
  unfold tailWord_5624477
  simp only [CollatzResearch.WordTrace]
  refine ⟨205141529244487888040695685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136761019496325258693797123 205141529244487888040695685)
  ·
    refine ⟨38464036733341479007630441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205141529244487888040695685 38464036733341479007630441)
    ·
      refine ⟨28848027550006109255722831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38464036733341479007630441 28848027550006109255722831)
      ·
        refine ⟨43272041325009163883584247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28848027550006109255722831 43272041325009163883584247)
        ·
          refine ⟨64908061987513745825376371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43272041325009163883584247 64908061987513745825376371)
          ·
            refine ⟨97362092981270618738064557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64908061987513745825376371 97362092981270618738064557)
            ·
              refine ⟨36510784867976482026774209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97362092981270618738064557 36510784867976482026774209)
              ·
                refine ⟨27383088650982361520080657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36510784867976482026774209 27383088650982361520080657)
                ·
                  refine ⟨20537316488236771140060493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27383088650982361520080657 20537316488236771140060493)
                  ·
                    refine ⟨7701493683088789177522685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20537316488236771140060493 7701493683088789177522685)
                    ·
                      refine ⟨2888060131158295941571007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701493683088789177522685 2888060131158295941571007)
                      ·
                        rfl

theorem cell23_5624477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_5624477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624477 prefixEnd_5624477 := by exact prefixLift 5624477
  have htrace : WordTrace (prefixWord ++ tailWord_5624477) baseStart_5624477 baseEnd_5624477 := by
    simpa [prefixWord, tailWord_5624477, baseEnd_5624477] using wordTrace_append hprefix tailTrace_5624477
  have hstable : (prefixWord ++ tailWord_5624477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624477).length < 2 ^ (prefixWord ++ tailWord_5624477).sum := by decide
  have hdescent : baseEnd_5624477 < baseStart_5624477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624628 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_5624628 : Nat := 118140960795 + 5624628 * 2 ^ 59
def prefixEnd_5624628 : Nat := 4983230072969 + 3 ^ 40 * 5624628 * 2
def baseEnd_5624628 : Nat := 2888137666737124850782813

theorem tailTrace_5624628 : CollatzResearch.WordTrace tailWord_5624628 prefixEnd_5624628 2888137666737124850782813 := by
  unfold tailWord_5624628
  simp only [CollatzResearch.WordTrace]
  refine ⟨102573518333470420414721269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136764691111293893886295025 102573518333470420414721269)
  ·
    refine ⟨9616267343762851913880119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102573518333470420414721269 9616267343762851913880119)
    ·
      refine ⟨14424401015644277870820179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9616267343762851913880119 14424401015644277870820179)
      ·
        refine ⟨21636601523466416806230269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14424401015644277870820179 21636601523466416806230269)
        ·
          refine ⟨8113725571299906302336351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21636601523466416806230269 8113725571299906302336351)
          ·
            refine ⟨12170588356949859453504527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113725571299906302336351 12170588356949859453504527)
            ·
              refine ⟨18255882535424789180256791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12170588356949859453504527 18255882535424789180256791)
              ·
                refine ⟨27383823803137183770385187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18255882535424789180256791 27383823803137183770385187)
                ·
                  refine ⟨41075735704705775655577781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27383823803137183770385187 41075735704705775655577781)
                  ·
                    refine ⟨3850850222316166467710417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41075735704705775655577781 3850850222316166467710417)
                    ·
                      refine ⟨2888137666737124850782813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850850222316166467710417 2888137666737124850782813)
                      ·
                        rfl

theorem cell23_5624628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_5624628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624628 prefixEnd_5624628 := by exact prefixLift 5624628
  have htrace : WordTrace (prefixWord ++ tailWord_5624628) baseStart_5624628 baseEnd_5624628 := by
    simpa [prefixWord, tailWord_5624628, baseEnd_5624628] using wordTrace_append hprefix tailTrace_5624628
  have hstable : (prefixWord ++ tailWord_5624628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624628).length < 2 ^ (prefixWord ++ tailWord_5624628).sum := by decide
  have hdescent : baseEnd_5624628 < baseStart_5624628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624658 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_5624658 : Nat := 118140960795 + 5624658 * 2 ^ 59
def prefixEnd_5624658 : Nat := 4983230072969 + 3 ^ 40 * 5624658 * 2
def baseEnd_5624658 : Nat := 2888153071156759733407675

theorem tailTrace_5624658 : CollatzResearch.WordTrace tailWord_5624658 prefixEnd_5624658 2888153071156759733407675 := by
  unfold tailWord_5624658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51287032714208038988258657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136765420571221437302023085 51287032714208038988258657)
  ·
    refine ⟨38465274535656029241193993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51287032714208038988258657 38465274535656029241193993)
    ·
      refine ⟨28848955901742021930895495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38465274535656029241193993 28848955901742021930895495)
      ·
        refine ⟨43273433852613032896343243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28848955901742021930895495 43273433852613032896343243)
        ·
          refine ⟨64910150778919549344514865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43273433852613032896343243 64910150778919549344514865)
          ·
            refine ⟨48682613084189662008386149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64910150778919549344514865 48682613084189662008386149)
            ·
              refine ⟨9127989953285561626572403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48682613084189662008386149 9127989953285561626572403)
              ·
                refine ⟨13691984929928342439858605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9127989953285561626572403 13691984929928342439858605)
                ·
                  refine ⟨5134494348723128414946977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13691984929928342439858605 5134494348723128414946977)
                  ·
                    refine ⟨3850870761542346311210233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5134494348723128414946977 3850870761542346311210233)
                    ·
                      refine ⟨2888153071156759733407675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850870761542346311210233 2888153071156759733407675)
                      ·
                        rfl

theorem cell23_5624658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_5624658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624658 prefixEnd_5624658 := by exact prefixLift 5624658
  have htrace : WordTrace (prefixWord ++ tailWord_5624658) baseStart_5624658 baseEnd_5624658 := by
    simpa [prefixWord, tailWord_5624658, baseEnd_5624658] using wordTrace_append hprefix tailTrace_5624658
  have hstable : (prefixWord ++ tailWord_5624658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624658).length < 2 ^ (prefixWord ++ tailWord_5624658).sum := by decide
  have hdescent : baseEnd_5624658 < baseStart_5624658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624677 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 2, 7]
def baseStart_5624677 : Nat := 118140960795 + 5624677 * 2 ^ 59
def prefixEnd_5624677 : Nat := 4983230072969 + 3 ^ 40 * 5624677 * 2
def baseEnd_5624677 : Nat := 962720942429731719690029

theorem tailTrace_5624677 : CollatzResearch.WordTrace tailWord_5624677 prefixEnd_5624677 962720942429731719690029 := by
  unfold tailWord_5624677
  simp only [CollatzResearch.WordTrace]
  refine ⟨205148823843763322197976285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136765882562508881465317523 205148823843763322197976285)
  ·
    refine ⟨76930808941411245824241107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205148823843763322197976285 76930808941411245824241107)
    ·
      refine ⟨115396213412116868736361661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76930808941411245824241107 115396213412116868736361661)
      ·
        refine ⟨43273580029543825776135623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115396213412116868736361661 43273580029543825776135623)
        ·
          refine ⟨64910370044315738664203435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43273580029543825776135623 64910370044315738664203435)
          ·
            refine ⟨97365555066473607996305153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64910370044315738664203435 97365555066473607996305153)
            ·
              refine ⟨73024166299855205997228865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97365555066473607996305153 73024166299855205997228865)
              ·
                refine ⟨54768124724891404497921649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73024166299855205997228865 54768124724891404497921649)
                ·
                  refine ⟨41076093543668553373441237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54768124724891404497921649 41076093543668553373441237)
                  ·
                    refine ⟨962720942429731719690029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41076093543668553373441237 962720942429731719690029)
                    ·
                      rfl

theorem cell23_5624677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_5624677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624677 prefixEnd_5624677 := by exact prefixLift 5624677
  have htrace : WordTrace (prefixWord ++ tailWord_5624677) baseStart_5624677 baseEnd_5624677 := by
    simpa [prefixWord, tailWord_5624677, baseEnd_5624677] using wordTrace_append hprefix tailTrace_5624677
  have hstable : (prefixWord ++ tailWord_5624677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624677).length < 2 ^ (prefixWord ++ tailWord_5624677).sum := by decide
  have hdescent : baseEnd_5624677 < baseStart_5624677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624724 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5624724 : Nat := 118140960795 + 5624724 * 2 ^ 59
def prefixEnd_5624724 : Nat := 4983230072969 + 3 ^ 40 * 5624724 * 2
def baseEnd_5624724 : Nat := 962728986959985491727457

theorem tailTrace_5624724 : CollatzResearch.WordTrace tailWord_5624724 prefixEnd_5624724 962728986959985491727457 := by
  unfold tailWord_5624724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102575269037296524612468613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136767025383062032816624817 102575269037296524612468613)
  ·
    refine ⟨19232862944493098364837865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102575269037296524612468613 19232862944493098364837865)
    ·
      refine ⟨14424647208369823773628399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19232862944493098364837865 14424647208369823773628399)
      ·
        refine ⟨21636970812554735660442599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14424647208369823773628399 21636970812554735660442599)
        ·
          refine ⟨32455456218832103490663899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21636970812554735660442599 32455456218832103490663899)
          ·
            refine ⟨48683184328248155235995849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32455456218832103490663899 48683184328248155235995849)
            ·
              refine ⟨36512388246186116426996887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48683184328248155235995849 36512388246186116426996887)
              ·
                refine ⟨54768582369279174640495331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36512388246186116426996887 54768582369279174640495331)
                ·
                  refine ⟨82152873553918761960742997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54768582369279174640495331 82152873553918761960742997)
                  ·
                    refine ⟨962728986959985491727457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82152873553918761960742997 962728986959985491727457)
                    ·
                      rfl

theorem cell23_5624724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5624724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624724 prefixEnd_5624724 := by exact prefixLift 5624724
  have htrace : WordTrace (prefixWord ++ tailWord_5624724) baseStart_5624724 baseEnd_5624724 := by
    simpa [prefixWord, tailWord_5624724, baseEnd_5624724] using wordTrace_append hprefix tailTrace_5624724
  have hstable : (prefixWord ++ tailWord_5624724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624724).length < 2 ^ (prefixWord ++ tailWord_5624724).sum := by decide
  have hdescent : baseEnd_5624724 < baseStart_5624724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624725 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_5624725 : Nat := 118140960795 + 5624725 * 2 ^ 59
def prefixEnd_5624725 : Nat := 4983230072969 + 3 ^ 40 * 5624725 * 2
def baseEnd_5624725 : Nat := 2888187474360610971269867

theorem tailTrace_5624725 : CollatzResearch.WordTrace tailWord_5624725 prefixEnd_5624725 2888187474360610971269867 := by
  unfold tailWord_5624725
  simp only [CollatzResearch.WordTrace]
  refine ⟨205150574547589426395723629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136767049698392950930482419 205150574547589426395723629)
  ·
    refine ⟨76931465455346034898396361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205150574547589426395723629 76931465455346034898396361)
    ·
      refine ⟨57698599091509526173797271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76931465455346034898396361 57698599091509526173797271)
      ·
        refine ⟨86547898637264289260695907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57698599091509526173797271 86547898637264289260695907)
        ·
          refine ⟨129821847955896433891043861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86547898637264289260695907 129821847955896433891043861)
          ·
            refine ⟨6085399122932645338642681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129821847955896433891043861 6085399122932645338642681)
            ·
              refine ⟨4564049342199484003982011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6085399122932645338642681 4564049342199484003982011)
              ·
                refine ⟨6846074013299226005973017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4564049342199484003982011 6846074013299226005973017)
                ·
                  refine ⟨5134555509974419504479763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846074013299226005973017 5134555509974419504479763)
                  ·
                    refine ⟨7701833264961629256719645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134555509974419504479763 7701833264961629256719645)
                    ·
                      refine ⟨2888187474360610971269867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7701833264961629256719645 2888187474360610971269867)
                      ·
                        rfl

theorem cell23_5624725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_5624725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624725 prefixEnd_5624725 := by exact prefixLift 5624725
  have htrace : WordTrace (prefixWord ++ tailWord_5624725) baseStart_5624725 baseEnd_5624725 := by
    simpa [prefixWord, tailWord_5624725, baseEnd_5624725] using wordTrace_append hprefix tailTrace_5624725
  have hstable : (prefixWord ++ tailWord_5624725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624725).length < 2 ^ (prefixWord ++ tailWord_5624725).sum := by decide
  have hdescent : baseEnd_5624725 < baseStart_5624725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624735 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 1, 3, 2]
def baseStart_5624735 : Nat := 118140960795 + 5624735 * 2 ^ 59
def prefixEnd_5624735 : Nat := 4983230072969 + 3 ^ 40 * 5624735 * 2
def baseEnd_5624735 : Nat := 2888192609167155932144821

theorem tailTrace_5624735 : CollatzResearch.WordTrace tailWord_5624735 prefixEnd_5624735 2888192609167155932144821 := by
  unfold tailWord_5624735
  simp only [CollatzResearch.WordTrace]
  refine ⟨205150939277553198103587659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136767292851702132069058439 205150939277553198103587659)
  ·
    refine ⟨307726408916329797155381489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205150939277553198103587659 307726408916329797155381489)
    ·
      refine ⟨230794806687247347866536117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307726408916329797155381489 230794806687247347866536117)
      ·
        refine ⟨21637013126929438862487761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230794806687247347866536117 21637013126929438862487761)
        ·
          refine ⟨16227759845197079146865821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21637013126929438862487761 16227759845197079146865821)
          ·
            refine ⟨6085409941948904680074683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16227759845197079146865821 6085409941948904680074683)
            ·
              refine ⟨9128114912923357020112025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085409941948904680074683 9128114912923357020112025)
              ·
                refine ⟨6846086184692517765084019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9128114912923357020112025 6846086184692517765084019)
                ·
                  refine ⟨10269129277038776647626029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6846086184692517765084019 10269129277038776647626029)
                  ·
                    refine ⟨3850923478889541242859761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10269129277038776647626029 3850923478889541242859761)
                    ·
                      refine ⟨2888192609167155932144821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3850923478889541242859761 2888192609167155932144821)
                      ·
                        rfl

theorem cell23_5624735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_5624735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624735 prefixEnd_5624735 := by exact prefixLift 5624735
  have htrace : WordTrace (prefixWord ++ tailWord_5624735) baseStart_5624735 baseEnd_5624735 := by
    simpa [prefixWord, tailWord_5624735, baseEnd_5624735] using wordTrace_append hprefix tailTrace_5624735
  have hstable : (prefixWord ++ tailWord_5624735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624735).length < 2 ^ (prefixWord ++ tailWord_5624735).sum := by decide
  have hdescent : baseEnd_5624735 < baseStart_5624735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624805 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 5]
def baseStart_5624805 : Nat := 118140960795 + 5624805 * 2 ^ 59
def prefixEnd_5624805 : Nat := 4983230072969 + 3 ^ 40 * 5624805 * 2
def baseEnd_5624805 : Nat := 320914283645885628696611

theorem tailTrace_5624805 : CollatzResearch.WordTrace tailWord_5624805 prefixEnd_5624805 320914283645885628696611 := by
  unfold tailWord_5624805
  simp only [CollatzResearch.WordTrace]
  refine ⟨205153492387299600058635869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136768994924866400039090579 205153492387299600058635869)
  ·
    refine ⟨76932559645237350021988451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205153492387299600058635869 76932559645237350021988451)
    ·
      refine ⟨115398839467856025032982677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76932559645237350021988451 115398839467856025032982677)
      ·
        refine ⟨5409320600055751173421063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115398839467856025032982677 5409320600055751173421063)
        ·
          refine ⟨8113980900083626760131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5409320600055751173421063 8113980900083626760131595)
          ·
            refine ⟨12170971350125440140197393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8113980900083626760131595 12170971350125440140197393)
            ·
              refine ⟨9128228512594080105148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12170971350125440140197393 9128228512594080105148045)
              ·
                refine ⟨3423085692222780039430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9128228512594080105148045 3423085692222780039430517)
                ·
                  refine ⟨320914283645885628696611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423085692222780039430517 320914283645885628696611)
                  ·
                    rfl

theorem cell23_5624805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 5].length) (baseStart_5624805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624805 prefixEnd_5624805 := by exact prefixLift 5624805
  have htrace : WordTrace (prefixWord ++ tailWord_5624805) baseStart_5624805 baseEnd_5624805 := by
    simpa [prefixWord, tailWord_5624805, baseEnd_5624805] using wordTrace_append hprefix tailTrace_5624805
  have hstable : (prefixWord ++ tailWord_5624805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624805).length < 2 ^ (prefixWord ++ tailWord_5624805).sum := by decide
  have hdescent : baseEnd_5624805 < baseStart_5624805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624865 : List Nat := [1, 2, 3, 2, 3, 1, 3, 3, 1, 4]
def baseStart_5624865 : Nat := 118140960795 + 5624865 * 2 ^ 59
def prefixEnd_5624865 : Nat := 4983230072969 + 3 ^ 40 * 5624865 * 2
def baseEnd_5624865 : Nat := 962753120550746807839741

theorem tailTrace_5624865 : CollatzResearch.WordTrace tailWord_5624865 prefixEnd_5624865 962753120550746807839741 := by
  unfold tailWord_5624865
  simp only [CollatzResearch.WordTrace]
  refine ⟨205155680767082230305820049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136770453844721486870546699 205155680767082230305820049)
  ·
    refine ⟨153866760575311672729365037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205155680767082230305820049 153866760575311672729365037)
    ·
      refine ⟨57700035215741877273511889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153866760575311672729365037 57700035215741877273511889)
      ·
        refine ⟨43275026411806407955133917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57700035215741877273511889 43275026411806407955133917)
        ·
          refine ⟨16228134904427402983175219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43275026411806407955133917 16228134904427402983175219)
          ·
            refine ⟨24342202356641104474762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228134904427402983175219 24342202356641104474762829)
            ·
              refine ⟨9128325883740414178036061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24342202356641104474762829 9128325883740414178036061)
              ·
                refine ⟨3423122206402655316763523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9128325883740414178036061 3423122206402655316763523)
                ·
                  refine ⟨5134683309603982975145285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423122206402655316763523 5134683309603982975145285)
                  ·
                    refine ⟨962753120550746807839741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134683309603982975145285 962753120550746807839741)
                    ·
                      rfl

theorem cell23_5624865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 3, 1, 4].length) (baseStart_5624865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624865 prefixEnd_5624865 := by exact prefixLift 5624865
  have htrace : WordTrace (prefixWord ++ tailWord_5624865) baseStart_5624865 baseEnd_5624865 := by
    simpa [prefixWord, tailWord_5624865, baseEnd_5624865] using wordTrace_append hprefix tailTrace_5624865
  have hstable : (prefixWord ++ tailWord_5624865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624865).length < 2 ^ (prefixWord ++ tailWord_5624865).sum := by decide
  have hdescent : baseEnd_5624865 < baseStart_5624865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5624921 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_5624921 : Nat := 118140960795 + 5624921 * 2 ^ 59
def prefixEnd_5624921 : Nat := 4983230072969 + 3 ^ 40 * 5624921 * 2
def baseEnd_5624921 : Nat := 962762705522964068139655

theorem tailTrace_5624921 : CollatzResearch.WordTrace tailWord_5624921 prefixEnd_5624921 962762705522964068139655 := by
  unfold tailWord_5624921
  simp only [CollatzResearch.WordTrace]
  refine ⟨205157723254879351869858617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136771815503252901246572411 205157723254879351869858617)
  ·
    refine ⟨153868292441159513902393963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205157723254879351869858617 153868292441159513902393963)
    ·
      refine ⟨230802438661739270853590945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153868292441159513902393963 230802438661739270853590945)
      ·
        refine ⟨173101828996304453140193209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230802438661739270853590945 173101828996304453140193209)
        ·
          refine ⟨129826371747228339855144907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173101828996304453140193209 129826371747228339855144907)
          ·
            refine ⟨194739557620842509782717361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129826371747228339855144907 194739557620842509782717361)
            ·
              refine ⟨146054668215631882337038021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194739557620842509782717361 146054668215631882337038021)
              ·
                refine ⟨27385250290430977938194629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146054668215631882337038021 27385250290430977938194629)
                ·
                  refine ⟨5134734429455808363411493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27385250290430977938194629 5134734429455808363411493)
                  ·
                    refine ⟨962762705522964068139655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134734429455808363411493 962762705522964068139655)
                    ·
                      rfl

theorem cell23_5624921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_5624921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5624921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5624921 prefixEnd_5624921 := by exact prefixLift 5624921
  have htrace : WordTrace (prefixWord ++ tailWord_5624921) baseStart_5624921 baseEnd_5624921 := by
    simpa [prefixWord, tailWord_5624921, baseEnd_5624921] using wordTrace_append hprefix tailTrace_5624921
  have hstable : (prefixWord ++ tailWord_5624921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5624921).length < 2 ^ (prefixWord ++ tailWord_5624921).sum := by decide
  have hdescent : baseEnd_5624921 < baseStart_5624921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5624921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625011 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 2, 6]
def baseStart_5625011 : Nat := 118140960795 + 5625011 * 2 ^ 59
def prefixEnd_5625011 : Nat := 4983230072969 + 3 ^ 40 * 5625011 * 2
def baseEnd_5625011 : Nat := 962778109942598950764517

theorem tailTrace_5625011 : CollatzResearch.WordTrace tailWord_5625011 prefixEnd_5625011 962778109942598950764517 := by
  unfold tailWord_5625011
  simp only [CollatzResearch.WordTrace]
  refine ⟨205161005824553297240634887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136774003883035531493756591 205161005824553297240634887)
  ·
    refine ⟨307741508736829945860952331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205161005824553297240634887 307741508736829945860952331)
    ·
      refine ⟨461612263105244918791428497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307741508736829945860952331 461612263105244918791428497)
      ·
        refine ⟨346209197328933689093571373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461612263105244918791428497 346209197328933689093571373)
        ·
          refine ⟨129828448998350133410089265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346209197328933689093571373 129828448998350133410089265)
          ·
            refine ⟨97371336748762600057566949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129828448998350133410089265 97371336748762600057566949)
            ·
              refine ⟨18257125640392987510793803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97371336748762600057566949 18257125640392987510793803)
              ·
                refine ⟨27385688460589481266190705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18257125640392987510793803 27385688460589481266190705)
                ·
                  refine ⟨20539266345442110949643029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27385688460589481266190705 20539266345442110949643029)
                  ·
                    refine ⟨962778109942598950764517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20539266345442110949643029 962778109942598950764517)
                    ·
                      rfl

theorem cell23_5625011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 2, 6].length) (baseStart_5625011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625011 prefixEnd_5625011 := by exact prefixLift 5625011
  have htrace : WordTrace (prefixWord ++ tailWord_5625011) baseStart_5625011 baseEnd_5625011 := by
    simpa [prefixWord, tailWord_5625011, baseEnd_5625011] using wordTrace_append hprefix tailTrace_5625011
  have hstable : (prefixWord ++ tailWord_5625011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625011).length < 2 ^ (prefixWord ++ tailWord_5625011).sum := by decide
  have hdescent : baseEnd_5625011 < baseStart_5625011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625022 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2]
def baseStart_5625022 : Nat := 118140960795 + 5625022 * 2 ^ 59
def prefixEnd_5625022 : Nat := 4983230072969 + 3 ^ 40 * 5625022 * 2
def baseEnd_5625022 : Nat := 2888339978114996309256001

theorem tailTrace_5625022 : CollatzResearch.WordTrace tailWord_5625022 prefixEnd_5625022 2888339978114996309256001 := by
  unfold tailWord_5625022
  simp only [CollatzResearch.WordTrace]
  refine ⟨25645175878439180764910665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136774271351675630746190213 25645175878439180764910665)
  ·
    refine ⟨19233881908829385573682999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25645175878439180764910665 19233881908829385573682999)
    ·
      refine ⟨28850822863244078360524499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19233881908829385573682999 28850822863244078360524499)
      ·
        refine ⟨43276234294866117540786749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28850822863244078360524499 43276234294866117540786749)
        ·
          refine ⟨16228587860574794077795031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43276234294866117540786749 16228587860574794077795031)
          ·
            refine ⟨24342881790862191116692547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228587860574794077795031 24342881790862191116692547)
            ·
              refine ⟨36514322686293286675038821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24342881790862191116692547 36514322686293286675038821)
              ·
                refine ⟨6846435503679991251569779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36514322686293286675038821 6846435503679991251569779)
                ·
                  refine ⟨10269653255519986877354669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6846435503679991251569779 10269653255519986877354669)
                  ·
                    refine ⟨3851119970819995079008001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10269653255519986877354669 3851119970819995079008001)
                    ·
                      refine ⟨2888339978114996309256001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851119970819995079008001 2888339978114996309256001)
                      ·
                        rfl

theorem cell23_5625022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_5625022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625022 prefixEnd_5625022 := by exact prefixLift 5625022
  have htrace : WordTrace (prefixWord ++ tailWord_5625022) baseStart_5625022 baseEnd_5625022 := by
    simpa [prefixWord, tailWord_5625022, baseEnd_5625022] using wordTrace_append hprefix tailTrace_5625022
  have hstable : (prefixWord ++ tailWord_5625022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625022).length < 2 ^ (prefixWord ++ tailWord_5625022).sum := by decide
  have hdescent : baseEnd_5625022 < baseStart_5625022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625031 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4]
def baseStart_5625031 : Nat := 118140960795 + 5625031 * 2 ^ 59
def prefixEnd_5625031 : Nat := 4983230072969 + 3 ^ 40 * 5625031 * 2
def baseEnd_5625031 : Nat := 2888344599440886774043459

theorem tailTrace_5625031 : CollatzResearch.WordTrace tailWord_5625031 prefixEnd_5625031 2888344599440886774043459 := by
  unfold tailWord_5625031
  simp only [CollatzResearch.WordTrace]
  refine ⟨205161735284480840656362947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136774490189653893770908631 205161735284480840656362947)
  ·
    refine ⟨307742602926721260984544421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205161735284480840656362947 307742602926721260984544421)
    ·
      refine ⟨57701738048760236434602079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307742602926721260984544421 57701738048760236434602079)
      ·
        refine ⟨86552607073140354651903119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57701738048760236434602079 86552607073140354651903119)
        ·
          refine ⟨129828910609710531977854679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86552607073140354651903119 129828910609710531977854679)
          ·
            refine ⟨194743365914565797966782019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129828910609710531977854679 194743365914565797966782019)
            ·
              refine ⟨292115048871848696950173029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194743365914565797966782019 292115048871848696950173029)
              ·
                refine ⟨54771571663471630678157443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 292115048871848696950173029 54771571663471630678157443)
                ·
                  refine ⟨82157357495207446017236165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54771571663471630678157443 82157357495207446017236165)
                  ·
                    refine ⟨15404504530351396128231781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82157357495207446017236165 15404504530351396128231781)
                    ·
                      refine ⟨2888344599440886774043459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15404504530351396128231781 2888344599440886774043459)
                      ·
                        rfl

theorem cell23_5625031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_5625031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625031 prefixEnd_5625031 := by exact prefixLift 5625031
  have htrace : WordTrace (prefixWord ++ tailWord_5625031) baseStart_5625031 baseEnd_5625031 := by
    simpa [prefixWord, tailWord_5625031, baseEnd_5625031] using wordTrace_append hprefix tailTrace_5625031
  have hstable : (prefixWord ++ tailWord_5625031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625031).length < 2 ^ (prefixWord ++ tailWord_5625031).sum := by decide
  have hdescent : baseEnd_5625031 < baseStart_5625031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625069 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 2, 2, 2]
def baseStart_5625069 : Nat := 118140960795 + 5625069 * 2 ^ 59
def prefixEnd_5625069 : Nat := 4983230072969 + 3 ^ 40 * 5625069 * 2
def baseEnd_5625069 : Nat := 2888364111705757625368285

theorem tailTrace_5625069 : CollatzResearch.WordTrace tailWord_5625069 prefixEnd_5625069 2888364111705757625368285 := by
  unfold tailWord_5625069
  simp only [CollatzResearch.WordTrace]
  refine ⟨205163121258343173146246261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136775414172228782097497507 205163121258343173146246261)
  ·
    refine ⟨19234042617969672482460587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205163121258343173146246261 19234042617969672482460587)
    ·
      refine ⟨28851063926954508723690881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19234042617969672482460587 28851063926954508723690881)
      ·
        refine ⟨21638297945215881542768161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28851063926954508723690881 21638297945215881542768161)
        ·
          refine ⟨16228723458911911157076121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21638297945215881542768161 16228723458911911157076121)
          ·
            refine ⟨12171542594183933367807091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16228723458911911157076121 12171542594183933367807091)
            ·
              refine ⟨18257313891275900051710637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12171542594183933367807091 18257313891275900051710637)
              ·
                refine ⟨6846492709228462519391489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18257313891275900051710637 6846492709228462519391489)
                ·
                  refine ⟨5134869531921346889543617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846492709228462519391489 5134869531921346889543617)
                  ·
                    refine ⟨3851152148941010167157713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5134869531921346889543617 3851152148941010167157713)
                    ·
                      refine ⟨2888364111705757625368285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851152148941010167157713 2888364111705757625368285)
                      ·
                        rfl

theorem cell23_5625069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_5625069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625069 prefixEnd_5625069 := by exact prefixLift 5625069
  have htrace : WordTrace (prefixWord ++ tailWord_5625069) baseStart_5625069 baseEnd_5625069 := by
    simpa [prefixWord, tailWord_5625069, baseEnd_5625069] using wordTrace_append hprefix tailTrace_5625069
  have hstable : (prefixWord ++ tailWord_5625069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625069).length < 2 ^ (prefixWord ++ tailWord_5625069).sum := by decide
  have hdescent : baseEnd_5625069 < baseStart_5625069 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625081 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_5625081 : Nat := 118140960795 + 5625081 * 2 ^ 59
def prefixEnd_5625081 : Nat := 4983230072969 + 3 ^ 40 * 5625081 * 2
def baseEnd_5625081 : Nat := 2888370273473611578418229

theorem tailTrace_5625081 : CollatzResearch.WordTrace tailWord_5625081 prefixEnd_5625081 2888370273473611578418229 := by
  unfold tailWord_5625081
  simp only [CollatzResearch.WordTrace]
  refine ⟨205163558934299699195683097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136775705956199799463788731 205163558934299699195683097)
  ·
    refine ⟨153872669200724774396762323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205163558934299699195683097 153872669200724774396762323)
    ·
      refine ⟨230809003801087161595143485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153872669200724774396762323 230809003801087161595143485)
      ·
        refine ⟨86553376425407685598178807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230809003801087161595143485 86553376425407685598178807)
        ·
          refine ⟨129830064638111528397268211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86553376425407685598178807 129830064638111528397268211)
          ·
            refine ⟨194745096957167292595902317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129830064638111528397268211 194745096957167292595902317)
            ·
              refine ⟨73029411358937734723463369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194745096957167292595902317 73029411358937734723463369)
              ·
                refine ⟨54772058519203301042597527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73029411358937734723463369 54772058519203301042597527)
                ·
                  refine ⟨82158087778804951563896291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54772058519203301042597527 82158087778804951563896291)
                  ·
                    refine ⟨123237131668207427345844437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82158087778804951563896291 123237131668207427345844437)
                    ·
                      refine ⟨2888370273473611578418229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123237131668207427345844437 2888370273473611578418229)
                      ·
                        rfl

theorem cell23_5625081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_5625081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625081 prefixEnd_5625081 := by exact prefixLift 5625081
  have htrace : WordTrace (prefixWord ++ tailWord_5625081) baseStart_5625081 baseEnd_5625081 := by
    simpa [prefixWord, tailWord_5625081, baseEnd_5625081] using wordTrace_append hprefix tailTrace_5625081
  have hstable : (prefixWord ++ tailWord_5625081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625081).length < 2 ^ (prefixWord ++ tailWord_5625081).sum := by decide
  have hdescent : baseEnd_5625081 < baseStart_5625081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625125 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_5625125 : Nat := 118140960795 + 5625125 * 2 ^ 59
def prefixEnd_5625125 : Nat := 4983230072969 + 3 ^ 40 * 5625125 * 2
def baseEnd_5625125 : Nat := 2888392866622409406268027

theorem tailTrace_5625125 : CollatzResearch.WordTrace tailWord_5625125 prefixEnd_5625125 2888392866622409406268027 := by
  unfold tailWord_5625125
  simp only [CollatzResearch.WordTrace]
  refine ⟨205165163746140294710284829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136776775830760196473523219 205165163746140294710284829)
  ·
    refine ⟨76936936404802610516356811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205165163746140294710284829 76936936404802610516356811)
    ·
      refine ⟨115405404607203915774535217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76936936404802610516356811 115405404607203915774535217)
      ·
        refine ⟨86554053455402936830901413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115405404607203915774535217 86554053455402936830901413)
        ·
          refine ⟨16228885022888050655794015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86554053455402936830901413 16228885022888050655794015)
          ·
            refine ⟨24343327534332075983691023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16228885022888050655794015 24343327534332075983691023)
            ·
              refine ⟨36514991301498113975536535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24343327534332075983691023 36514991301498113975536535)
              ·
                refine ⟨54772486952247170963304803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36514991301498113975536535 54772486952247170963304803)
                ·
                  refine ⟨82158730428370756444957205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54772486952247170963304803 82158730428370756444957205)
                  ·
                    refine ⟨3851190488829879208357369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82158730428370756444957205 3851190488829879208357369)
                    ·
                      refine ⟨2888392866622409406268027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851190488829879208357369 2888392866622409406268027)
                      ·
                        rfl

theorem cell23_5625125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_5625125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625125 prefixEnd_5625125 := by exact prefixLift 5625125
  have htrace : WordTrace (prefixWord ++ tailWord_5625125) baseStart_5625125 baseEnd_5625125 := by
    simpa [prefixWord, tailWord_5625125, baseEnd_5625125] using wordTrace_append hprefix tailTrace_5625125
  have hstable : (prefixWord ++ tailWord_5625125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625125).length < 2 ^ (prefixWord ++ tailWord_5625125).sum := by decide
  have hdescent : baseEnd_5625125 < baseStart_5625125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625152 : List Nat := [2, 1, 1, 2, 2, 1, 6, 3, 1, 4]
def baseStart_5625152 : Nat := 118140960795 + 5625152 * 2 ^ 59
def prefixEnd_5625152 : Nat := 4983230072969 + 3 ^ 40 * 5625152 * 2
def baseEnd_5625152 : Nat := 962802243533360266876801

theorem tailTrace_5625152 : CollatzResearch.WordTrace tailWord_5625152 prefixEnd_5625152 962802243533360266876801 := by
  unfold tailWord_5625152
  simp only [CollatzResearch.WordTrace]
  refine ⟨102583074258521239160758855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136777432344694985547678473 102583074258521239160758855)
  ·
    refine ⟨153874611387781858741138283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102583074258521239160758855 153874611387781858741138283)
    ·
      refine ⟨230811917081672788111707425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153874611387781858741138283 230811917081672788111707425)
      ·
        refine ⟨173108937811254591083780569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230811917081672788111707425 173108937811254591083780569)
        ·
          refine ⟨129831703358440943312835427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173108937811254591083780569 129831703358440943312835427)
          ·
            refine ⟨194747555037661414969253141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129831703358440943312835427 194747555037661414969253141)
            ·
              refine ⟨9128791642390378826683741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194747555037661414969253141 9128791642390378826683741)
              ·
                refine ⟨3423296865896392060006403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9128791642390378826683741 3423296865896392060006403)
                ·
                  refine ⟨5134945298844588090009605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423296865896392060006403 5134945298844588090009605)
                  ·
                    refine ⟨962802243533360266876801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5134945298844588090009605 962802243533360266876801)
                    ·
                      rfl

theorem cell23_5625152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_5625152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625152 prefixEnd_5625152 := by exact prefixLift 5625152
  have htrace : WordTrace (prefixWord ++ tailWord_5625152) baseStart_5625152 baseEnd_5625152 := by
    simpa [prefixWord, tailWord_5625152, baseEnd_5625152] using wordTrace_append hprefix tailTrace_5625152
  have hstable : (prefixWord ++ tailWord_5625152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625152).length < 2 ^ (prefixWord ++ tailWord_5625152).sum := by decide
  have hdescent : baseEnd_5625152 < baseStart_5625152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625178 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_5625178 : Nat := 118140960795 + 5625178 * 2 ^ 59
def prefixEnd_5625178 : Nat := 4983230072969 + 3 ^ 40 * 5625178 * 2
def baseEnd_5625178 : Nat := 962806693699032566301761

theorem tailTrace_5625178 : CollatzResearch.WordTrace tailWord_5625178 prefixEnd_5625178 962806693699032566301761 := by
  unfold tailWord_5625178
  simp only [CollatzResearch.WordTrace]
  refine ⟨51291774203737071190491047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136778064543298856507976125 51291774203737071190491047)
  ·
    refine ⟨76937661305605606785736571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51291774203737071190491047 76937661305605606785736571)
    ·
      refine ⟨115406491958408410178604857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76937661305605606785736571 115406491958408410178604857)
      ·
        refine ⟨86554868968806307633953643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115406491958408410178604857 86554868968806307633953643)
        ·
          refine ⟨129832303453209461450930465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86554868968806307633953643 129832303453209461450930465)
          ·
            refine ⟨97374227589907096088197849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129832303453209461450930465 97374227589907096088197849)
            ·
              refine ⟨73030670692430322066148387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97374227589907096088197849 73030670692430322066148387)
              ·
                refine ⟨109546006038645483099222581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73030670692430322066148387 109546006038645483099222581)
                ·
                  refine ⟨10269938066123014040552117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109546006038645483099222581 10269938066123014040552117)
                  ·
                    refine ⟨962806693699032566301761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10269938066123014040552117 962806693699032566301761)
                    ·
                      rfl

theorem cell23_5625178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_5625178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625178 prefixEnd_5625178 := by exact prefixLift 5625178
  have htrace : WordTrace (prefixWord ++ tailWord_5625178) baseStart_5625178 baseEnd_5625178 := by
    simpa [prefixWord, tailWord_5625178, baseEnd_5625178] using wordTrace_append hprefix tailTrace_5625178
  have hstable : (prefixWord ++ tailWord_5625178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625178).length < 2 ^ (prefixWord ++ tailWord_5625178).sum := by decide
  have hdescent : baseEnd_5625178 < baseStart_5625178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625202 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_5625202 : Nat := 118140960795 + 5625202 * 2 ^ 59
def prefixEnd_5625202 : Nat := 4983230072969 + 3 ^ 40 * 5625202 * 2
def baseEnd_5625202 : Nat := 2888432404632805605005173

theorem tailTrace_5625202 : CollatzResearch.WordTrace tailWord_5625202 prefixEnd_5625202 2888432404632805605005173 := by
  unfold tailWord_5625202
  simp only [CollatzResearch.WordTrace]
  refine ⟨51291993041715334215209465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136778648111240891240558573 51291993041715334215209465)
  ·
    refine ⟨38468994781286500661407099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51291993041715334215209465 38468994781286500661407099)
    ·
      refine ⟨57703492171929750992110649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38468994781286500661407099 57703492171929750992110649)
      ·
        refine ⟨43277619128947313244082987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57703492171929750992110649 43277619128947313244082987)
        ·
          refine ⟨64916428693420969866124481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43277619128947313244082987 64916428693420969866124481)
          ·
            refine ⟨48687321520065727399593361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64916428693420969866124481 48687321520065727399593361)
            ·
              refine ⟨36515491140049295549695021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48687321520065727399593361 36515491140049295549695021)
              ·
                refine ⟨13693309177518485831135633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36515491140049295549695021 13693309177518485831135633)
                ·
                  refine ⟨10269981883138864373351725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13693309177518485831135633 10269981883138864373351725)
                  ·
                    refine ⟨3851243206177074140006897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10269981883138864373351725 3851243206177074140006897)
                    ·
                      refine ⟨2888432404632805605005173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851243206177074140006897 2888432404632805605005173)
                      ·
                        rfl

theorem cell23_5625202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_5625202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625202 prefixEnd_5625202 := by exact prefixLift 5625202
  have htrace : WordTrace (prefixWord ++ tailWord_5625202) baseStart_5625202 baseEnd_5625202 := by
    simpa [prefixWord, tailWord_5625202, baseEnd_5625202] using wordTrace_append hprefix tailTrace_5625202
  have hstable : (prefixWord ++ tailWord_5625202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625202).length < 2 ^ (prefixWord ++ tailWord_5625202).sum := by decide
  have hdescent : baseEnd_5625202 < baseStart_5625202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625209 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 1, 1, 3]
def baseStart_5625209 : Nat := 118140960795 + 5625209 * 2 ^ 59
def prefixEnd_5625209 : Nat := 4983230072969 + 3 ^ 40 * 5625209 * 2
def baseEnd_5625209 : Nat := 2888435998997387077617641

theorem tailTrace_5625209 : CollatzResearch.WordTrace tailWord_5625209 prefixEnd_5625209 2888435998997387077617641 := by
  unfold tailWord_5625209
  simp only [CollatzResearch.WordTrace]
  refine ⟨205168227477835977056342681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136778818318557318037561787 205168227477835977056342681)
  ·
    refine ⟨153876170608376982792257011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205168227477835977056342681 153876170608376982792257011)
    ·
      refine ⟨230814255912565474188385517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153876170608376982792257011 230814255912565474188385517)
      ·
        refine ⟨86555345967212052820644569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230814255912565474188385517 86555345967212052820644569)
        ·
          refine ⟨64916509475409039615483427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86555345967212052820644569 64916509475409039615483427)
          ·
            refine ⟨97374764213113559423225141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64916509475409039615483427 97374764213113559423225141)
            ·
              refine ⟨9128884144979396195927357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97374764213113559423225141 9128884144979396195927357)
              ·
                refine ⟨3423331554367273573472759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9128884144979396195927357 3423331554367273573472759)
                ·
                  refine ⟨5134997331550910360209139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423331554367273573472759 5134997331550910360209139)
                  ·
                    refine ⟨7702495997326365540313709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5134997331550910360209139 7702495997326365540313709)
                    ·
                      refine ⟨2888435998997387077617641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7702495997326365540313709 2888435998997387077617641)
                      ·
                        rfl

theorem cell23_5625209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_5625209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625209 prefixEnd_5625209 := by exact prefixLift 5625209
  have htrace : WordTrace (prefixWord ++ tailWord_5625209) baseStart_5625209 baseEnd_5625209 := by
    simpa [prefixWord, tailWord_5625209, baseEnd_5625209] using wordTrace_append hprefix tailTrace_5625209
  have hstable : (prefixWord ++ tailWord_5625209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625209).length < 2 ^ (prefixWord ++ tailWord_5625209).sum := by decide
  have hdescent : baseEnd_5625209 < baseStart_5625209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625228 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_5625228 : Nat := 118140960795 + 5625228 * 2 ^ 59
def prefixEnd_5625228 : Nat := 4983230072969 + 3 ^ 40 * 5625228 * 2
def baseEnd_5625228 : Nat := 2888445755129822503280053

theorem tailTrace_5625228 : CollatzResearch.WordTrace tailWord_5625228 prefixEnd_5625228 2888445755129822503280053 := by
  unfold tailWord_5625228
  simp only [CollatzResearch.WordTrace]
  refine ⟨102584460232383571650642169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136779280309844762200856225 102584460232383571650642169)
  ·
    refine ⟨76938345174287678737981627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102584460232383571650642169 76938345174287678737981627)
    ·
      refine ⟨115407517761431518106972441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76938345174287678737981627 115407517761431518106972441)
      ·
        refine ⟨86555638321073638580229331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115407517761431518106972441 86555638321073638580229331)
        ·
          refine ⟨129833457481610457870343997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86555638321073638580229331 129833457481610457870343997)
          ·
            refine ⟨48687546555603921701378999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129833457481610457870343997 48687546555603921701378999)
            ·
              refine ⟨73031319833405882552068499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48687546555603921701378999 73031319833405882552068499)
              ·
                refine ⟨109546979750108823828102749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73031319833405882552068499 109546979750108823828102749)
                ·
                  refine ⟨41080117406290808935538531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109546979750108823828102749 41080117406290808935538531)
                  ·
                    refine ⟨61620176109436213403307797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41080117406290808935538531 61620176109436213403307797)
                    ·
                      refine ⟨2888445755129822503280053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61620176109436213403307797 2888445755129822503280053)
                      ·
                        rfl

theorem cell23_5625228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_5625228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625228 prefixEnd_5625228 := by exact prefixLift 5625228
  have htrace : WordTrace (prefixWord ++ tailWord_5625228) baseStart_5625228 baseEnd_5625228 := by
    simpa [prefixWord, tailWord_5625228, baseEnd_5625228] using wordTrace_append hprefix tailTrace_5625228
  have hstable : (prefixWord ++ tailWord_5625228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625228).length < 2 ^ (prefixWord ++ tailWord_5625228).sum := by decide
  have hdescent : baseEnd_5625228 < baseStart_5625228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625242 : List Nat := [3, 1, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_5625242 : Nat := 118140960795 + 5625242 * 2 ^ 59
def prefixEnd_5625242 : Nat := 4983230072969 + 3 ^ 40 * 5625242 * 2
def baseEnd_5625242 : Nat := 962817647952995149501663

theorem tailTrace_5625242 : CollatzResearch.WordTrace tailWord_5625242 prefixEnd_5625242 962817647952995149501663 := by
  unfold tailWord_5625242
  simp only [CollatzResearch.WordTrace]
  refine ⟨51292357771679105923073495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136779620724477615794862653 51292357771679105923073495)
  ·
    refine ⟨76938536657518658884610243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51292357771679105923073495 76938536657518658884610243)
    ·
      refine ⟨115407804986277988326915365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76938536657518658884610243 115407804986277988326915365)
      ·
        refine ⟨21638963434927122811296631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115407804986277988326915365 21638963434927122811296631)
        ·
          refine ⟨32458445152390684216944947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21638963434927122811296631 32458445152390684216944947)
          ·
            refine ⟨48687667728586026325417421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32458445152390684216944947 48687667728586026325417421)
            ·
              refine ⟨18257875398219759872031533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48687667728586026325417421 18257875398219759872031533)
              ·
                refine ⟨6846703274332409952011825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18257875398219759872031533 6846703274332409952011825)
                ·
                  refine ⟨5135027455749307464008869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846703274332409952011825 5135027455749307464008869)
                  ·
                    refine ⟨962817647952995149501663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5135027455749307464008869 962817647952995149501663)
                    ·
                      rfl

theorem cell23_5625242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_5625242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625242 prefixEnd_5625242 := by exact prefixLift 5625242
  have htrace : WordTrace (prefixWord ++ tailWord_5625242) baseStart_5625242 baseEnd_5625242 := by
    simpa [prefixWord, tailWord_5625242, baseEnd_5625242] using wordTrace_append hprefix tailTrace_5625242
  have hstable : (prefixWord ++ tailWord_5625242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625242).length < 2 ^ (prefixWord ++ tailWord_5625242).sum := by decide
  have hdescent : baseEnd_5625242 < baseStart_5625242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625245 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_5625245 : Nat := 118140960795 + 5625245 * 2 ^ 59
def prefixEnd_5625245 : Nat := 4983230072969 + 3 ^ 40 * 5625245 * 2
def baseEnd_5625245 : Nat := 2888454484300948936767475

theorem tailTrace_5625245 : CollatzResearch.WordTrace tailWord_5625245 prefixEnd_5625245 2888454484300948936767475 := by
  unfold tailWord_5625245
  simp only [CollatzResearch.WordTrace]
  refine ⟨205169540505705555204653189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136779693670470370136435459 205169540505705555204653189)
  ·
    refine ⟨38469288844819791600872473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205169540505705555204653189 38469288844819791600872473)
    ·
      refine ⟨28851966633614843700654355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38469288844819791600872473 28851966633614843700654355)
      ·
        refine ⟨43277949950422265550981533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28851966633614843700654355 43277949950422265550981533)
        ·
          refine ⟨16229231231408349581618075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43277949950422265550981533 16229231231408349581618075)
          ·
            refine ⟨24343846847112524372427113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16229231231408349581618075 24343846847112524372427113)
            ·
              refine ⟨18257885135334393279320335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24343846847112524372427113 18257885135334393279320335)
              ·
                refine ⟨27386827703001589918980503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18257885135334393279320335 27386827703001589918980503)
                ·
                  refine ⟨41080241554502384878470755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27386827703001589918980503 41080241554502384878470755)
                  ·
                    refine ⟨61620362331753577317706133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41080241554502384878470755 61620362331753577317706133)
                    ·
                      refine ⟨2888454484300948936767475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61620362331753577317706133 2888454484300948936767475)
                      ·
                        rfl

theorem cell23_5625245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_5625245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625245 prefixEnd_5625245 := by exact prefixLift 5625245
  have htrace : WordTrace (prefixWord ++ tailWord_5625245) baseStart_5625245 baseEnd_5625245 := by
    simpa [prefixWord, tailWord_5625245, baseEnd_5625245] using wordTrace_append hprefix tailTrace_5625245
  have hstable : (prefixWord ++ tailWord_5625245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625245).length < 2 ^ (prefixWord ++ tailWord_5625245).sum := by decide
  have hdescent : baseEnd_5625245 < baseStart_5625245 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625246 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5625246 : Nat := 118140960795 + 5625246 * 2 ^ 59
def prefixEnd_5625246 : Nat := 4983230072969 + 3 ^ 40 * 5625246 * 2
def baseEnd_5625246 : Nat := 962818332593867810951657

theorem tailTrace_5625246 : CollatzResearch.WordTrace tailWord_5625246 prefixEnd_5625246 962818332593867810951657 := by
  unfold tailWord_5625246
  simp only [CollatzResearch.WordTrace]
  refine ⟨25646197122337741546929949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136779717985801288250293061 25646197122337741546929949)
  ·
    refine ⟨9617323920876653080098731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25646197122337741546929949 9617323920876653080098731)
    ·
      refine ⟨14425985881314979620148097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9617323920876653080098731 14425985881314979620148097)
      ·
        refine ⟨10819489410986234715111073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14425985881314979620148097 10819489410986234715111073)
        ·
          refine ⟨8114617058239676036333305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10819489410986234715111073 8114617058239676036333305)
          ·
            refine ⟨6085962793679757027249979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8114617058239676036333305 6085962793679757027249979)
            ·
              refine ⟨9128944190519635540874969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6085962793679757027249979 9128944190519635540874969)
              ·
                refine ⟨6846708142889726655656227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9128944190519635540874969 6846708142889726655656227)
                ·
                  refine ⟨10270062214334589983484341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6846708142889726655656227 10270062214334589983484341)
                  ·
                    refine ⟨962818332593867810951657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10270062214334589983484341 962818332593867810951657)
                    ·
                      rfl

theorem cell23_5625246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5625246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625246 prefixEnd_5625246 := by exact prefixLift 5625246
  have htrace : WordTrace (prefixWord ++ tailWord_5625246) baseStart_5625246 baseEnd_5625246 := by
    simpa [prefixWord, tailWord_5625246, baseEnd_5625246] using wordTrace_append hprefix tailTrace_5625246
  have hstable : (prefixWord ++ tailWord_5625246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625246).length < 2 ^ (prefixWord ++ tailWord_5625246).sum := by decide
  have hdescent : baseEnd_5625246 < baseStart_5625246 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625309 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_5625309 : Nat := 118140960795 + 5625309 * 2 ^ 59
def prefixEnd_5625309 : Nat := 4983230072969 + 3 ^ 40 * 5625309 * 2
def baseEnd_5625309 : Nat := 2888487347062836686367181

theorem tailTrace_5625309 : CollatzResearch.WordTrace tailWord_5625309 prefixEnd_5625309 2888487347062836686367181 := by
  unfold tailWord_5625309
  simp only [CollatzResearch.WordTrace]
  refine ⟨205171874777473694134982981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136781249851649129423321987 205171874777473694134982981)
  ·
    refine ⟨38469726520776317650309309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205171874777473694134982981 38469726520776317650309309)
    ·
      refine ⟨14426147445291119118865991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38469726520776317650309309 14426147445291119118865991)
      ·
        refine ⟨21639221167936678678298987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14426147445291119118865991 21639221167936678678298987)
        ·
          refine ⟨32458831751905018017448481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21639221167936678678298987 32458831751905018017448481)
          ·
            refine ⟨24344123813928763513086361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32458831751905018017448481 24344123813928763513086361)
            ·
              refine ⟨18258092860446572634814771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24344123813928763513086361 18258092860446572634814771)
              ·
                refine ⟨27387139290669858952222157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18258092860446572634814771 27387139290669858952222157)
                ·
                  refine ⟨10270177234001197107083309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27387139290669858952222157 10270177234001197107083309)
                  ·
                    refine ⟨3851316462750448915156241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10270177234001197107083309 3851316462750448915156241)
                    ·
                      refine ⟨2888487347062836686367181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851316462750448915156241 2888487347062836686367181)
                      ·
                        rfl

theorem cell23_5625309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_5625309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625309 prefixEnd_5625309 := by exact prefixLift 5625309
  have htrace : WordTrace (prefixWord ++ tailWord_5625309) baseStart_5625309 baseEnd_5625309 := by
    simpa [prefixWord, tailWord_5625309, baseEnd_5625309] using wordTrace_append hprefix tailTrace_5625309
  have hstable : (prefixWord ++ tailWord_5625309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625309).length < 2 ^ (prefixWord ++ tailWord_5625309).sum := by decide
  have hdescent : baseEnd_5625309 < baseStart_5625309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625333 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_5625333 : Nat := 118140960795 + 5625333 * 2 ^ 59
def prefixEnd_5625333 : Nat := 4983230072969 + 3 ^ 40 * 5625333 * 2
def baseEnd_5625333 : Nat := 2888499670598544592467071

theorem tailTrace_5625333 : CollatzResearch.WordTrace tailWord_5625333 prefixEnd_5625333 2888499670598544592467071 := by
  unfold tailWord_5625333
  simp only [CollatzResearch.WordTrace]
  refine ⟨205172750129386746233856653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136781833419591164155904435 205172750129386746233856653)
  ·
    refine ⟨76939781298520029837696245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205172750129386746233856653 76939781298520029837696245)
    ·
      refine ⟨7213104496736252797284023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76939781298520029837696245 7213104496736252797284023)
      ·
        refine ⟨10819656745104379195926035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7213104496736252797284023 10819656745104379195926035)
        ·
          refine ⟨16229485117656568793889053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10819656745104379195926035 16229485117656568793889053)
          ·
            refine ⟨6086056919121213297708395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16229485117656568793889053 6086056919121213297708395)
            ·
              refine ⟨9129085378681819946562593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086056919121213297708395 9129085378681819946562593)
              ·
                refine ⟨6846814034011364959921945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9129085378681819946562593 6846814034011364959921945)
                ·
                  refine ⟨5135110525508523719941459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6846814034011364959921945 5135110525508523719941459)
                  ·
                    refine ⟨7702665788262785579912189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135110525508523719941459 7702665788262785579912189)
                    ·
                      refine ⟨2888499670598544592467071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7702665788262785579912189 2888499670598544592467071)
                      ·
                        rfl

theorem cell23_5625333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_5625333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625333 prefixEnd_5625333 := by exact prefixLift 5625333
  have htrace : WordTrace (prefixWord ++ tailWord_5625333) baseStart_5625333 baseEnd_5625333 := by
    simpa [prefixWord, tailWord_5625333, baseEnd_5625333] using wordTrace_append hprefix tailTrace_5625333
  have hstable : (prefixWord ++ tailWord_5625333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625333).length < 2 ^ (prefixWord ++ tailWord_5625333).sum := by decide
  have hdescent : baseEnd_5625333 < baseStart_5625333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625350 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_5625350 : Nat := 118140960795 + 5625350 * 2 ^ 59
def prefixEnd_5625350 : Nat := 4983230072969 + 3 ^ 40 * 5625350 * 2
def baseEnd_5625350 : Nat := 2888508399769671025954493

theorem tailTrace_5625350 : CollatzResearch.WordTrace tailWord_5625350 prefixEnd_5625350 2888508399769671025954493 := by
  unfold tailWord_5625350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411667817822661191788297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136782246780216772091483669 6411667817822661191788297)
  ·
    refine ⟨4808750863366995893841223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6411667817822661191788297 4808750863366995893841223)
    ·
      refine ⟨7213126295050493840761835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808750863366995893841223 7213126295050493840761835)
      ·
        refine ⟨10819689442575740761142753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7213126295050493840761835 10819689442575740761142753)
        ·
          refine ⟨8114767081931805570857065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10819689442575740761142753 8114767081931805570857065)
          ·
            refine ⟨6086075311448854178142799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8114767081931805570857065 6086075311448854178142799)
            ·
              refine ⟨9129112967173281267214199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086075311448854178142799 9129112967173281267214199)
              ·
                refine ⟨13693669450759921900821299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9129112967173281267214199 13693669450759921900821299)
                ·
                  refine ⟨20540504176139882851231949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13693669450759921900821299 20540504176139882851231949)
                  ·
                    refine ⟨7702689066052456069211981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20540504176139882851231949 7702689066052456069211981)
                    ·
                      refine ⟨2888508399769671025954493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7702689066052456069211981 2888508399769671025954493)
                      ·
                        rfl

theorem cell23_5625350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_5625350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625350 prefixEnd_5625350 := by exact prefixLift 5625350
  have htrace : WordTrace (prefixWord ++ tailWord_5625350) baseStart_5625350 baseEnd_5625350 := by
    simpa [prefixWord, tailWord_5625350, baseEnd_5625350] using wordTrace_append hprefix tailTrace_5625350
  have hstable : (prefixWord ++ tailWord_5625350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625350).length < 2 ^ (prefixWord ++ tailWord_5625350).sum := by decide
  have hdescent : baseEnd_5625350 < baseStart_5625350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625356 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_5625356 : Nat := 118140960795 + 5625356 * 2 ^ 59
def prefixEnd_5625356 : Nat := 4983230072969 + 3 ^ 40 * 5625356 * 2
def baseEnd_5625356 : Nat := 2888511480653598002479465

theorem tailTrace_5625356 : CollatzResearch.WordTrace tailWord_5625356 prefixEnd_5625356 2888511480653598002479465 := by
  unfold tailWord_5625356
  simp only [CollatzResearch.WordTrace]
  refine ⟨102586794504151710580971961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136782392672202280774629281 102586794504151710580971961)
  ·
    refine ⟨76940095878113782935728971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102586794504151710580971961 76940095878113782935728971)
    ·
      refine ⟨115410143817170674403593457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76940095878113782935728971 115410143817170674403593457)
      ·
        refine ⟨86557607862878005802695093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115410143817170674403593457 86557607862878005802695093)
        ·
          refine ⟨8114775737144813044002665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86557607862878005802695093 8114775737144813044002665)
          ·
            refine ⟨6086081802858609783001999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8114775737144813044002665 6086081802858609783001999)
            ·
              refine ⟨9129122704287914674502999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086081802858609783001999 9129122704287914674502999)
              ·
                refine ⟨13693684056431872011754499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9129122704287914674502999 13693684056431872011754499)
                ·
                  refine ⟨20540526084647808017631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13693684056431872011754499 20540526084647808017631749)
                  ·
                    refine ⟨3851348640871464003305953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20540526084647808017631749 3851348640871464003305953)
                    ·
                      refine ⟨2888511480653598002479465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851348640871464003305953 2888511480653598002479465)
                      ·
                        rfl

theorem cell23_5625356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_5625356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625356 prefixEnd_5625356 := by exact prefixLift 5625356
  have htrace : WordTrace (prefixWord ++ tailWord_5625356) baseStart_5625356 baseEnd_5625356 := by
    simpa [prefixWord, tailWord_5625356, baseEnd_5625356] using wordTrace_append hprefix tailTrace_5625356
  have hstable : (prefixWord ++ tailWord_5625356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625356).length < 2 ^ (prefixWord ++ tailWord_5625356).sum := by decide
  have hdescent : baseEnd_5625356 < baseStart_5625356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625375 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 1, 7]
def baseStart_5625375 : Nat := 118140960795 + 5625375 * 2 ^ 59
def prefixEnd_5625375 : Nat := 4983230072969 + 3 ^ 40 * 5625375 * 2
def baseEnd_5625375 : Nat := 962840412262011142713959

theorem tailTrace_5625375 : CollatzResearch.WordTrace tailWord_5625375 prefixEnd_5625375 962840412262011142713959 := by
  unfold tailWord_5625375
  simp only [CollatzResearch.WordTrace]
  refine ⟨205174281995234587406885579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136782854663489724937923719 205174281995234587406885579)
  ·
    refine ⟨307761422992851881110328369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205174281995234587406885579 307761422992851881110328369)
    ·
      refine ⟨230821067244638910832746277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307761422992851881110328369 230821067244638910832746277)
      ·
        refine ⟨43278950108369795781139927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230821067244638910832746277 43278950108369795781139927)
        ·
          refine ⟨64918425162554693671709891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43278950108369795781139927 64918425162554693671709891)
          ·
            refine ⟨97377637743832040507564837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64918425162554693671709891 97377637743832040507564837)
            ·
              refine ⟨18258307076968507595168407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97377637743832040507564837 18258307076968507595168407)
              ·
                refine ⟨27387460615452761392752611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18258307076968507595168407 27387460615452761392752611)
                ·
                  refine ⟨41081190923179142089128917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27387460615452761392752611 41081190923179142089128917)
                  ·
                    refine ⟨962840412262011142713959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41081190923179142089128917 962840412262011142713959)
                    ·
                      rfl

theorem cell23_5625375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 7].length) (baseStart_5625375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625375 prefixEnd_5625375 := by exact prefixLift 5625375
  have htrace : WordTrace (prefixWord ++ tailWord_5625375) baseStart_5625375 baseEnd_5625375 := by
    simpa [prefixWord, tailWord_5625375, baseEnd_5625375] using wordTrace_append hprefix tailTrace_5625375
  have hstable : (prefixWord ++ tailWord_5625375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625375).length < 2 ^ (prefixWord ++ tailWord_5625375).sum := by decide
  have hdescent : baseEnd_5625375 < baseStart_5625375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625422 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_5625422 : Nat := 118140960795 + 5625422 * 2 ^ 59
def prefixEnd_5625422 : Nat := 4983230072969 + 3 ^ 40 * 5625422 * 2
def baseEnd_5625422 : Nat := 962848456792264914751387

theorem tailTrace_5625422 : CollatzResearch.WordTrace tailWord_5625422 prefixEnd_5625422 962848456792264914751387 := by
  unfold tailWord_5625422
  simp only [CollatzResearch.WordTrace]
  refine ⟨25646999528258039304230815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136783997484042876289231013 25646999528258039304230815)
  ·
    refine ⟨38470499292387058956346223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25646999528258039304230815 38470499292387058956346223)
    ·
      refine ⟨57705748938580588434519335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38470499292387058956346223 57705748938580588434519335)
      ·
        refine ⟨86558623407870882651779003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57705748938580588434519335 86558623407870882651779003)
        ·
          refine ⟨129837935111806323977668505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86558623407870882651779003 129837935111806323977668505)
          ·
            refine ⟨97378451333854742983251379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129837935111806323977668505 97378451333854742983251379)
            ·
              refine ⟨146067677000782114474877069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97378451333854742983251379 146067677000782114474877069)
              ·
                refine ⟨54775378875293292928078901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146067677000782114474877069 54775378875293292928078901)
                ·
                  refine ⟨5135191769558746212007397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54775378875293292928078901 5135191769558746212007397)
                  ·
                    refine ⟨962848456792264914751387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5135191769558746212007397 962848456792264914751387)
                    ·
                      rfl

theorem cell23_5625422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_5625422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625422 prefixEnd_5625422 := by exact prefixLift 5625422
  have htrace : WordTrace (prefixWord ++ tailWord_5625422) baseStart_5625422 baseEnd_5625422 := by
    simpa [prefixWord, tailWord_5625422, baseEnd_5625422] using wordTrace_append hprefix tailTrace_5625422
  have hstable : (prefixWord ++ tailWord_5625422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625422).length < 2 ^ (prefixWord ++ tailWord_5625422).sum := by decide
  have hdescent : baseEnd_5625422 < baseStart_5625422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625455 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6]
def baseStart_5625455 : Nat := 118140960795 + 5625455 * 2 ^ 59
def prefixEnd_5625455 : Nat := 4983230072969 + 3 ^ 40 * 5625455 * 2
def baseEnd_5625455 : Nat := 2888562315238393115141509

theorem tailTrace_5625455 : CollatzResearch.WordTrace tailWord_5625455 prefixEnd_5625455 2888562315238393115141509 := by
  unfold tailWord_5625455
  simp only [CollatzResearch.WordTrace]
  refine ⟨205177199834944761069797819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136784799889963174046531879 205177199834944761069797819)
  ·
    refine ⟨307765799752417141604696729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205177199834944761069797819 307765799752417141604696729)
    ·
      refine ⟨230824349814312856203522547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307765799752417141604696729 230824349814312856203522547)
      ·
        refine ⟨346236524721469284305283821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230824349814312856203522547 346236524721469284305283821)
        ·
          refine ⟨129838696770550981614481433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346236524721469284305283821 129838696770550981614481433)
          ·
            refine ⟨97379022577913236210861075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129838696770550981614481433 97379022577913236210861075)
            ·
              refine ⟨146068533866869854316291613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97379022577913236210861075 146068533866869854316291613)
              ·
                refine ⟨54775700200076195368609355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146068533866869854316291613 54775700200076195368609355)
                ·
                  refine ⟨82163550300114293052914033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54775700200076195368609355 82163550300114293052914033)
                  ·
                    refine ⟨61622662725085719789685525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82163550300114293052914033 61622662725085719789685525)
                    ·
                      refine ⟨2888562315238393115141509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61622662725085719789685525 2888562315238393115141509)
                      ·
                        rfl

theorem cell23_5625455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_5625455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625455 prefixEnd_5625455 := by exact prefixLift 5625455
  have htrace : WordTrace (prefixWord ++ tailWord_5625455) baseStart_5625455 baseEnd_5625455 := by
    simpa [prefixWord, tailWord_5625455, baseEnd_5625455] using wordTrace_append hprefix tailTrace_5625455
  have hstable : (prefixWord ++ tailWord_5625455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625455).length < 2 ^ (prefixWord ++ tailWord_5625455).sum := by decide
  have hdescent : baseEnd_5625455 < baseStart_5625455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625456 : List Nat := [2, 1, 1, 1, 6, 2, 1, 4, 1, 4]
def baseStart_5625456 : Nat := 118140960795 + 5625456 * 2 ^ 59
def prefixEnd_5625456 : Nat := 4983230072969 + 3 ^ 40 * 5625456 * 2
def baseEnd_5625456 : Nat := 962854276239682537076335

theorem tailTrace_5625456 : CollatzResearch.WordTrace tailWord_5625456 prefixEnd_5625456 962854276239682537076335 := by
  unfold tailWord_5625456
  simp only [CollatzResearch.WordTrace]
  refine ⟨102588618153970569120292111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136784824205294092160389481 102588618153970569120292111)
  ·
    refine ⟨153882927230955853680438167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102588618153970569120292111 153882927230955853680438167)
    ·
      refine ⟨230824390846433780520657251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153882927230955853680438167 230824390846433780520657251)
      ·
        refine ⟨346236586269650670780985877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230824390846433780520657251 346236586269650670780985877)
        ·
          refine ⟨16229839981389875192858713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 346236586269650670780985877 16229839981389875192858713)
          ·
            refine ⟨12172379986042406394644035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16229839981389875192858713 12172379986042406394644035)
            ·
              refine ⟨18258569979063609591966053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172379986042406394644035 18258569979063609591966053)
              ·
                refine ⟨3423481871074426798493635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18258569979063609591966053 3423481871074426798493635)
                ·
                  refine ⟨5135222806611640197740453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423481871074426798493635 5135222806611640197740453)
                  ·
                    refine ⟨962854276239682537076335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5135222806611640197740453 962854276239682537076335)
                    ·
                      rfl

theorem cell23_5625456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_5625456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625456 prefixEnd_5625456 := by exact prefixLift 5625456
  have htrace : WordTrace (prefixWord ++ tailWord_5625456) baseStart_5625456 baseEnd_5625456 := by
    simpa [prefixWord, tailWord_5625456, baseEnd_5625456] using wordTrace_append hprefix tailTrace_5625456
  have hstable : (prefixWord ++ tailWord_5625456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625456).length < 2 ^ (prefixWord ++ tailWord_5625456).sum := by decide
  have hdescent : baseEnd_5625456 < baseStart_5625456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625475 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7]
def baseStart_5625475 : Nat := 118140960795 + 5625475 * 2 ^ 59
def prefixEnd_5625475 : Nat := 4983230072969 + 3 ^ 40 * 5625475 * 2
def baseEnd_5625475 : Nat := 2888572584851483036891417

theorem tailTrace_5625475 : CollatzResearch.WordTrace tailWord_5625475 prefixEnd_5625475 2888572584851483036891417 := by
  unfold tailWord_5625475
  simp only [CollatzResearch.WordTrace]
  refine ⟨205177929294872304485525879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136785286196581536323683919 205177929294872304485525879)
  ·
    refine ⟨307766893942308456728288819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205177929294872304485525879 307766893942308456728288819)
    ·
      refine ⟨461650340913462685092433229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307766893942308456728288819 461650340913462685092433229)
      ·
        refine ⟨173118877842548506909662461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461650340913462685092433229 173118877842548506909662461)
        ·
          refine ⟨64919579190955690091123423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173118877842548506909662461 64919579190955690091123423)
          ·
            refine ⟨97379368786433535136685135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64919579190955690091123423 97379368786433535136685135)
            ·
              refine ⟨146069053179650302705027703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97379368786433535136685135 146069053179650302705027703)
              ·
                refine ⟨219103579769475454057541555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146069053179650302705027703 219103579769475454057541555)
                ·
                  refine ⟨328655369654213181086312333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219103579769475454057541555 328655369654213181086312333)
                  ·
                    refine ⟨123245763620329942907367125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328655369654213181086312333 123245763620329942907367125)
                    ·
                      refine ⟨2888572584851483036891417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123245763620329942907367125 2888572584851483036891417)
                      ·
                        rfl

theorem cell23_5625475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_5625475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625475 prefixEnd_5625475 := by exact prefixLift 5625475
  have htrace : WordTrace (prefixWord ++ tailWord_5625475) baseStart_5625475 baseEnd_5625475 := by
    simpa [prefixWord, tailWord_5625475, baseEnd_5625475] using wordTrace_append hprefix tailTrace_5625475
  have hstable : (prefixWord ++ tailWord_5625475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625475).length < 2 ^ (prefixWord ++ tailWord_5625475).sum := by decide
  have hdescent : baseEnd_5625475 < baseStart_5625475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625479 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 3]
def baseStart_5625479 : Nat := 118140960795 + 5625479 * 2 ^ 59
def prefixEnd_5625479 : Nat := 4983230072969 + 3 ^ 40 * 5625479 * 2
def baseEnd_5625479 : Nat := 2888574638774101021241399

theorem tailTrace_5625479 : CollatzResearch.WordTrace tailWord_5625479 prefixEnd_5625479 2888574638774101021241399 := by
  unfold tailWord_5625479
  simp only [CollatzResearch.WordTrace]
  refine ⟨205178075186857813168671491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136785383457905208779114327 205178075186857813168671491)
  ·
    refine ⟨307767112780286719753007237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205178075186857813168671491 307767112780286719753007237)
    ·
      refine ⟨57706333646303759953688857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307767112780286719753007237 57706333646303759953688857)
      ·
        refine ⟨43279750234727819965266643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57706333646303759953688857 43279750234727819965266643)
        ·
          refine ⟨64919625352091729947899965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43279750234727819965266643 64919625352091729947899965)
          ·
            refine ⟨24344859507034398730462487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64919625352091729947899965 24344859507034398730462487)
            ·
              refine ⟨36517289260551598095693731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24344859507034398730462487 36517289260551598095693731)
              ·
                refine ⟨54775933890827397143540597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36517289260551598095693731 54775933890827397143540597)
                ·
                  refine ⟨5135243802265068482206931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54775933890827397143540597 5135243802265068482206931)
                  ·
                    refine ⟨7702865703397602723310397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135243802265068482206931 7702865703397602723310397)
                    ·
                      refine ⟨2888574638774101021241399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7702865703397602723310397 2888574638774101021241399)
                      ·
                        rfl

theorem cell23_5625479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_5625479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625479 prefixEnd_5625479 := by exact prefixLift 5625479
  have htrace : WordTrace (prefixWord ++ tailWord_5625479) baseStart_5625479 baseEnd_5625479 := by
    simpa [prefixWord, tailWord_5625479, baseEnd_5625479] using wordTrace_append hprefix tailTrace_5625479
  have hstable : (prefixWord ++ tailWord_5625479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625479).length < 2 ^ (prefixWord ++ tailWord_5625479).sum := by decide
  have hdescent : baseEnd_5625479 < baseStart_5625479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625489 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_5625489 : Nat := 118140960795 + 5625489 * 2 ^ 59
def prefixEnd_5625489 : Nat := 4983230072969 + 3 ^ 40 * 5625489 * 2
def baseEnd_5625489 : Nat := 2888579773580645982116353

theorem tailTrace_5625489 : CollatzResearch.WordTrace tailWord_5625489 prefixEnd_5625489 2888579773580645982116353 := by
  unfold tailWord_5625489
  simp only [CollatzResearch.WordTrace]
  refine ⟨205178439916821584876535521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136785626611214389917690347 205178439916821584876535521)
  ·
    refine ⟨153883829937616188657401641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205178439916821584876535521 153883829937616188657401641)
    ·
      refine ⟨115412872453212141493051231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153883829937616188657401641 115412872453212141493051231)
      ·
        refine ⟨173119308679818212239576847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115412872453212141493051231 173119308679818212239576847)
        ·
          refine ⟨259678963019727318359365271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173119308679818212239576847 259678963019727318359365271)
          ·
            refine ⟨389518444529590977539047907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259678963019727318359365271 389518444529590977539047907)
            ·
              refine ⟨584277666794386466308571861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389518444529590977539047907 584277666794386466308571861)
              ·
                refine ⟨13694007815493432804107153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584277666794386466308571861 13694007815493432804107153)
                ·
                  refine ⟨10270505861620074603080365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13694007815493432804107153 10270505861620074603080365)
                  ·
                    refine ⟨3851439698107527976155137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10270505861620074603080365 3851439698107527976155137)
                    ·
                      refine ⟨2888579773580645982116353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851439698107527976155137 2888579773580645982116353)
                      ·
                        rfl

theorem cell23_5625489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_5625489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625489 prefixEnd_5625489 := by exact prefixLift 5625489
  have htrace : WordTrace (prefixWord ++ tailWord_5625489) baseStart_5625489 baseEnd_5625489 := by
    simpa [prefixWord, tailWord_5625489, baseEnd_5625489] using wordTrace_append hprefix tailTrace_5625489
  have hstable : (prefixWord ++ tailWord_5625489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625489).length < 2 ^ (prefixWord ++ tailWord_5625489).sum := by decide
  have hdescent : baseEnd_5625489 < baseStart_5625489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625503 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 6]
def baseStart_5625503 : Nat := 118140960795 + 5625503 * 2 ^ 59
def prefixEnd_5625503 : Nat := 4983230072969 + 3 ^ 40 * 5625503 * 2
def baseEnd_5625503 : Nat := 320954106923312103037921

theorem tailTrace_5625503 : CollatzResearch.WordTrace tailWord_5625503 prefixEnd_5625503 320954106923312103037921 := by
  unfold tailWord_5625503
  simp only [CollatzResearch.WordTrace]
  refine ⟨205178950538770865267545163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136785967025847243511696775 205178950538770865267545163)
  ·
    refine ⟨307768425808156297901317745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205178950538770865267545163 307768425808156297901317745)
    ·
      refine ⟨230826319356117223425988309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307768425808156297901317745 230826319356117223425988309)
      ·
        refine ⟨5409991859908997424046601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 230826319356117223425988309 5409991859908997424046601)
        ·
          refine ⟨4057493894931748068034951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5409991859908997424046601 4057493894931748068034951)
          ·
            refine ⟨6086240842397622102052427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057493894931748068034951 6086240842397622102052427)
            ·
              refine ⟨9129361263596433153078641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6086240842397622102052427 9129361263596433153078641)
              ·
                refine ⟨6847020947697324864808981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9129361263596433153078641 6847020947697324864808981)
                ·
                  refine ⟨320954106923312103037921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6847020947697324864808981 320954106923312103037921)
                  ·
                    rfl

theorem cell23_5625503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 6].length) (baseStart_5625503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625503 prefixEnd_5625503 := by exact prefixLift 5625503
  have htrace : WordTrace (prefixWord ++ tailWord_5625503) baseStart_5625503 baseEnd_5625503 := by
    simpa [prefixWord, tailWord_5625503, baseEnd_5625503] using wordTrace_append hprefix tailTrace_5625503
  have hstable : (prefixWord ++ tailWord_5625503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625503).length < 2 ^ (prefixWord ++ tailWord_5625503).sum := by decide
  have hdescent : baseEnd_5625503 < baseStart_5625503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625522 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5625522 : Nat := 118140960795 + 5625522 * 2 ^ 59
def prefixEnd_5625522 : Nat := 4983230072969 + 3 ^ 40 * 5625522 * 2
def baseEnd_5625522 : Nat := 2888596718442244353003701

theorem tailTrace_5625522 : CollatzResearch.WordTrace tailWord_5625522 prefixEnd_5625522 2888596718442244353003701 := by
  unfold tailWord_5625522
  simp only [CollatzResearch.WordTrace]
  refine ⟨51294910881425507878121705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136786429017134687674991213 51294910881425507878121705)
  ·
    refine ⟨38471183161069130908591279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51294910881425507878121705 38471183161069130908591279)
    ·
      refine ⟨57706774741603696362886919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38471183161069130908591279 57706774741603696362886919)
      ·
        refine ⟨86560162112405544544330379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57706774741603696362886919 86560162112405544544330379)
        ·
          refine ⟨129840243168608316816495569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86560162112405544544330379 129840243168608316816495569)
          ·
            refine ⟨97380182376456237612371677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129840243168608316816495569 97380182376456237612371677)
            ·
              refine ⟨36517568391171089104639379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97380182376456237612371677 36517568391171089104639379)
              ·
                refine ⟨54776352586756633656959069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36517568391171089104639379 54776352586756633656959069)
                ·
                  refine ⟨20541132220033737621359651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54776352586756633656959069 20541132220033737621359651)
                  ·
                    refine ⟨30811698330050606432039477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20541132220033737621359651 30811698330050606432039477)
                    ·
                      refine ⟨2888596718442244353003701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30811698330050606432039477 2888596718442244353003701)
                      ·
                        rfl

theorem cell23_5625522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5625522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625522 prefixEnd_5625522 := by exact prefixLift 5625522
  have htrace : WordTrace (prefixWord ++ tailWord_5625522) baseStart_5625522 baseEnd_5625522 := by
    simpa [prefixWord, tailWord_5625522, baseEnd_5625522] using wordTrace_append hprefix tailTrace_5625522
  have hstable : (prefixWord ++ tailWord_5625522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625522).length < 2 ^ (prefixWord ++ tailWord_5625522).sum := by decide
  have hdescent : baseEnd_5625522 < baseStart_5625522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625529 : List Nat := [1, 2, 1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_5625529 : Nat := 118140960795 + 5625529 * 2 ^ 59
def prefixEnd_5625529 : Nat := 4983230072969 + 3 ^ 40 * 5625529 * 2
def baseEnd_5625529 : Nat := 962866770935608608538723

theorem tailTrace_5625529 : CollatzResearch.WordTrace tailWord_5625529 prefixEnd_5625529 962866770935608608538723 := by
  unfold tailWord_5625529
  simp only [CollatzResearch.WordTrace]
  refine ⟨205179898836676671707991641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136786599224451114471994427 205179898836676671707991641)
  ·
    refine ⟨153884924127507503780993731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205179898836676671707991641 153884924127507503780993731)
    ·
      refine ⟨230827386191261255671490597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153884924127507503780993731 230827386191261255671490597)
      ·
        refine ⟨43280134910861485438404487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230827386191261255671490597 43280134910861485438404487)
        ·
          refine ⟨64920202366292228157606731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43280134910861485438404487 64920202366292228157606731)
          ·
            refine ⟨97380303549438342236410097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64920202366292228157606731 97380303549438342236410097)
            ·
              refine ⟨73035227662078756677307573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97380303549438342236410097 73035227662078756677307573)
              ·
                refine ⟨6847052593319883438497585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73035227662078756677307573 6847052593319883438497585)
                ·
                  refine ⟨5135289444989912578873189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6847052593319883438497585 5135289444989912578873189)
                  ·
                    refine ⟨962866770935608608538723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5135289444989912578873189 962866770935608608538723)
                    ·
                      rfl

theorem cell23_5625529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_5625529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625529 prefixEnd_5625529 := by exact prefixLift 5625529
  have htrace : WordTrace (prefixWord ++ tailWord_5625529) baseStart_5625529 baseEnd_5625529 := by
    simpa [prefixWord, tailWord_5625529, baseEnd_5625529] using wordTrace_append hprefix tailTrace_5625529
  have hstable : (prefixWord ++ tailWord_5625529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625529).length < 2 ^ (prefixWord ++ tailWord_5625529).sum := by decide
  have hdescent : baseEnd_5625529 < baseStart_5625529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625536 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2]
def baseStart_5625536 : Nat := 118140960795 + 5625536 * 2 ^ 59
def prefixEnd_5625536 : Nat := 4983230072969 + 3 ^ 40 * 5625536 * 2
def baseEnd_5625536 : Nat := 2888603907171407298228637

theorem tailTrace_5625536 : CollatzResearch.WordTrace tailWord_5625536 prefixEnd_5625536 2888603907171407298228637 := by
  unfold tailWord_5625536
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590077073825655951748231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136786769431767541268997641 102590077073825655951748231)
  ·
    refine ⟨153885115610738483927622347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102590077073825655951748231 153885115610738483927622347)
    ·
      refine ⟨230827673416107725891433521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153885115610738483927622347 230827673416107725891433521)
      ·
        refine ⟨173120755062080794418575141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230827673416107725891433521 173120755062080794418575141)
        ·
          refine ⟨32460141574140148953482839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173120755062080794418575141 32460141574140148953482839)
          ·
            refine ⟨48690212361210223430224259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32460141574140148953482839 48690212361210223430224259)
            ·
              refine ⟨73035318541815335145336389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48690212361210223430224259 73035318541815335145336389)
              ·
                refine ⟨13694122226590375339750573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73035318541815335145336389 13694122226590375339750573)
                ·
                  refine ⟨5135295834971390752406465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13694122226590375339750573 5135295834971390752406465)
                  ·
                    refine ⟨3851471876228543064304849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5135295834971390752406465 3851471876228543064304849)
                    ·
                      refine ⟨2888603907171407298228637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851471876228543064304849 2888603907171407298228637)
                      ·
                        rfl

theorem cell23_5625536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_5625536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625536 prefixEnd_5625536 := by exact prefixLift 5625536
  have htrace : WordTrace (prefixWord ++ tailWord_5625536) baseStart_5625536 baseEnd_5625536 := by
    simpa [prefixWord, tailWord_5625536, baseEnd_5625536] using wordTrace_append hprefix tailTrace_5625536
  have hstable : (prefixWord ++ tailWord_5625536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625536).length < 2 ^ (prefixWord ++ tailWord_5625536).sum := by decide
  have hdescent : baseEnd_5625536 < baseStart_5625536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625556 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_5625556 : Nat := 118140960795 + 5625556 * 2 ^ 59
def prefixEnd_5625556 : Nat := 4983230072969 + 3 ^ 40 * 5625556 * 2
def baseEnd_5625556 : Nat := 2888614176784497219978545

theorem tailTrace_5625556 : CollatzResearch.WordTrace tailWord_5625556 prefixEnd_5625556 2888614176784497219978545 := by
  unfold tailWord_5625556
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590441803789427659612261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136787255738385903546149681 102590441803789427659612261)
  ·
    refine ⟨19235707838210517686177299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102590441803789427659612261 19235707838210517686177299)
    ·
      refine ⟨28853561757315776529265949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19235707838210517686177299 28853561757315776529265949)
      ·
        refine ⟨10820085658993416198474731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28853561757315776529265949 10820085658993416198474731)
        ·
          refine ⟨16230128488490124297712097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10820085658993416198474731 16230128488490124297712097)
          ·
            refine ⟨12172596366367593223284073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16230128488490124297712097 12172596366367593223284073)
            ·
              refine ⟨9129447274775694917463055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12172596366367593223284073 9129447274775694917463055)
              ·
                refine ⟨13694170912163542376194583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9129447274775694917463055 13694170912163542376194583)
                ·
                  refine ⟨20541256368245313564291875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13694170912163542376194583 20541256368245313564291875)
                  ·
                    refine ⟨30811884552367970346437813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20541256368245313564291875 30811884552367970346437813)
                    ·
                      refine ⟨2888614176784497219978545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30811884552367970346437813 2888614176784497219978545)
                      ·
                        rfl

theorem cell23_5625556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_5625556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625556 prefixEnd_5625556 := by exact prefixLift 5625556
  have htrace : WordTrace (prefixWord ++ tailWord_5625556) baseStart_5625556 baseEnd_5625556 := by
    simpa [prefixWord, tailWord_5625556, baseEnd_5625556] using wordTrace_append hprefix tailTrace_5625556
  have hstable : (prefixWord ++ tailWord_5625556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625556).length < 2 ^ (prefixWord ++ tailWord_5625556).sum := by decide
  have hdescent : baseEnd_5625556 < baseStart_5625556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625572 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_5625572 : Nat := 118140960795 + 5625572 * 2 ^ 59
def prefixEnd_5625572 : Nat := 4983230072969 + 3 ^ 40 * 5625572 * 2
def baseEnd_5625572 : Nat := 962874130824989719126157

theorem tailTrace_5625572 : CollatzResearch.WordTrace tailWord_5625572 prefixEnd_5625572 962874130824989719126157 := by
  unfold tailWord_5625572
  simp only [CollatzResearch.WordTrace]
  refine ⟨102590733587760445025903485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136787644783680593367871313 102590733587760445025903485)
  ·
    refine ⟨38471525095410166884713807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102590733587760445025903485 38471525095410166884713807)
    ·
      refine ⟨57707287643115250327070711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38471525095410166884713807 57707287643115250327070711)
      ·
        refine ⟨86560931464672875490606067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57707287643115250327070711 86560931464672875490606067)
        ·
          refine ⟨129841397197009313235909101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86560931464672875490606067 129841397197009313235909101)
          ·
            refine ⟨48690523948878492463465913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129841397197009313235909101 48690523948878492463465913)
            ·
              refine ⟨36517892961658869347599435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48690523948878492463465913 36517892961658869347599435)
              ·
                refine ⟨54776839442488304021399153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36517892961658869347599435 54776839442488304021399153)
                ·
                  refine ⟨41082629581866228016049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54776839442488304021399153 41082629581866228016049365)
                  ·
                    refine ⟨962874130824989719126157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41082629581866228016049365 962874130824989719126157)
                    ·
                      rfl

theorem cell23_5625572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_5625572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625572 prefixEnd_5625572 := by exact prefixLift 5625572
  have htrace : WordTrace (prefixWord ++ tailWord_5625572) baseStart_5625572 baseEnd_5625572 := by
    simpa [prefixWord, tailWord_5625572, baseEnd_5625572] using wordTrace_append hprefix tailTrace_5625572
  have hstable : (prefixWord ++ tailWord_5625572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625572).length < 2 ^ (prefixWord ++ tailWord_5625572).sum := by decide
  have hdescent : baseEnd_5625572 < baseStart_5625572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625592 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_5625592 : Nat := 118140960795 + 5625592 * 2 ^ 59
def prefixEnd_5625592 : Nat := 4983230072969 + 3 ^ 40 * 5625592 * 2
def baseEnd_5625592 : Nat := 2888632662088059079128379

theorem tailTrace_5625592 : CollatzResearch.WordTrace tailWord_5625592 prefixEnd_5625592 2888632662088059079128379 := by
  unfold tailWord_5625592
  simp only [CollatzResearch.WordTrace]
  refine ⟨102591098317724216733767515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136788131090298955645023353 102591098317724216733767515)
  ·
    refine ⟨153886647476586325100651273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102591098317724216733767515 153886647476586325100651273)
    ·
      refine ⟨115414985607439743825488455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153886647476586325100651273 115414985607439743825488455)
      ·
        refine ⟨173122478411159615738232683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115414985607439743825488455 173122478411159615738232683)
        ·
          refine ⟨259683717616739423607349025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173122478411159615738232683 259683717616739423607349025)
          ·
            refine ⟨194762788212554567705511769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259683717616739423607349025 194762788212554567705511769)
            ·
              refine ⟨146072091159415925779133827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194762788212554567705511769 146072091159415925779133827)
              ·
                refine ⟨219108136739123888668700741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146072091159415925779133827 219108136739123888668700741)
                ·
                  refine ⟨41082775638585729125381389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219108136739123888668700741 41082775638585729125381389)
                  ·
                    refine ⟨15406040864469648422018021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41082775638585729125381389 15406040864469648422018021)
                    ·
                      refine ⟨2888632662088059079128379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15406040864469648422018021 2888632662088059079128379)
                      ·
                        rfl

theorem cell23_5625592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_5625592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625592 prefixEnd_5625592 := by exact prefixLift 5625592
  have htrace : WordTrace (prefixWord ++ tailWord_5625592) baseStart_5625592 baseEnd_5625592 := by
    simpa [prefixWord, tailWord_5625592, baseEnd_5625592] using wordTrace_append hprefix tailTrace_5625592
  have hstable : (prefixWord ++ tailWord_5625592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625592).length < 2 ^ (prefixWord ++ tailWord_5625592).sum := by decide
  have hdescent : baseEnd_5625592 < baseStart_5625592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625596 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_5625596 : Nat := 118140960795 + 5625596 * 2 ^ 59
def prefixEnd_5625596 : Nat := 4983230072969 + 3 ^ 40 * 5625596 * 2
def baseEnd_5625596 : Nat := 2888634716010677063478361

theorem tailTrace_5625596 : CollatzResearch.WordTrace tailWord_5625596 prefixEnd_5625596 2888634716010677063478361 := by
  unfold tailWord_5625596
  simp only [CollatzResearch.WordTrace]
  refine ⟨102591171263716971075340321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136788228351622628100453761 102591171263716971075340321)
  ·
    refine ⟨76943378447787728306505241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102591171263716971075340321 76943378447787728306505241)
    ·
      refine ⟨57707533835840796229878931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76943378447787728306505241 57707533835840796229878931)
      ·
        refine ⟨86561300753761194344818397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57707533835840796229878931 86561300753761194344818397)
        ·
          refine ⟨32460487782660447879306899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86561300753761194344818397 32460487782660447879306899)
          ·
            refine ⟨48690731673990671818960349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32460487782660447879306899 48690731673990671818960349)
            ·
              refine ⟨18259024377746501932110131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48690731673990671818960349 18259024377746501932110131)
              ·
                refine ⟨27388536566619752898165197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18259024377746501932110131 27388536566619752898165197)
                ·
                  refine ⟨10270701212482407336811949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27388536566619752898165197 10270701212482407336811949)
                  ·
                    refine ⟨3851512954680902751304481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10270701212482407336811949 3851512954680902751304481)
                    ·
                      refine ⟨2888634716010677063478361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851512954680902751304481 2888634716010677063478361)
                      ·
                        rfl

theorem cell23_5625596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_5625596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625596 prefixEnd_5625596 := by exact prefixLift 5625596
  have htrace : WordTrace (prefixWord ++ tailWord_5625596) baseStart_5625596 baseEnd_5625596 := by
    simpa [prefixWord, tailWord_5625596, baseEnd_5625596] using wordTrace_append hprefix tailTrace_5625596
  have hstable : (prefixWord ++ tailWord_5625596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625596).length < 2 ^ (prefixWord ++ tailWord_5625596).sum := by decide
  have hdescent : baseEnd_5625596 < baseStart_5625596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625649 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 7]
def baseStart_5625649 : Nat := 118140960795 + 5625649 * 2 ^ 59
def prefixEnd_5625649 : Nat := 4983230072969 + 3 ^ 40 * 5625649 * 2
def baseEnd_5625649 : Nat := 320962436720596150679513

theorem tailTrace_5625649 : CollatzResearch.WordTrace tailWord_5625649 prefixEnd_5625649 320962436720596150679513 := by
  unfold tailWord_5625649
  simp only [CollatzResearch.WordTrace]
  refine ⟨205184275596241932202360001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136789517064161288134906667 205184275596241932202360001)
  ·
    refine ⟨153888206697181449151770001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205184275596241932202360001 153888206697181449151770001)
    ·
      refine ⟨115416155022886086863827501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153888206697181449151770001 115416155022886086863827501)
      ·
        refine ⟨43281058133582282573935313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115416155022886086863827501 43281058133582282573935313)
        ·
          refine ⟨32460793600186711930451485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43281058133582282573935313 32460793600186711930451485)
          ·
            refine ⟨12172797600070016973919307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32460793600186711930451485 12172797600070016973919307)
            ·
              refine ⟨18259196400105025460878961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12172797600070016973919307 18259196400105025460878961)
              ·
                refine ⟨13694397300078769095659221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18259196400105025460878961 13694397300078769095659221)
                ·
                  refine ⟨320962436720596150679513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13694397300078769095659221 320962436720596150679513)
                  ·
                    rfl

theorem cell23_5625649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_5625649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625649 prefixEnd_5625649 := by exact prefixLift 5625649
  have htrace : WordTrace (prefixWord ++ tailWord_5625649) baseStart_5625649 baseEnd_5625649 := by
    simpa [prefixWord, tailWord_5625649, baseEnd_5625649] using wordTrace_append hprefix tailTrace_5625649
  have hstable : (prefixWord ++ tailWord_5625649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625649).length < 2 ^ (prefixWord ++ tailWord_5625649).sum := by decide
  have hdescent : baseEnd_5625649 < baseStart_5625649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625677 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5625677 : Nat := 118140960795 + 5625677 * 2 ^ 59
def prefixEnd_5625677 : Nat := 4983230072969 + 3 ^ 40 * 5625677 * 2
def baseEnd_5625677 : Nat := 2888676307943691246565489

theorem tailTrace_5625677 : CollatzResearch.WordTrace tailWord_5625677 prefixEnd_5625677 2888676307943691246565489 := by
  unfold tailWord_5625677
  simp only [CollatzResearch.WordTrace]
  refine ⟨205185296840140492984379285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136790197893426995322919523 205185296840140492984379285)
  ·
    refine ⟨9618060789381585608642779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205185296840140492984379285 9618060789381585608642779)
    ·
      refine ⟨14427091184072378412964169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618060789381585608642779 14427091184072378412964169)
      ·
        refine ⟨10820318388054283809723127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14427091184072378412964169 10820318388054283809723127)
        ·
          refine ⟨16230477582081425714584691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10820318388054283809723127 16230477582081425714584691)
          ·
            refine ⟨24345716373122138571877037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16230477582081425714584691 24345716373122138571877037)
            ·
              refine ⟨9129643639920801964453889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24345716373122138571877037 9129643639920801964453889)
              ·
                refine ⟨6847232729940601473340417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9129643639920801964453889 6847232729940601473340417)
                ·
                  refine ⟨5135424547455451105005313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6847232729940601473340417 5135424547455451105005313)
                  ·
                    refine ⟨3851568410591588328753985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5135424547455451105005313 3851568410591588328753985)
                    ·
                      refine ⟨2888676307943691246565489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851568410591588328753985 2888676307943691246565489)
                      ·
                        rfl

theorem cell23_5625677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5625677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625677 prefixEnd_5625677 := by exact prefixLift 5625677
  have htrace : WordTrace (prefixWord ++ tailWord_5625677) baseStart_5625677 baseEnd_5625677 := by
    simpa [prefixWord, tailWord_5625677, baseEnd_5625677] using wordTrace_append hprefix tailTrace_5625677
  have hstable : (prefixWord ++ tailWord_5625677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625677).length < 2 ^ (prefixWord ++ tailWord_5625677).sum := by decide
  have hdescent : baseEnd_5625677 < baseStart_5625677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625739 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 6]
def baseStart_5625739 : Nat := 118140960795 + 5625739 * 2 ^ 59
def prefixEnd_5625739 : Nat := 4983230072969 + 3 ^ 40 * 5625739 * 2
def baseEnd_5625739 : Nat := 320967571527141111554467

theorem tailTrace_5625739 : CollatzResearch.WordTrace tailWord_5625739 prefixEnd_5625739 320967571527141111554467 := by
  unfold tailWord_5625739
  simp only [CollatzResearch.WordTrace]
  refine ⟨205187558165915877573136271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136791705443943918382090847 205187558165915877573136271)
  ·
    refine ⟨307781337248873816359704407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205187558165915877573136271 307781337248873816359704407)
    ·
      refine ⟨461672005873310724539556611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307781337248873816359704407 461672005873310724539556611)
      ·
        refine ⟨692508008809966086809334917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461672005873310724539556611 692508008809966086809334917)
        ·
          refine ⟨129845251651868641276750297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 692508008809966086809334917 129845251651868641276750297)
          ·
            refine ⟨97383938738901480957562723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129845251651868641276750297 97383938738901480957562723)
            ·
              refine ⟨146075908108352221436344085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97383938738901480957562723 146075908108352221436344085)
              ·
                refine ⟨6847308192579010379828629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146075908108352221436344085 6847308192579010379828629)
                ·
                  refine ⟨320967571527141111554467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6847308192579010379828629 320967571527141111554467)
                  ·
                    rfl

theorem cell23_5625739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 6].length) (baseStart_5625739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625739 prefixEnd_5625739 := by exact prefixLift 5625739
  have htrace : WordTrace (prefixWord ++ tailWord_5625739) baseStart_5625739 baseEnd_5625739 := by
    simpa [prefixWord, tailWord_5625739, baseEnd_5625739] using wordTrace_append hprefix tailTrace_5625739
  have hstable : (prefixWord ++ tailWord_5625739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625739).length < 2 ^ (prefixWord ++ tailWord_5625739).sum := by decide
  have hdescent : baseEnd_5625739 < baseStart_5625739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625799 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 5, 6]
def baseStart_5625799 : Nat := 118140960795 + 5625799 * 2 ^ 59
def prefixEnd_5625799 : Nat := 4983230072969 + 3 ^ 40 * 5625799 * 2
def baseEnd_5625799 : Nat := 962912984194513256413309

theorem tailTrace_5625799 : CollatzResearch.WordTrace tailWord_5625799 prefixEnd_5625799 962912984194513256413309 := by
  unfold tailWord_5625799
  simp only [CollatzResearch.WordTrace]
  refine ⟨205189746545698507820320451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136793164363799005213546967 205189746545698507820320451)
  ·
    refine ⟨307784619818547761730480677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205189746545698507820320451 307784619818547761730480677)
    ·
      refine ⟨57709616215977705324465127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307784619818547761730480677 57709616215977705324465127)
      ·
        refine ⟨86564424323966557986697691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57709616215977705324465127 86564424323966557986697691)
        ·
          refine ⟨129846636485949836980046537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86564424323966557986697691 129846636485949836980046537)
          ·
            refine ⟨97384977364462377735034903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129846636485949836980046537 97384977364462377735034903)
            ·
              refine ⟨146077466046693566602552355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97384977364462377735034903 146077466046693566602552355)
              ·
                refine ⟨219116199070040349903828533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146077466046693566602552355 219116199070040349903828533)
                ·
                  refine ⟨20542143662816282803483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 219116199070040349903828533 20542143662816282803483925)
                  ·
                    refine ⟨962912984194513256413309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20542143662816282803483925 962912984194513256413309)
                    ·
                      rfl

theorem cell23_5625799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 5, 6].length) (baseStart_5625799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625799 prefixEnd_5625799 := by exact prefixLift 5625799
  have htrace : WordTrace (prefixWord ++ tailWord_5625799) baseStart_5625799 baseEnd_5625799 := by
    simpa [prefixWord, tailWord_5625799, baseEnd_5625799] using wordTrace_append hprefix tailTrace_5625799
  have hstable : (prefixWord ++ tailWord_5625799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625799).length < 2 ^ (prefixWord ++ tailWord_5625799).sum := by decide
  have hdescent : baseEnd_5625799 < baseStart_5625799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625806 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4]
def baseStart_5625806 : Nat := 118140960795 + 5625806 * 2 ^ 59
def prefixEnd_5625806 : Nat := 4983230072969 + 3 ^ 40 * 5625806 * 2
def baseEnd_5625806 : Nat := 2888742546948121241852395

theorem tailTrace_5625806 : CollatzResearch.WordTrace tailWord_5625806 prefixEnd_5625806 2888742546948121241852395 := by
  unfold tailWord_5625806
  simp only [CollatzResearch.WordTrace]
  refine ⟨25648750232084143501978159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136793334571115432010550181 25648750232084143501978159)
  ·
    refine ⟨38473125348126215252967239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25648750232084143501978159 38473125348126215252967239)
    ·
      refine ⟨57709688022189322879450859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38473125348126215252967239 57709688022189322879450859)
      ·
        refine ⟨86564532033283984319176289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57709688022189322879450859 86564532033283984319176289)
        ·
          refine ⟨64923399024962988239382217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86564532033283984319176289 64923399024962988239382217)
          ·
            refine ⟨48692549268722241179536663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64923399024962988239382217 48692549268722241179536663)
            ·
              refine ⟨73038823903083361769304995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48692549268722241179536663 73038823903083361769304995)
              ·
                refine ⟨109558235854625042653957493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73038823903083361769304995 109558235854625042653957493)
                ·
                  refine ⟨10271084611371097748808515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109558235854625042653957493 10271084611371097748808515)
                  ·
                    refine ⟨15406626917056646623212773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10271084611371097748808515 15406626917056646623212773)
                    ·
                      refine ⟨2888742546948121241852395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15406626917056646623212773 2888742546948121241852395)
                      ·
                        rfl

theorem cell23_5625806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_5625806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625806 prefixEnd_5625806 := by exact prefixLift 5625806
  have htrace : WordTrace (prefixWord ++ tailWord_5625806) baseStart_5625806 baseEnd_5625806 := by
    simpa [prefixWord, tailWord_5625806, baseEnd_5625806] using wordTrace_append hprefix tailTrace_5625806
  have hstable : (prefixWord ++ tailWord_5625806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625806).length < 2 ^ (prefixWord ++ tailWord_5625806).sum := by decide
  have hdescent : baseEnd_5625806 < baseStart_5625806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625816 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_5625816 : Nat := 118140960795 + 5625816 * 2 ^ 59
def prefixEnd_5625816 : Nat := 4983230072969 + 3 ^ 40 * 5625816 * 2
def baseEnd_5625816 : Nat := 962915893918222067575783

theorem tailTrace_5625816 : CollatzResearch.WordTrace tailWord_5625816 prefixEnd_5625816 962915893918222067575783 := by
  unfold tailWord_5625816
  simp only [CollatzResearch.WordTrace]
  refine ⟨102595183293318459861844651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136793577724424613149126201 102595183293318459861844651)
  ·
    refine ⟨153892774939977689792766977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102595183293318459861844651 153892774939977689792766977)
    ·
      refine ⟨115419581204983267344575233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153892774939977689792766977 115419581204983267344575233)
      ·
        refine ⟨86564685903737450508431425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115419581204983267344575233 86564685903737450508431425)
        ·
          refine ⟨64923514427803087881323569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86564685903737450508431425 64923514427803087881323569)
          ·
            refine ⟨48692635820852315910992677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64923514427803087881323569 48692635820852315910992677)
            ·
              refine ⟨9129869216409809233311127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48692635820852315910992677 9129869216409809233311127)
              ·
                refine ⟨13694803824614713849966691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9129869216409809233311127 13694803824614713849966691)
                ·
                  refine ⟨20542205736922070774950037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13694803824614713849966691 20542205736922070774950037)
                  ·
                    refine ⟨962915893918222067575783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20542205736922070774950037 962915893918222067575783)
                    ·
                      rfl

theorem cell23_5625816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_5625816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625816 prefixEnd_5625816 := by exact prefixLift 5625816
  have htrace : WordTrace (prefixWord ++ tailWord_5625816) baseStart_5625816 baseEnd_5625816 := by
    simpa [prefixWord, tailWord_5625816, baseEnd_5625816] using wordTrace_append hprefix tailTrace_5625816
  have hstable : (prefixWord ++ tailWord_5625816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625816).length < 2 ^ (prefixWord ++ tailWord_5625816).sum := by decide
  have hdescent : baseEnd_5625816 < baseStart_5625816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625857 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 1, 2, 2]
def baseStart_5625857 : Nat := 118140960795 + 5625857 * 2 ^ 59
def prefixEnd_5625857 : Nat := 4983230072969 + 3 ^ 40 * 5625857 * 2
def baseEnd_5625857 : Nat := 2888768734461500542314661

theorem tailTrace_5625857 : CollatzResearch.WordTrace tailWord_5625857 prefixEnd_5625857 2888768734461500542314661 := by
  unfold tailWord_5625857
  simp only [CollatzResearch.WordTrace]
  refine ⟨205191861979488383725931825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136794574652992255817287883 205191861979488383725931825)
  ·
    refine ⟨153893896484616287794448869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205191861979488383725931825 153893896484616287794448869)
    ·
      refine ⟨28855105590865553961459163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153893896484616287794448869 28855105590865553961459163)
      ·
        refine ⟨43282658386298330942188745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28855105590865553961459163 43282658386298330942188745)
        ·
          refine ⟨32461993789723748206641559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43282658386298330942188745 32461993789723748206641559)
          ·
            refine ⟨48692990684585622309962339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32461993789723748206641559 48692990684585622309962339)
            ·
              refine ⟨73039486026878433464943509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48692990684585622309962339 73039486026878433464943509)
              ·
                refine ⟨3423725907509926568669227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73039486026878433464943509 3423725907509926568669227)
                ·
                  refine ⟨5135588861264889853003841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423725907509926568669227 5135588861264889853003841)
                  ·
                    refine ⟨3851691645948667389752881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5135588861264889853003841 3851691645948667389752881)
                    ·
                      refine ⟨2888768734461500542314661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851691645948667389752881 2888768734461500542314661)
                      ·
                        rfl

theorem cell23_5625857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_5625857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625857 prefixEnd_5625857 := by exact prefixLift 5625857
  have htrace : WordTrace (prefixWord ++ tailWord_5625857) baseStart_5625857 baseEnd_5625857 := by
    simpa [prefixWord, tailWord_5625857, baseEnd_5625857] using wordTrace_append hprefix tailTrace_5625857
  have hstable : (prefixWord ++ tailWord_5625857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625857).length < 2 ^ (prefixWord ++ tailWord_5625857).sum := by decide
  have hdescent : baseEnd_5625857 < baseStart_5625857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625859 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 1, 9]
def baseStart_5625859 : Nat := 118140960795 + 5625859 * 2 ^ 59
def prefixEnd_5625859 : Nat := 4983230072969 + 3 ^ 40 * 5625859 * 2
def baseEnd_5625859 : Nat := 962923253807603178163217

theorem tailTrace_5625859 : CollatzResearch.WordTrace tailWord_5625859 prefixEnd_5625859 962923253807603178163217 := by
  unfold tailWord_5625859
  simp only [CollatzResearch.WordTrace]
  refine ⟨205191934925481138067504631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136794623283654092045003087 205191934925481138067504631)
  ·
    refine ⟨307787902388221707101256947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205191934925481138067504631 307787902388221707101256947)
    ·
      refine ⟨461681853582332560651885421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307787902388221707101256947 461681853582332560651885421)
      ·
        refine ⟨173130695093374710244457033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461681853582332560651885421 173130695093374710244457033)
        ·
          refine ⟨129848021320031032683342775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173130695093374710244457033 129848021320031032683342775)
          ·
            refine ⟨194772031980046549025014163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129848021320031032683342775 194772031980046549025014163)
            ·
              refine ⟨292158047970069823537521245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194772031980046549025014163 292158047970069823537521245)
              ·
                refine ⟨109559267988776183826570467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292158047970069823537521245 109559267988776183826570467)
                ·
                  refine ⟨164338901983164275739855701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109559267988776183826570467 164338901983164275739855701)
                  ·
                    refine ⟨962923253807603178163217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164338901983164275739855701 962923253807603178163217)
                    ·
                      rfl

theorem cell23_5625859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_5625859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625859 prefixEnd_5625859 := by exact prefixLift 5625859
  have htrace : WordTrace (prefixWord ++ tailWord_5625859) baseStart_5625859 baseEnd_5625859 := by
    simpa [prefixWord, tailWord_5625859, baseEnd_5625859] using wordTrace_append hprefix tailTrace_5625859
  have hstable : (prefixWord ++ tailWord_5625859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625859).length < 2 ^ (prefixWord ++ tailWord_5625859).sum := by decide
  have hdescent : baseEnd_5625859 < baseStart_5625859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625860 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_5625860 : Nat := 118140960795 + 5625860 * 2 ^ 59
def prefixEnd_5625860 : Nat := 4983230072969 + 3 ^ 40 * 5625860 * 2
def baseEnd_5625860 : Nat := 2888770274903464030577147

theorem tailTrace_5625860 : CollatzResearch.WordTrace tailWord_5625860 prefixEnd_5625860 2888770274903464030577147 := by
  unfold tailWord_5625860
  simp only [CollatzResearch.WordTrace]
  refine ⟨102595985699238757619145517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136794647598985010158860689 102595985699238757619145517)
  ·
    refine ⟨38473494637214534107179569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102595985699238757619145517 38473494637214534107179569)
    ·
      refine ⟨28855120977910900580384677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38473494637214534107179569 28855120977910900580384677)
      ·
        refine ⟨5410335183358293858822127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28855120977910900580384677 5410335183358293858822127)
        ·
          refine ⟨8115502775037440788233191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410335183358293858822127 8115502775037440788233191)
          ·
            refine ⟨12173254162556161182349787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115502775037440788233191 12173254162556161182349787)
            ·
              refine ⟨18259881243834241773524681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173254162556161182349787 18259881243834241773524681)
              ·
                refine ⟨13694910932875681330143511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18259881243834241773524681 13694910932875681330143511)
                ·
                  refine ⟨20542366399313521995215267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13694910932875681330143511 20542366399313521995215267)
                  ·
                    refine ⟨30813549598970282992822901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20542366399313521995215267 30813549598970282992822901)
                    ·
                      refine ⟨2888770274903464030577147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30813549598970282992822901 2888770274903464030577147)
                      ·
                        rfl

theorem cell23_5625860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_5625860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625860 prefixEnd_5625860 := by exact prefixLift 5625860
  have htrace : WordTrace (prefixWord ++ tailWord_5625860) baseStart_5625860 baseEnd_5625860 := by
    simpa [prefixWord, tailWord_5625860, baseEnd_5625860] using wordTrace_append hprefix tailTrace_5625860
  have hstable : (prefixWord ++ tailWord_5625860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625860).length < 2 ^ (prefixWord ++ tailWord_5625860).sum := by decide
  have hdescent : baseEnd_5625860 < baseStart_5625860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625908 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_5625908 : Nat := 118140960795 + 5625908 * 2 ^ 59
def prefixEnd_5625908 : Nat := 4983230072969 + 3 ^ 40 * 5625908 * 2
def baseEnd_5625908 : Nat := 2888794921974879842776927

theorem tailTrace_5625908 : CollatzResearch.WordTrace tailWord_5625908 prefixEnd_5625908 2888794921974879842776927 := by
  unfold tailWord_5625908
  simp only [CollatzResearch.WordTrace]
  refine ⟨102596861051151809718019189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136795814734869079624025585 102596861051151809718019189)
  ·
    refine ⟨9618455723545482161064299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102596861051151809718019189 9618455723545482161064299)
    ·
      refine ⟨14427683585318223241596449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618455723545482161064299 14427683585318223241596449)
      ·
        refine ⟨10820762688988667431197337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14427683585318223241596449 10820762688988667431197337)
        ·
          refine ⟨8115572016741500573398003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10820762688988667431197337 8115572016741500573398003)
          ·
            refine ⟨12173358025112250860097005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115572016741500573398003 12173358025112250860097005)
            ·
              refine ⟨4565009259417094072536377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12173358025112250860097005 4565009259417094072536377)
              ·
                refine ⟨3423756944562820554402283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565009259417094072536377 3423756944562820554402283)
                ·
                  refine ⟨5135635416844230831603425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423756944562820554402283 5135635416844230831603425)
                  ·
                    refine ⟨3851726562633173123702569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5135635416844230831603425 3851726562633173123702569)
                    ·
                      refine ⟨2888794921974879842776927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851726562633173123702569 2888794921974879842776927)
                      ·
                        rfl

theorem cell23_5625908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_5625908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625908 prefixEnd_5625908 := by exact prefixLift 5625908
  have htrace : WordTrace (prefixWord ++ tailWord_5625908) baseStart_5625908 baseEnd_5625908 := by
    simpa [prefixWord, tailWord_5625908, baseEnd_5625908] using wordTrace_append hprefix tailTrace_5625908
  have hstable : (prefixWord ++ tailWord_5625908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625908).length < 2 ^ (prefixWord ++ tailWord_5625908).sum := by decide
  have hdescent : baseEnd_5625908 < baseStart_5625908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625916 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5625916 : Nat := 118140960795 + 5625916 * 2 ^ 59
def prefixEnd_5625916 : Nat := 4983230072969 + 3 ^ 40 * 5625916 * 2
def baseEnd_5625916 : Nat := 2888799029820115811476889

theorem tailTrace_5625916 : CollatzResearch.WordTrace tailWord_5625916 prefixEnd_5625916 2888799029820115811476889 := by
  unfold tailWord_5625916
  simp only [CollatzResearch.WordTrace]
  refine ⟨102597006943137318401164801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136796009257516424534886401 102597006943137318401164801)
  ·
    refine ⟨76947755207352988800873601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102597006943137318401164801 76947755207352988800873601)
    ·
      refine ⟨57710816405514741600655201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76947755207352988800873601 57710816405514741600655201)
      ·
        refine ⟨43283112304136056200491401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57710816405514741600655201 43283112304136056200491401)
        ·
          refine ⟨32462334228102042150368551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43283112304136056200491401 32462334228102042150368551)
          ·
            refine ⟨48693501342153063225552827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32462334228102042150368551 48693501342153063225552827)
            ·
              refine ⟨73040252013229594838329241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48693501342153063225552827 73040252013229594838329241)
              ·
                refine ⟨54780189009922196128746931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73040252013229594838329241 54780189009922196128746931)
                ·
                  refine ⟨82170283514883294193120397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54780189009922196128746931 82170283514883294193120397)
                  ·
                    refine ⟨30813856318081235322420149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82170283514883294193120397 30813856318081235322420149)
                    ·
                      refine ⟨2888799029820115811476889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30813856318081235322420149 2888799029820115811476889)
                      ·
                        rfl

theorem cell23_5625916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5625916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625916 prefixEnd_5625916 := by exact prefixLift 5625916
  have htrace : WordTrace (prefixWord ++ tailWord_5625916) baseStart_5625916 baseEnd_5625916 := by
    simpa [prefixWord, tailWord_5625916, baseEnd_5625916] using wordTrace_append hprefix tailTrace_5625916
  have hstable : (prefixWord ++ tailWord_5625916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625916).length < 2 ^ (prefixWord ++ tailWord_5625916).sum := by decide
  have hdescent : baseEnd_5625916 < baseStart_5625916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625933 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_5625933 : Nat := 118140960795 + 5625933 * 2 ^ 59
def prefixEnd_5625933 : Nat := 4983230072969 + 3 ^ 40 * 5625933 * 2
def baseEnd_5625933 : Nat := 2888807758991242244964311

theorem tailTrace_5625933 : CollatzResearch.WordTrace tailWord_5625933 prefixEnd_5625933 2888807758991242244964311 := by
  unfold tailWord_5625933
  simp only [CollatzResearch.WordTrace]
  refine ⟨205194633927213048705698453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136796422618142032470465635 205194633927213048705698453)
  ·
    refine ⟨9618498465338111658079615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 205194633927213048705698453 9618498465338111658079615)
    ·
      refine ⟨14427747698007167487119423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618498465338111658079615 14427747698007167487119423)
      ·
        refine ⟨21641621547010751230679135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14427747698007167487119423 21641621547010751230679135)
        ·
          refine ⟨32462432320516126846018703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21641621547010751230679135 32462432320516126846018703)
          ·
            refine ⟨48693648480774190269028055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32462432320516126846018703 48693648480774190269028055)
            ·
              refine ⟨73040472721161285403542083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48693648480774190269028055 73040472721161285403542083)
              ·
                refine ⟨109560709081741928105313125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73040472721161285403542083 109560709081741928105313125)
                ·
                  refine ⟨20542632952826611519746211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109560709081741928105313125 20542632952826611519746211)
                  ·
                    refine ⟨30813949429239917279619317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20542632952826611519746211 30813949429239917279619317)
                    ·
                      refine ⟨2888807758991242244964311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30813949429239917279619317 2888807758991242244964311)
                      ·
                        rfl

theorem cell23_5625933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_5625933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625933 prefixEnd_5625933 := by exact prefixLift 5625933
  have htrace : WordTrace (prefixWord ++ tailWord_5625933) baseStart_5625933 baseEnd_5625933 := by
    simpa [prefixWord, tailWord_5625933, baseEnd_5625933] using wordTrace_append hprefix tailTrace_5625933
  have hstable : (prefixWord ++ tailWord_5625933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625933).length < 2 ^ (prefixWord ++ tailWord_5625933).sum := by decide
  have hdescent : baseEnd_5625933 < baseStart_5625933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625953 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 5]
def baseStart_5625953 : Nat := 118140960795 + 5625953 * 2 ^ 59
def prefixEnd_5625953 : Nat := 4983230072969 + 3 ^ 40 * 5625953 * 2
def baseEnd_5625953 : Nat := 320979780956036907412691

theorem tailTrace_5625953 : CollatzResearch.WordTrace tailWord_5625953 prefixEnd_5625953 320979780956036907412691 := by
  unfold tailWord_5625953
  simp only [CollatzResearch.WordTrace]
  refine ⟨205195363387140592121426513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136796908924760394747617675 205195363387140592121426513)
  ·
    refine ⟨153896522540355444091069885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205195363387140592121426513 153896522540355444091069885)
    ·
      refine ⟨57711195952633291534151207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153896522540355444091069885 57711195952633291534151207)
      ·
        refine ⟨86566793928949937301226811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57711195952633291534151207 86566793928949937301226811)
        ·
          refine ⟨129850190893424905951840217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86566793928949937301226811 129850190893424905951840217)
          ·
            refine ⟨97387643170068679463880163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129850190893424905951840217 97387643170068679463880163)
            ·
              refine ⟨146081464755103019195820245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97387643170068679463880163 146081464755103019195820245)
              ·
                refine ⟨3423784330197727012402037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146081464755103019195820245 3423784330197727012402037)
                ·
                  refine ⟨320979780956036907412691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423784330197727012402037 320979780956036907412691)
                  ·
                    rfl

theorem cell23_5625953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 5].length) (baseStart_5625953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625953 prefixEnd_5625953 := by exact prefixLift 5625953
  have htrace : WordTrace (prefixWord ++ tailWord_5625953) baseStart_5625953 baseEnd_5625953 := by
    simpa [prefixWord, tailWord_5625953, baseEnd_5625953] using wordTrace_append hprefix tailTrace_5625953
  have hstable : (prefixWord ++ tailWord_5625953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625953).length < 2 ^ (prefixWord ++ tailWord_5625953).sum := by decide
  have hdescent : baseEnd_5625953 < baseStart_5625953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5625970 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_5625970 : Nat := 118140960795 + 5625970 * 2 ^ 59
def prefixEnd_5625970 : Nat := 4983230072969 + 3 ^ 40 * 5625970 * 2
def baseEnd_5625970 : Nat := 320980750863939844466849

theorem tailTrace_5625970 : CollatzResearch.WordTrace tailWord_5625970 prefixEnd_5625970 320980750863939844466849 := by
  unfold tailWord_5625970
  simp only [CollatzResearch.WordTrace]
  refine ⟨51298995857019751006198841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136797322285386002683196909 51298995857019751006198841)
  ·
    refine ⟨38474246892764813254649131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51298995857019751006198841 38474246892764813254649131)
    ·
      refine ⟨57711370339147219881973697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38474246892764813254649131 57711370339147219881973697)
      ·
        refine ⟨43283527754360414911480273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57711370339147219881973697 43283527754360414911480273)
        ·
          refine ⟨32462645815770311183610205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43283527754360414911480273 32462645815770311183610205)
          ·
            refine ⟨12173492180913866693853827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32462645815770311183610205 12173492180913866693853827)
            ·
              refine ⟨18260238271370800040780741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173492180913866693853827 18260238271370800040780741)
              ·
                refine ⟨3423794675882025007646389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18260238271370800040780741 3423794675882025007646389)
                ·
                  refine ⟨320980750863939844466849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423794675882025007646389 320980750863939844466849)
                  ·
                    rfl

theorem cell23_5625970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_5625970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5625970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5625970 prefixEnd_5625970 := by exact prefixLift 5625970
  have htrace : WordTrace (prefixWord ++ tailWord_5625970) baseStart_5625970 baseEnd_5625970 := by
    simpa [prefixWord, tailWord_5625970, baseEnd_5625970] using wordTrace_append hprefix tailTrace_5625970
  have hstable : (prefixWord ++ tailWord_5625970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5625970).length < 2 ^ (prefixWord ++ tailWord_5625970).sum := by decide
  have hdescent : baseEnd_5625970 < baseStart_5625970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5625970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626003 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 6, 2]
def baseStart_5626003 : Nat := 118140960795 + 5626003 * 2 ^ 59
def prefixEnd_5626003 : Nat := 4983230072969 + 3 ^ 40 * 5626003 * 2
def baseEnd_5626003 : Nat := 2888843702637056971088989

theorem tailTrace_5626003 : CollatzResearch.WordTrace tailWord_5626003 prefixEnd_5626003 2888843702637056971088989 := by
  unfold tailWord_5626003
  simp only [CollatzResearch.WordTrace]
  refine ⟨205197187036959450660746663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136798124691306300440497775 205197187036959450660746663)
  ·
    refine ⟨307795780555439175991119995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205197187036959450660746663 307795780555439175991119995)
    ·
      refine ⟨461693670833158763986679993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307795780555439175991119995 461693670833158763986679993)
      ·
        refine ⟨346270253124869072990009995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461693670833158763986679993 346270253124869072990009995)
        ·
          refine ⟨519405379687303609485014993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346270253124869072990009995 519405379687303609485014993)
          ·
            refine ⟨389554034765477707113761245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519405379687303609485014993 389554034765477707113761245)
            ·
              refine ⟨146082763037054140167660467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389554034765477707113761245 146082763037054140167660467)
              ·
                refine ⟨219124144555581210251490701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146082763037054140167660467 219124144555581210251490701)
                ·
                  refine ⟨82171554208342953844309013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219124144555581210251490701 82171554208342953844309013)
                  ·
                    refine ⟨3851791603516075961451985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82171554208342953844309013 3851791603516075961451985)
                    ·
                      refine ⟨2888843702637056971088989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851791603516075961451985 2888843702637056971088989)
                      ·
                        rfl

theorem cell23_5626003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 6, 2].length) (baseStart_5626003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626003 prefixEnd_5626003 := by exact prefixLift 5626003
  have htrace : WordTrace (prefixWord ++ tailWord_5626003) baseStart_5626003 baseEnd_5626003 := by
    simpa [prefixWord, tailWord_5626003, baseEnd_5626003] using wordTrace_append hprefix tailTrace_5626003
  have hstable : (prefixWord ++ tailWord_5626003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626003).length < 2 ^ (prefixWord ++ tailWord_5626003).sum := by decide
  have hdescent : baseEnd_5626003 < baseStart_5626003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626004 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 5]
def baseStart_5626004 : Nat := 118140960795 + 5626004 * 2 ^ 59
def prefixEnd_5626004 : Nat := 4983230072969 + 3 ^ 40 * 5626004 * 2
def baseEnd_5626004 : Nat := 320982690679745718575165

theorem tailTrace_5626004 : CollatzResearch.WordTrace tailWord_5626004 prefixEnd_5626004 320982690679745718575165 := by
  unfold tailWord_5626004
  simp only [CollatzResearch.WordTrace]
  refine ⟨102598611754977913915766533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136798149006637218554355377 102598611754977913915766533)
  ·
    refine ⟨19237239704058358859206225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102598611754977913915766533 19237239704058358859206225)
    ·
      refine ⟨14427929778043769144404669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19237239704058358859206225 14427929778043769144404669)
      ·
        refine ⟨5410473666766413429151751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14427929778043769144404669 5410473666766413429151751)
        ·
          refine ⟨8115710500149620143727627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410473666766413429151751 8115710500149620143727627)
          ·
            refine ⟨12173565750224430215591441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8115710500149620143727627 12173565750224430215591441)
            ·
              refine ⟨9130174312668322661693581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12173565750224430215591441 9130174312668322661693581)
              ·
                refine ⟨3423815367250620998135093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9130174312668322661693581 3423815367250620998135093)
                ·
                  refine ⟨320982690679745718575165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3423815367250620998135093 320982690679745718575165)
                  ·
                    rfl

theorem cell23_5626004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_5626004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626004 prefixEnd_5626004 := by exact prefixLift 5626004
  have htrace : WordTrace (prefixWord ++ tailWord_5626004) baseStart_5626004 baseEnd_5626004 := by
    simpa [prefixWord, tailWord_5626004, baseEnd_5626004] using wordTrace_append hprefix tailTrace_5626004
  have hstable : (prefixWord ++ tailWord_5626004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626004).length < 2 ^ (prefixWord ++ tailWord_5626004).sum := by decide
  have hdescent : baseEnd_5626004 < baseStart_5626004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626114 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_5626114 : Nat := 118140960795 + 5626114 * 2 ^ 59
def prefixEnd_5626114 : Nat := 4983230072969 + 3 ^ 40 * 5626114 * 2
def baseEnd_5626114 : Nat := 2888900698989706036800979

theorem tailTrace_5626114 : CollatzResearch.WordTrace tailWord_5626114 prefixEnd_5626114 2888900698989706036800979 := by
  unfold tailWord_5626114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51300308884889329154509349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136800823693038211078691597 51300308884889329154509349)
  ·
    refine ⟨9618807915916749216470503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51300308884889329154509349 9618807915916749216470503)
    ·
      refine ⟨14428211873875123824705755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618807915916749216470503 14428211873875123824705755)
      ·
        refine ⟨21642317810812685737058633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14428211873875123824705755 21642317810812685737058633)
        ·
          refine ⟨16231738358109514302793975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21642317810812685737058633 16231738358109514302793975)
          ·
            refine ⟨24347607537164271454190963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16231738358109514302793975 24347607537164271454190963)
            ·
              refine ⟨36521411305746407181286445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24347607537164271454190963 36521411305746407181286445)
              ·
                refine ⟨13695529239654902692982417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36521411305746407181286445 13695529239654902692982417)
                ·
                  refine ⟨10271646929741177019736813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13695529239654902692982417 10271646929741177019736813)
                  ·
                    refine ⟨3851867598652941382401305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10271646929741177019736813 3851867598652941382401305)
                    ·
                      refine ⟨2888900698989706036800979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851867598652941382401305 2888900698989706036800979)
                      ·
                        rfl

theorem cell23_5626114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_5626114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626114 prefixEnd_5626114 := by exact prefixLift 5626114
  have htrace : WordTrace (prefixWord ++ tailWord_5626114) baseStart_5626114 baseEnd_5626114 := by
    simpa [prefixWord, tailWord_5626114, baseEnd_5626114] using wordTrace_append hprefix tailTrace_5626114
  have hstable : (prefixWord ++ tailWord_5626114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626114).length < 2 ^ (prefixWord ++ tailWord_5626114).sum := by decide
  have hdescent : baseEnd_5626114 < baseStart_5626114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626120 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_5626120 : Nat := 118140960795 + 5626120 * 2 ^ 59
def prefixEnd_5626120 : Nat := 4983230072969 + 3 ^ 40 * 5626120 * 2
def baseEnd_5626120 : Nat := 962967926624544337775317

theorem tailTrace_5626120 : CollatzResearch.WordTrace tailWord_5626120 prefixEnd_5626120 962967926624544337775317 := by
  unfold tailWord_5626120
  simp only [CollatzResearch.WordTrace]
  refine ⟨102600727188767789821377907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136800969585023719761837209 102600727188767789821377907)
  ·
    refine ⟨153901090783151684732066861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102600727188767789821377907 153901090783151684732066861)
    ·
      refine ⟨57712909043681881774525073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153901090783151684732066861 57712909043681881774525073)
      ·
        refine ⟨43284681782761411330893805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57712909043681881774525073 43284681782761411330893805)
        ·
          refine ⟨16231755668535529249085177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43284681782761411330893805 16231755668535529249085177)
          ·
            refine ⟨12173816751401646936813883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16231755668535529249085177 12173816751401646936813883)
            ·
              refine ⟨18260725127102470405220825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12173816751401646936813883 18260725127102470405220825)
              ·
                refine ⟨13695543845326852803915619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18260725127102470405220825 13695543845326852803915619)
                ·
                  refine ⟨20543315767990279205873429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13695543845326852803915619 20543315767990279205873429)
                  ·
                    refine ⟨962967926624544337775317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20543315767990279205873429 962967926624544337775317)
                    ·
                      rfl

theorem cell23_5626120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_5626120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626120 prefixEnd_5626120 := by exact prefixLift 5626120
  have htrace : WordTrace (prefixWord ++ tailWord_5626120) baseStart_5626120 baseEnd_5626120 := by
    simpa [prefixWord, tailWord_5626120, baseEnd_5626120] using wordTrace_append hprefix tailTrace_5626120
  have hstable : (prefixWord ++ tailWord_5626120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626120).length < 2 ^ (prefixWord ++ tailWord_5626120).sum := by decide
  have hdescent : baseEnd_5626120 < baseStart_5626120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626138 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_5626138 : Nat := 118140960795 + 5626138 * 2 ^ 59
def prefixEnd_5626138 : Nat := 4983230072969 + 3 ^ 40 * 5626138 * 2
def baseEnd_5626138 : Nat := 2888913022525413942900869

theorem tailTrace_5626138 : CollatzResearch.WordTrace tailWord_5626138 prefixEnd_5626138 2888913022525413942900869 := by
  unfold tailWord_5626138
  simp only [CollatzResearch.WordTrace]
  refine ⟨51300527722867592179227767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136801407260980245811274045 51300527722867592179227767)
  ·
    refine ⟨76950791584301388268841651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51300527722867592179227767 76950791584301388268841651)
    ·
      refine ⟨115426187376452082403262477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76950791584301388268841651 115426187376452082403262477)
      ·
        refine ⟨43284820266169530901223429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115426187376452082403262477 43284820266169530901223429)
        ·
          refine ⟨8115903799906787043979393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43284820266169530901223429 8115903799906787043979393)
          ·
            refine ⟨6086927849930090282984545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8115903799906787043979393 6086927849930090282984545)
            ·
              refine ⟨4565195887447567712238409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6086927849930090282984545 4565195887447567712238409)
              ·
                refine ⟨3423896915585675784178807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565195887447567712238409 3423896915585675784178807)
                ·
                  refine ⟨5135845373378513676268211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3423896915585675784178807 5135845373378513676268211)
                  ·
                    refine ⟨7703768060067770514402317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135845373378513676268211 7703768060067770514402317)
                    ·
                      refine ⟨2888913022525413942900869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7703768060067770514402317 2888913022525413942900869)
                      ·
                        rfl

theorem cell23_5626138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_5626138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626138 prefixEnd_5626138 := by exact prefixLift 5626138
  have htrace : WordTrace (prefixWord ++ tailWord_5626138) baseStart_5626138 baseEnd_5626138 := by
    simpa [prefixWord, tailWord_5626138, baseEnd_5626138] using wordTrace_append hprefix tailTrace_5626138
  have hstable : (prefixWord ++ tailWord_5626138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626138).length < 2 ^ (prefixWord ++ tailWord_5626138).sum := by decide
  have hdescent : baseEnd_5626138 < baseStart_5626138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626163 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 2, 7]
def baseStart_5626163 : Nat := 118140960795 + 5626163 * 2 ^ 59
def prefixEnd_5626163 : Nat := 4983230072969 + 3 ^ 40 * 5626163 * 2
def baseEnd_5626163 : Nat := 962975286513925448362751

theorem tailTrace_5626163 : CollatzResearch.WordTrace tailWord_5626163 prefixEnd_5626163 962975286513925448362751 := by
  unfold tailWord_5626163
  simp only [CollatzResearch.WordTrace]
  refine ⟨205203022716379797986571143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136802015144253198657714095 205203022716379797986571143)
  ·
    refine ⟨307804534074569696979856715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205203022716379797986571143 307804534074569696979856715)
    ·
      refine ⟨461706801111854545469785073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307804534074569696979856715 461706801111854545469785073)
      ·
        refine ⟨346280100833890909102338805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461706801111854545469785073 346280100833890909102338805)
        ·
          refine ⟨32463759453177272728344263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346280100833890909102338805 32463759453177272728344263)
          ·
            refine ⟨48695639179765909092516395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32463759453177272728344263 48695639179765909092516395)
            ·
              refine ⟨73043458769648863638774593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48695639179765909092516395 73043458769648863638774593)
              ·
                refine ⟨54782594077236647729080945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73043458769648863638774593 54782594077236647729080945)
                ·
                  refine ⟨41086945557927485796810709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54782594077236647729080945 41086945557927485796810709)
                  ·
                    refine ⟨962975286513925448362751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41086945557927485796810709 962975286513925448362751)
                    ·
                      rfl

theorem cell23_5626163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_5626163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626163 prefixEnd_5626163 := by exact prefixLift 5626163
  have htrace : WordTrace (prefixWord ++ tailWord_5626163) baseStart_5626163 baseEnd_5626163 := by
    simpa [prefixWord, tailWord_5626163, baseEnd_5626163] using wordTrace_append hprefix tailTrace_5626163
  have hstable : (prefixWord ++ tailWord_5626163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626163).length < 2 ^ (prefixWord ++ tailWord_5626163).sum := by decide
  have hdescent : baseEnd_5626163 < baseStart_5626163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626194 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_5626194 : Nat := 118140960795 + 5626194 * 2 ^ 59
def prefixEnd_5626194 : Nat := 4983230072969 + 3 ^ 40 * 5626194 * 2
def baseEnd_5626194 : Nat := 2888941777442065723800611

theorem tailTrace_5626194 : CollatzResearch.WordTrace tailWord_5626194 prefixEnd_5626194 2888941777442065723800611 := by
  unfold tailWord_5626194
  simp only [CollatzResearch.WordTrace]
  refine ⟨51301038344816872570237409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136802768919511660187299757 51301038344816872570237409)
  ·
    refine ⟨38475778758612654427678057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51301038344816872570237409 38475778758612654427678057)
    ·
      refine ⟨28856834068959490820758543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38475778758612654427678057 28856834068959490820758543)
      ·
        refine ⟨43285251103439236231137815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28856834068959490820758543 43285251103439236231137815)
        ·
          refine ⟨64927876655158854346706723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43285251103439236231137815 64927876655158854346706723)
          ·
            refine ⟨97391814982738281520060085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64927876655158854346706723 97391814982738281520060085)
            ·
              refine ⟨9130482654631713892505633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97391814982738281520060085 9130482654631713892505633)
              ·
                refine ⟨6847861990973785419379225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9130482654631713892505633 6847861990973785419379225)
                ·
                  refine ⟨5135896493230339064534419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6847861990973785419379225 5135896493230339064534419)
                  ·
                    refine ⟨7703844739845508596801629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5135896493230339064534419 7703844739845508596801629)
                    ·
                      refine ⟨2888941777442065723800611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7703844739845508596801629 2888941777442065723800611)
                      ·
                        rfl

theorem cell23_5626194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_5626194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626194 prefixEnd_5626194 := by exact prefixLift 5626194
  have htrace : WordTrace (prefixWord ++ tailWord_5626194) baseStart_5626194 baseEnd_5626194 := by
    simpa [prefixWord, tailWord_5626194, baseEnd_5626194] using wordTrace_append hprefix tailTrace_5626194
  have hstable : (prefixWord ++ tailWord_5626194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626194).length < 2 ^ (prefixWord ++ tailWord_5626194).sum := by decide
  have hdescent : baseEnd_5626194 < baseStart_5626194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626223 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 9]
def baseStart_5626223 : Nat := 118140960795 + 5626223 * 2 ^ 59
def prefixEnd_5626223 : Nat := 4983230072969 + 3 ^ 40 * 5626223 * 2
def baseEnd_5626223 : Nat := 320995185375671790037553

theorem tailTrace_5626223 : CollatzResearch.WordTrace tailWord_5626223 prefixEnd_5626223 320995185375671790037553 := by
  unfold tailWord_5626223
  simp only [CollatzResearch.WordTrace]
  refine ⟨205205211096162428233755323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136803474064108285489170215 205205211096162428233755323)
  ·
    refine ⟨307807816644243642350632985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205205211096162428233755323 307807816644243642350632985)
    ·
      refine ⟨230855862483182731762974739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307807816644243642350632985 230855862483182731762974739)
      ·
        refine ⟨346283793724774097644462109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230855862483182731762974739 346283793724774097644462109)
        ·
          refine ⟨129856422646790286616673291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 346283793724774097644462109 129856422646790286616673291)
          ·
            refine ⟨194784633970185429925009937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129856422646790286616673291 194784633970185429925009937)
            ·
              refine ⟨146088475477639072443757453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194784633970185429925009937 146088475477639072443757453)
              ·
                refine ⟨54783178304114652166409045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146088475477639072443757453 54783178304114652166409045)
                ·
                  refine ⟨320995185375671790037553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54783178304114652166409045 320995185375671790037553)
                  ·
                    rfl

theorem cell23_5626223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 9].length) (baseStart_5626223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626223 prefixEnd_5626223 := by exact prefixLift 5626223
  have htrace : WordTrace (prefixWord ++ tailWord_5626223) baseStart_5626223 baseEnd_5626223 := by
    simpa [prefixWord, tailWord_5626223, baseEnd_5626223] using wordTrace_append hprefix tailTrace_5626223
  have hstable : (prefixWord ++ tailWord_5626223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626223).length < 2 ^ (prefixWord ++ tailWord_5626223).sum := by decide
  have hdescent : baseEnd_5626223 < baseStart_5626223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626307 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 4, 2]
def baseStart_5626307 : Nat := 118140960795 + 5626307 * 2 ^ 59
def prefixEnd_5626307 : Nat := 4983230072969 + 3 ^ 40 * 5626307 * 2
def baseEnd_5626307 : Nat := 2888999800756023781687591

theorem tailTrace_5626307 : CollatzResearch.WordTrace tailWord_5626307 prefixEnd_5626307 2888999800756023781687591 := by
  unfold tailWord_5626307
  simp only [CollatzResearch.WordTrace]
  refine ⟨205208274827858110579813175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136805516551905407053208783 205208274827858110579813175)
  ·
    refine ⟨307812412241787165869719763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205208274827858110579813175 307812412241787165869719763)
    ·
      refine ⟨461718618362680748804579645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307812412241787165869719763 461718618362680748804579645)
      ·
        refine ⟨173144481886005280801717367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461718618362680748804579645 173144481886005280801717367)
        ·
          refine ⟨259716722829007921202576051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173144481886005280801717367 259716722829007921202576051)
          ·
            refine ⟨389575084243511881803864077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259716722829007921202576051 389575084243511881803864077)
            ·
              refine ⟨146090656591316955676449029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 389575084243511881803864077 146090656591316955676449029)
              ·
                refine ⟨27391998110871929189334193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146090656591316955676449029 27391998110871929189334193)
                ·
                  refine ⟨20543998583153946892000645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27391998110871929189334193 20543998583153946892000645)
                  ·
                    refine ⟨3851999734341365042250121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20543998583153946892000645 3851999734341365042250121)
                    ·
                      refine ⟨2888999800756023781687591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3851999734341365042250121 2888999800756023781687591)
                      ·
                        rfl

theorem cell23_5626307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4, 2].length) (baseStart_5626307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626307 prefixEnd_5626307 := by exact prefixLift 5626307
  have htrace : WordTrace (prefixWord ++ tailWord_5626307) baseStart_5626307 baseEnd_5626307 := by
    simpa [prefixWord, tailWord_5626307, baseEnd_5626307] using wordTrace_append hprefix tailTrace_5626307
  have hstable : (prefixWord ++ tailWord_5626307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626307).length < 2 ^ (prefixWord ++ tailWord_5626307).sum := by decide
  have hdescent : baseEnd_5626307 < baseStart_5626307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626308 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 5]
def baseStart_5626308 : Nat := 118140960795 + 5626308 * 2 ^ 59
def prefixEnd_5626308 : Nat := 4983230072969 + 3 ^ 40 * 5626308 * 2
def baseEnd_5626308 : Nat := 321000034915186475308343

theorem tailTrace_5626308 : CollatzResearch.WordTrace tailWord_5626308 prefixEnd_5626308 321000034915186475308343 := by
  unfold tailWord_5626308
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604155650427243875299789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136805540867236325167066385 102604155650427243875299789)
  ·
    refine ⟨38476558368910216453237421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102604155650427243875299789 38476558368910216453237421)
    ·
      refine ⟨14428709388341331169964033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38476558368910216453237421 14428709388341331169964033)
      ·
        refine ⟨10821532041255998377473025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14428709388341331169964033 10821532041255998377473025)
        ·
          refine ⟨8116149030941998783104769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821532041255998377473025 8116149030941998783104769)
          ·
            refine ⟨6087111773206499087328577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116149030941998783104769 6087111773206499087328577)
            ·
              refine ⟨4565333829904874315496433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087111773206499087328577 4565333829904874315496433)
              ·
                refine ⟨3424000372428655736622325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565333829904874315496433 3424000372428655736622325)
                ·
                  refine ⟨321000034915186475308343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3424000372428655736622325 321000034915186475308343)
                  ·
                    rfl

theorem cell23_5626308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_5626308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626308 prefixEnd_5626308 := by exact prefixLift 5626308
  have htrace : WordTrace (prefixWord ++ tailWord_5626308) baseStart_5626308 baseEnd_5626308 := by
    simpa [prefixWord, tailWord_5626308, baseEnd_5626308] using wordTrace_append hprefix tailTrace_5626308
  have hstable : (prefixWord ++ tailWord_5626308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626308).length < 2 ^ (prefixWord ++ tailWord_5626308).sum := by decide
  have hdescent : baseEnd_5626308 < baseStart_5626308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626324 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_5626324 : Nat := 118140960795 + 5626324 * 2 ^ 59
def prefixEnd_5626324 : Nat := 4983230072969 + 3 ^ 40 * 5626324 * 2
def baseEnd_5626324 : Nat := 2889008529927150215175013

theorem tailTrace_5626324 : CollatzResearch.WordTrace tailWord_5626324 prefixEnd_5626324 2889008529927150215175013 := by
  unfold tailWord_5626324
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604447434398261241591013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136805929912531014988788017 102604447434398261241591013)
  ·
    refine ⟨19238333893949673982798315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102604447434398261241591013 19238333893949673982798315)
    ·
      refine ⟨28857500840924510974197473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19238333893949673982798315 28857500840924510974197473)
      ·
        refine ⟨21643125630693383230648105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28857500840924510974197473 21643125630693383230648105)
        ·
          refine ⟨16232344223020037422986079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21643125630693383230648105 16232344223020037422986079)
          ·
            refine ⟨24348516334530056134479119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16232344223020037422986079 24348516334530056134479119)
            ·
              refine ⟨36522774501795084201718679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24348516334530056134479119 36522774501795084201718679)
              ·
                refine ⟨54784161752692626302578019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36522774501795084201718679 54784161752692626302578019)
                ·
                  refine ⟨82176242629038939453867029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54784161752692626302578019 82176242629038939453867029)
                  ·
                    refine ⟨3852011373236200286900017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82176242629038939453867029 3852011373236200286900017)
                    ·
                      refine ⟨2889008529927150215175013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852011373236200286900017 2889008529927150215175013)
                      ·
                        rfl

theorem cell23_5626324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_5626324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626324 prefixEnd_5626324 := by exact prefixLift 5626324
  have htrace : WordTrace (prefixWord ++ tailWord_5626324) baseStart_5626324 baseEnd_5626324 := by
    simpa [prefixWord, tailWord_5626324, baseEnd_5626324] using wordTrace_append hprefix tailTrace_5626324
  have hstable : (prefixWord ++ tailWord_5626324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626324).length < 2 ^ (prefixWord ++ tailWord_5626324).sum := by decide
  have hdescent : baseEnd_5626324 < baseStart_5626324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626338 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_5626338 : Nat := 118140960795 + 5626338 * 2 ^ 59
def prefixEnd_5626338 : Nat := 4983230072969 + 3 ^ 40 * 5626338 * 2
def baseEnd_5626338 : Nat := 963005239552104386799983

theorem tailTrace_5626338 : CollatzResearch.WordTrace tailWord_5626338 prefixEnd_5626338 963005239552104386799983 := by
  unfold tailWord_5626338
  simp only [CollatzResearch.WordTrace]
  refine ⟨51302351372686450718547917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136806270327163868582794445 51302351372686450718547917)
  ·
    refine ⟨19238381764757419019455469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51302351372686450718547917 19238381764757419019455469)
    ·
      refine ⟨7214393161784032132295801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19238381764757419019455469 7214393161784032132295801)
      ·
        refine ⟨5410794871338024099221851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7214393161784032132295801 5410794871338024099221851)
        ·
          refine ⟨8116192307007036148832777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410794871338024099221851 8116192307007036148832777)
          ·
            refine ⟨6087144230255277111624583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116192307007036148832777 6087144230255277111624583)
            ·
              refine ⟨9130716345382915667436875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087144230255277111624583 9130716345382915667436875)
              ·
                refine ⟨13696074518074373501155313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9130716345382915667436875 13696074518074373501155313)
                ·
                  refine ⟨10272055888555780125866485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13696074518074373501155313 10272055888555780125866485)
                  ·
                    refine ⟨963005239552104386799983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10272055888555780125866485 963005239552104386799983)
                    ·
                      rfl

theorem cell23_5626338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_5626338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626338 prefixEnd_5626338 := by exact prefixLift 5626338
  have htrace : WordTrace (prefixWord ++ tailWord_5626338) baseStart_5626338 baseEnd_5626338 := by
    simpa [prefixWord, tailWord_5626338, baseEnd_5626338] using wordTrace_append hprefix tailTrace_5626338
  have hstable : (prefixWord ++ tailWord_5626338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626338).length < 2 ^ (prefixWord ++ tailWord_5626338).sum := by decide
  have hdescent : baseEnd_5626338 < baseStart_5626338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626341 : List Nat := [1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5626341 : Nat := 118140960795 + 5626341 * 2 ^ 59
def prefixEnd_5626341 : Nat := 4983230072969 + 3 ^ 40 * 5626341 * 2
def baseEnd_5626341 : Nat := 2889017259098276648662435

theorem tailTrace_5626341 : CollatzResearch.WordTrace tailWord_5626341 prefixEnd_5626341 2889017259098276648662435 := by
  unfold tailWord_5626341
  simp only [CollatzResearch.WordTrace]
  refine ⟨205209514909734934386550877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136806343273156622924367251 205209514909734934386550877)
  ·
    refine ⟨76953568091150600394956579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205209514909734934386550877 76953568091150600394956579)
    ·
      refine ⟨115430352136725900592434869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76953568091150600394956579 115430352136725900592434869)
      ·
        refine ⟨10821595512818053180540769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115430352136725900592434869 10821595512818053180540769)
        ·
          refine ⟨8116196634613539885405577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10821595512818053180540769 8116196634613539885405577)
          ·
            refine ⟨6087147475960154914054183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116196634613539885405577 6087147475960154914054183)
            ·
              refine ⟨9130721213940232371081275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087147475960154914054183 9130721213940232371081275)
              ·
                refine ⟨13696081820910348556621913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9130721213940232371081275 13696081820910348556621913)
                ·
                  refine ⟨10272061365682761417466435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13696081820910348556621913 10272061365682761417466435)
                  ·
                    refine ⟨15408092048524142126199653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10272061365682761417466435 15408092048524142126199653)
                    ·
                      refine ⟨2889017259098276648662435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15408092048524142126199653 2889017259098276648662435)
                      ·
                        rfl

theorem cell23_5626341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5626341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626341 prefixEnd_5626341 := by exact prefixLift 5626341
  have htrace : WordTrace (prefixWord ++ tailWord_5626341) baseStart_5626341 baseEnd_5626341 := by
    simpa [prefixWord, tailWord_5626341, baseEnd_5626341] using wordTrace_append hprefix tailTrace_5626341
  have hstable : (prefixWord ++ tailWord_5626341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626341).length < 2 ^ (prefixWord ++ tailWord_5626341).sum := by decide
  have hdescent : baseEnd_5626341 < baseStart_5626341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626344 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_5626344 : Nat := 118140960795 + 5626344 * 2 ^ 59
def prefixEnd_5626344 : Nat := 4983230072969 + 3 ^ 40 * 5626344 * 2
def baseEnd_5626344 : Nat := 2889018799540240136924921

theorem tailTrace_5626344 : CollatzResearch.WordTrace tailWord_5626344 prefixEnd_5626344 2889018799540240136924921 := by
  unfold tailWord_5626344
  simp only [CollatzResearch.WordTrace]
  refine ⟨102604812164362032949455043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136806416219149377265940057 102604812164362032949455043)
  ·
    refine ⟨153907218246543049424182565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102604812164362032949455043 153907218246543049424182565)
    ·
      refine ⟨28857603421226821767034231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153907218246543049424182565 28857603421226821767034231)
      ·
        refine ⟨43286405131840232650551347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28857603421226821767034231 43286405131840232650551347)
        ·
          refine ⟨64929607697760348975827021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43286405131840232650551347 64929607697760348975827021)
          ·
            refine ⟨24348602886660130865935133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64929607697760348975827021 24348602886660130865935133)
            ·
              refine ⟨9130726082497549074725675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24348602886660130865935133 9130726082497549074725675)
              ·
                refine ⟨13696089123746323612088513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9130726082497549074725675 13696089123746323612088513)
                ·
                  refine ⟨10272066842809742709066385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13696089123746323612088513 10272066842809742709066385)
                  ·
                    refine ⟨7704050132107307031799789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10272066842809742709066385 7704050132107307031799789)
                    ·
                      refine ⟨2889018799540240136924921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704050132107307031799789 2889018799540240136924921)
                      ·
                        rfl

theorem cell23_5626344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_5626344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626344 prefixEnd_5626344 := by exact prefixLift 5626344
  have htrace : WordTrace (prefixWord ++ tailWord_5626344) baseStart_5626344 baseEnd_5626344 := by
    simpa [prefixWord, tailWord_5626344, baseEnd_5626344] using wordTrace_append hprefix tailTrace_5626344
  have hstable : (prefixWord ++ tailWord_5626344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626344).length < 2 ^ (prefixWord ++ tailWord_5626344).sum := by decide
  have hdescent : baseEnd_5626344 < baseStart_5626344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626417 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_5626417 : Nat := 118140960795 + 5626417 * 2 ^ 59
def prefixEnd_5626417 : Nat := 4983230072969 + 3 ^ 40 * 5626417 * 2
def baseEnd_5626417 : Nat := 2889056283628018351312085

theorem tailTrace_5626417 : CollatzResearch.WordTrace tailWord_5626417 prefixEnd_5626417 2889056283628018351312085 := by
  unfold tailWord_5626417
  simp only [CollatzResearch.WordTrace]
  refine ⟨205212286857459599366317505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136808191238306399577545003 205212286857459599366317505)
  ·
    refine ⟨153909215143094699524738129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205212286857459599366317505 153909215143094699524738129)
    ·
      refine ⟨115431911357321024643553597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153909215143094699524738129 115431911357321024643553597)
      ·
        refine ⟨43286966758995384241332599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115431911357321024643553597 43286966758995384241332599)
        ·
          refine ⟨64930450138493076361998899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43286966758995384241332599 64930450138493076361998899)
          ·
            refine ⟨97395675207739614542998349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64930450138493076361998899 97395675207739614542998349)
            ·
              refine ⟨36523378202902355453624381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97395675207739614542998349 36523378202902355453624381)
              ·
                refine ⟨13696266826088383295109143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36523378202902355453624381 13696266826088383295109143)
                ·
                  refine ⟨20544400239132574942663715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13696266826088383295109143 20544400239132574942663715)
                  ·
                    refine ⟨30816600358698862413995573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20544400239132574942663715 30816600358698862413995573)
                    ·
                      refine ⟨2889056283628018351312085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30816600358698862413995573 2889056283628018351312085)
                      ·
                        rfl

theorem cell23_5626417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_5626417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626417 prefixEnd_5626417 := by exact prefixLift 5626417
  have htrace : WordTrace (prefixWord ++ tailWord_5626417) baseStart_5626417 baseEnd_5626417 := by
    simpa [prefixWord, tailWord_5626417, baseEnd_5626417] using wordTrace_append hprefix tailTrace_5626417
  have hstable : (prefixWord ++ tailWord_5626417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626417).length < 2 ^ (prefixWord ++ tailWord_5626417).sum := by decide
  have hdescent : baseEnd_5626417 < baseStart_5626417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626424 : List Nat := [2, 1, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_5626424 : Nat := 118140960795 + 5626424 * 2 ^ 59
def prefixEnd_5626424 : Nat := 4983230072969 + 3 ^ 40 * 5626424 * 2
def baseEnd_5626424 : Nat := 963019959330866607974851

theorem tailTrace_5626424 : CollatzResearch.WordTrace tailWord_5626424 prefixEnd_5626424 963019959330866607974851 := by
  unfold tailWord_5626424
  simp only [CollatzResearch.WordTrace]
  refine ⟨102606271084217119780911163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136808361445622826374548217 102606271084217119780911163)
  ·
    refine ⟨153909406626325679671366745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102606271084217119780911163 153909406626325679671366745)
    ·
      refine ⟨115432054969744259753525059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153909406626325679671366745 115432054969744259753525059)
      ·
        refine ⟨173148082454616389630287589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115432054969744259753525059 173148082454616389630287589)
        ·
          refine ⟨32465265460240573055678923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173148082454616389630287589 32465265460240573055678923)
          ·
            refine ⟨48697898190360859583518385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32465265460240573055678923 48697898190360859583518385)
            ·
              refine ⟨36523423642770644687638789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48697898190360859583518385 36523423642770644687638789)
              ·
                refine ⟨6848141933019495878932273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36523423642770644687638789 6848141933019495878932273)
                ·
                  refine ⟨5136106449764621909199205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6848141933019495878932273 5136106449764621909199205)
                  ·
                    refine ⟨963019959330866607974851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136106449764621909199205 963019959330866607974851)
                    ·
                      rfl

theorem cell23_5626424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_5626424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626424 prefixEnd_5626424 := by exact prefixLift 5626424
  have htrace : WordTrace (prefixWord ++ tailWord_5626424) baseStart_5626424 baseEnd_5626424 := by
    simpa [prefixWord, tailWord_5626424, baseEnd_5626424] using wordTrace_append hprefix tailTrace_5626424
  have hstable : (prefixWord ++ tailWord_5626424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626424).length < 2 ^ (prefixWord ++ tailWord_5626424).sum := by decide
  have hdescent : baseEnd_5626424 < baseStart_5626424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626437 : List Nat := [1, 3, 1, 1, 1, 6, 2, 8]
def baseStart_5626437 : Nat := 118140960795 + 5626437 * 2 ^ 59
def prefixEnd_5626437 : Nat := 4983230072969 + 3 ^ 40 * 5626437 * 2
def baseEnd_5626437 : Nat := 107002464934855861965259

theorem tailTrace_5626437 : CollatzResearch.WordTrace tailWord_5626437 prefixEnd_5626437 107002464934855861965259 := by
  unfold tailWord_5626437
  simp only [CollatzResearch.WordTrace]
  refine ⟨205213016317387142782045565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136808677544924761854697043 205213016317387142782045565)
  ·
    refine ⟨76954881119020178543267087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205213016317387142782045565 76954881119020178543267087)
    ·
      refine ⟨115432321678530267814900631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76954881119020178543267087 115432321678530267814900631)
      ·
        refine ⟨173148482517795401722350947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115432321678530267814900631 173148482517795401722350947)
        ·
          refine ⟨259722723776693102583526421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173148482517795401722350947 259722723776693102583526421)
          ·
            refine ⟨12174502677032489183602801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 259722723776693102583526421 12174502677032489183602801)
            ·
              refine ⟨9130877007774366887702101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12174502677032489183602801 9130877007774366887702101)
              ·
                refine ⟨107002464934855861965259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9130877007774366887702101 107002464934855861965259)
                ·
                  rfl

theorem cell23_5626437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 8].length) (baseStart_5626437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626437 prefixEnd_5626437 := by exact prefixLift 5626437
  have htrace : WordTrace (prefixWord ++ tailWord_5626437) baseStart_5626437 baseEnd_5626437 := by
    simpa [prefixWord, tailWord_5626437, baseEnd_5626437] using wordTrace_append hprefix tailTrace_5626437
  have hstable : (prefixWord ++ tailWord_5626437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626437).length < 2 ^ (prefixWord ++ tailWord_5626437).sum := by decide
  have hdescent : baseEnd_5626437 < baseStart_5626437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626462 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_5626462 : Nat := 118140960795 + 5626462 * 2 ^ 59
def prefixEnd_5626462 : Nat := 4983230072969 + 3 ^ 40 * 5626462 * 2
def baseEnd_5626462 : Nat := 963026463419156891749793

theorem tailTrace_5626462 : CollatzResearch.WordTrace tailWord_5626462 prefixEnd_5626462 963026463419156891749793 := by
  unfold tailWord_5626462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25651741017787071506463205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136809285428197714701137093 25651741017787071506463205)
  ·
    refine ⟨4809701440835075907461851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25651741017787071506463205 4809701440835075907461851)
    ·
      refine ⟨7214552161252613861192777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4809701440835075907461851 7214552161252613861192777)
      ·
        refine ⟨5410914120939460395894583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7214552161252613861192777 5410914120939460395894583)
        ·
          refine ⟨8116371181409190593841875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5410914120939460395894583 8116371181409190593841875)
          ·
            refine ⟨12174556772113785890762813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116371181409190593841875 12174556772113785890762813)
            ·
              refine ⟨4565458789542669709036055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12174556772113785890762813 4565458789542669709036055)
              ·
                refine ⟨6848188184314004563554083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565458789542669709036055 6848188184314004563554083)
                ·
                  refine ⟨10272282276471006845331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848188184314004563554083 10272282276471006845331125)
                  ·
                    refine ⟨963026463419156891749793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10272282276471006845331125 963026463419156891749793)
                    ·
                      rfl

theorem cell23_5626462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_5626462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626462 prefixEnd_5626462 := by exact prefixLift 5626462
  have htrace : WordTrace (prefixWord ++ tailWord_5626462) baseStart_5626462 baseEnd_5626462 := by
    simpa [prefixWord, tailWord_5626462, baseEnd_5626462] using wordTrace_append hprefix tailTrace_5626462
  have hstable : (prefixWord ++ tailWord_5626462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626462).length < 2 ^ (prefixWord ++ tailWord_5626462).sum := by decide
  have hdescent : baseEnd_5626462 < baseStart_5626462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626464 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_5626464 : Nat := 118140960795 + 5626464 * 2 ^ 59
def prefixEnd_5626464 : Nat := 4983230072969 + 3 ^ 40 * 5626464 * 2
def baseEnd_5626464 : Nat := 2889080417218779667424369

theorem tailTrace_5626464 : CollatzResearch.WordTrace tailWord_5626464 prefixEnd_5626464 2889080417218779667424369 := by
  unfold tailWord_5626464
  simp only [CollatzResearch.WordTrace]
  refine ⟨102607000544144663196639223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136809334058859550928852297 102607000544144663196639223)
  ·
    refine ⟨153910500816216994794958835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102607000544144663196639223 153910500816216994794958835)
    ·
      refine ⟨230865751224325492192438253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153910500816216994794958835 230865751224325492192438253)
      ·
        refine ⟨86574656709122059572164345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230865751224325492192438253 86574656709122059572164345)
        ·
          refine ⟨64930992531841544679123259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86574656709122059572164345 64930992531841544679123259)
          ·
            refine ⟨97396488797762317018684889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64930992531841544679123259 97396488797762317018684889)
            ·
              refine ⟨73047366598321737764013667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97396488797762317018684889 73047366598321737764013667)
              ·
                refine ⟨109571049897482606646020501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73047366598321737764013667 109571049897482606646020501)
                ·
                  refine ⟨5136142963944497186532211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109571049897482606646020501 5136142963944497186532211)
                  ·
                    refine ⟨7704214445916745779798317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5136142963944497186532211 7704214445916745779798317)
                    ·
                      refine ⟨2889080417218779667424369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704214445916745779798317 2889080417218779667424369)
                      ·
                        rfl

theorem cell23_5626464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_5626464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626464 prefixEnd_5626464 := by exact prefixLift 5626464
  have htrace : WordTrace (prefixWord ++ tailWord_5626464) baseStart_5626464 baseEnd_5626464 := by
    simpa [prefixWord, tailWord_5626464, baseEnd_5626464] using wordTrace_append hprefix tailTrace_5626464
  have hstable : (prefixWord ++ tailWord_5626464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626464).length < 2 ^ (prefixWord ++ tailWord_5626464).sum := by decide
  have hdescent : baseEnd_5626464 < baseStart_5626464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626487 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_5626487 : Nat := 118140960795 + 5626487 * 2 ^ 59
def prefixEnd_5626487 : Nat := 4983230072969 + 3 ^ 40 * 5626487 * 2
def baseEnd_5626487 : Nat := 2889092227273833077436763

theorem tailTrace_5626487 : CollatzResearch.WordTrace tailWord_5626487 prefixEnd_5626487 2889092227273833077436763 := by
  unfold tailWord_5626487
  simp only [CollatzResearch.WordTrace]
  refine ⟨205214839967206001321365715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136809893311470667547577143 205214839967206001321365715)
  ·
    refine ⟨307822259950809001982048573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205214839967206001321365715 307822259950809001982048573)
    ·
      refine ⟨115433347481553375743268215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307822259950809001982048573 115433347481553375743268215)
      ·
        refine ⟨173150021222330063614902323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115433347481553375743268215 173150021222330063614902323)
        ·
          refine ⟨259725031833495095422353485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173150021222330063614902323 259725031833495095422353485)
          ·
            refine ⟨97396886937560660783382557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259725031833495095422353485 97396886937560660783382557)
            ·
              refine ⟨36523832601585247793768459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97396886937560660783382557 36523832601585247793768459)
              ·
                refine ⟨54785748902377871690652689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36523832601585247793768459 54785748902377871690652689)
                ·
                  refine ⟨41089311676783403767989517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54785748902377871690652689 41089311676783403767989517)
                  ·
                    refine ⟨15408491878793776412996069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41089311676783403767989517 15408491878793776412996069)
                    ·
                      refine ⟨2889092227273833077436763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15408491878793776412996069 2889092227273833077436763)
                      ·
                        rfl

theorem cell23_5626487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_5626487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626487 prefixEnd_5626487 := by exact prefixLift 5626487
  have htrace : WordTrace (prefixWord ++ tailWord_5626487) baseStart_5626487 baseEnd_5626487 := by
    simpa [prefixWord, tailWord_5626487, baseEnd_5626487] using wordTrace_append hprefix tailTrace_5626487
  have hstable : (prefixWord ++ tailWord_5626487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626487).length < 2 ^ (prefixWord ++ tailWord_5626487).sum := by decide
  have hdescent : baseEnd_5626487 < baseStart_5626487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626507 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_5626507 : Nat := 118140960795 + 5626507 * 2 ^ 59
def prefixEnd_5626507 : Nat := 4983230072969 + 3 ^ 40 * 5626507 * 2
def baseEnd_5626507 : Nat := 2889102496886922999186671

theorem tailTrace_5626507 : CollatzResearch.WordTrace tailWord_5626507 prefixEnd_5626507 2889102496886922999186671 := by
  unfold tailWord_5626507
  simp only [CollatzResearch.WordTrace]
  refine ⟨205215569427133544737093775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136810379618089029824729183 205215569427133544737093775)
  ·
    refine ⟨307823354140700317105640663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205215569427133544737093775 307823354140700317105640663)
    ·
      refine ⟨461735031211050475658460995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307823354140700317105640663 461735031211050475658460995)
      ·
        refine ⟨692602546816575713487691493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461735031211050475658460995 692602546816575713487691493)
        ·
          refine ⟨129862977528107946278942155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 692602546816575713487691493 129862977528107946278942155)
          ·
            refine ⟨194794466292161919418413233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129862977528107946278942155 194794466292161919418413233)
            ·
              refine ⟨146095849719121439563809925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194794466292161919418413233 146095849719121439563809925)
              ·
                refine ⟨27392971822335269918214361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146095849719121439563809925 27392971822335269918214361)
                ·
                  refine ⟨20544728866751452438660771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27392971822335269918214361 20544728866751452438660771)
                  ·
                    refine ⟨30817093300127178657991157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20544728866751452438660771 30817093300127178657991157)
                    ·
                      refine ⟨2889102496886922999186671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30817093300127178657991157 2889102496886922999186671)
                      ·
                        rfl

theorem cell23_5626507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_5626507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626507 prefixEnd_5626507 := by exact prefixLift 5626507
  have htrace : WordTrace (prefixWord ++ tailWord_5626507) baseStart_5626507 baseEnd_5626507 := by
    simpa [prefixWord, tailWord_5626507, baseEnd_5626507] using wordTrace_append hprefix tailTrace_5626507
  have hstable : (prefixWord ++ tailWord_5626507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626507).length < 2 ^ (prefixWord ++ tailWord_5626507).sum := by decide
  have hdescent : baseEnd_5626507 < baseStart_5626507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626521 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 4, 2, 2]
def baseStart_5626521 : Nat := 118140960795 + 5626521 * 2 ^ 59
def prefixEnd_5626521 : Nat := 4983230072969 + 3 ^ 40 * 5626521 * 2
def baseEnd_5626521 : Nat := 2889109685616085944411607

theorem tailTrace_5626521 : CollatzResearch.WordTrace tailWord_5626521 prefixEnd_5626521 2889109685616085944411607 := by
  unfold tailWord_5626521
  simp only [CollatzResearch.WordTrace]
  refine ⟨205216080049082825128103417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136810720032721883418735611 205216080049082825128103417)
  ·
    refine ⟨153912060036812118846077563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205216080049082825128103417 153912060036812118846077563)
    ·
      refine ⟨230868090055218178269116345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153912060036812118846077563 230868090055218178269116345)
      ·
        refine ⟨173151067541413633701837259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230868090055218178269116345 173151067541413633701837259)
        ·
          refine ⟨259726601312120450552755889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173151067541413633701837259 259726601312120450552755889)
          ·
            refine ⟨194794950984090337914566917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259726601312120450552755889 194794950984090337914566917)
            ·
              refine ⟨36524053309516938358981297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194794950984090337914566917 36524053309516938358981297)
              ·
                refine ⟨27393039982137703769235973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36524053309516938358981297 27393039982137703769235973)
                ·
                  refine ⟨5136194996650819456731745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27393039982137703769235973 5136194996650819456731745)
                  ·
                    refine ⟨3852146247488114592548809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5136194996650819456731745 3852146247488114592548809)
                    ·
                      refine ⟨2889109685616085944411607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852146247488114592548809 2889109685616085944411607)
                      ·
                        rfl

theorem cell23_5626521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_5626521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626521 prefixEnd_5626521 := by exact prefixLift 5626521
  have htrace : WordTrace (prefixWord ++ tailWord_5626521) baseStart_5626521 baseEnd_5626521 := by
    simpa [prefixWord, tailWord_5626521, baseEnd_5626521] using wordTrace_append hprefix tailTrace_5626521
  have hstable : (prefixWord ++ tailWord_5626521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626521).length < 2 ^ (prefixWord ++ tailWord_5626521).sum := by decide
  have hdescent : baseEnd_5626521 < baseStart_5626521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626554 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_5626554 : Nat := 118140960795 + 5626554 * 2 ^ 59
def prefixEnd_5626554 : Nat := 4983230072969 + 3 ^ 40 * 5626554 * 2
def baseEnd_5626554 : Nat := 2889126630477684315298955

theorem tailTrace_5626554 : CollatzResearch.WordTrace tailWord_5626554 prefixEnd_5626554 2889126630477684315298955 := by
  unfold tailWord_5626554
  simp only [CollatzResearch.WordTrace]
  refine ⟨51304320914490817941013679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136811522438642181176036477 51304320914490817941013679)
  ·
    refine ⟨76956481371736226911520519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51304320914490817941013679 76956481371736226911520519)
    ·
      refine ⟨115434722057604340367280779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76956481371736226911520519 115434722057604340367280779)
      ·
        refine ⟨173152083086406510550921169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115434722057604340367280779 173152083086406510550921169)
        ·
          refine ⟨129864062314804882913190877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173152083086406510550921169 129864062314804882913190877)
          ·
            refine ⟨48699023368051831092446579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129864062314804882913190877 48699023368051831092446579)
            ·
              refine ⟨73048535052077746638669869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48699023368051831092446579 73048535052077746638669869)
              ·
                refine ⟨27393200644529154989501201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73048535052077746638669869 27393200644529154989501201)
                ·
                  refine ⟨20544900483396866242125901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27393200644529154989501201 20544900483396866242125901)
                  ·
                    refine ⟨7704337681273824840797213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20544900483396866242125901 7704337681273824840797213)
                    ·
                      refine ⟨2889126630477684315298955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704337681273824840797213 2889126630477684315298955)
                      ·
                        rfl

theorem cell23_5626554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_5626554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626554 prefixEnd_5626554 := by exact prefixLift 5626554
  have htrace : WordTrace (prefixWord ++ tailWord_5626554) baseStart_5626554 baseEnd_5626554 := by
    simpa [prefixWord, tailWord_5626554, baseEnd_5626554] using wordTrace_append hprefix tailTrace_5626554
  have hstable : (prefixWord ++ tailWord_5626554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626554).length < 2 ^ (prefixWord ++ tailWord_5626554).sum := by decide
  have hdescent : baseEnd_5626554 < baseStart_5626554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626567 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5626567 : Nat := 118140960795 + 5626567 * 2 ^ 59
def prefixEnd_5626567 : Nat := 4983230072969 + 3 ^ 40 * 5626567 * 2
def baseEnd_5626567 : Nat := 2889133305726192764436395

theorem tailTrace_5626567 : CollatzResearch.WordTrace tailWord_5626567 prefixEnd_5626567 2889133305726192764436395 := by
  unfold tailWord_5626567
  simp only [CollatzResearch.WordTrace]
  refine ⟨205217757806916174984277955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136811838537944116656185303 205217757806916174984277955)
  ·
    refine ⟨307826636710374262476416933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205217757806916174984277955 307826636710374262476416933)
    ·
      refine ⟨57717494383195174214328175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307826636710374262476416933 57717494383195174214328175)
      ·
        refine ⟨86576241574792761321492263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57717494383195174214328175 86576241574792761321492263)
        ·
          refine ⟨129864362362189141982238395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86576241574792761321492263 129864362362189141982238395)
          ·
            refine ⟨194796543543283712973357593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129864362362189141982238395 194796543543283712973357593)
            ·
              refine ⟨146097407657462784730018195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194796543543283712973357593 146097407657462784730018195)
              ·
                refine ⟨219146111486194177095027293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146097407657462784730018195 219146111486194177095027293)
                ·
                  refine ⟨82179791807322816410635235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 219146111486194177095027293 82179791807322816410635235)
                  ·
                    refine ⟨123269687710984224615952853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82179791807322816410635235 123269687710984224615952853)
                    ·
                      refine ⟨2889133305726192764436395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123269687710984224615952853 2889133305726192764436395)
                      ·
                        rfl

theorem cell23_5626567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5626567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626567 prefixEnd_5626567 := by exact prefixLift 5626567
  have htrace : WordTrace (prefixWord ++ tailWord_5626567) baseStart_5626567 baseEnd_5626567 := by
    simpa [prefixWord, tailWord_5626567, baseEnd_5626567] using wordTrace_append hprefix tailTrace_5626567
  have hstable : (prefixWord ++ tailWord_5626567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626567).length < 2 ^ (prefixWord ++ tailWord_5626567).sum := by decide
  have hdescent : baseEnd_5626567 < baseStart_5626567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626574 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_5626574 : Nat := 118140960795 + 5626574 * 2 ^ 59
def prefixEnd_5626574 : Nat := 4983230072969 + 3 ^ 40 * 5626574 * 2
def baseEnd_5626574 : Nat := 963045633363591412349621

theorem tailTrace_5626574 : CollatzResearch.WordTrace tailWord_5626574 prefixEnd_5626574 963045633363591412349621 := by
  unfold tailWord_5626574
  simp only [CollatzResearch.WordTrace]
  refine ⟨25652251639736351897472847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136812008745260543453188517 25652251639736351897472847)
  ·
    refine ⟨38478377459604527846209271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25652251639736351897472847 38478377459604527846209271)
    ·
      refine ⟨57717566189406791769313907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38478377459604527846209271 57717566189406791769313907)
      ·
        refine ⟨86576349284110187653970861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57717566189406791769313907 86576349284110187653970861)
        ·
          refine ⟨32466130981541320370239073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86576349284110187653970861 32466130981541320370239073)
          ·
            refine ⟨24349598236155990277679305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32466130981541320370239073 24349598236155990277679305)
            ·
              refine ⟨18262198677116992708259479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24349598236155990277679305 18262198677116992708259479)
              ·
                refine ⟨27393298015675489062389219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18262198677116992708259479 27393298015675489062389219)
                ·
                  refine ⟨41089947023513233593583829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27393298015675489062389219 41089947023513233593583829)
                  ·
                    refine ⟨963045633363591412349621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41089947023513233593583829 963045633363591412349621)
                    ·
                      rfl

theorem cell23_5626574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_5626574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626574 prefixEnd_5626574 := by exact prefixLift 5626574
  have htrace : WordTrace (prefixWord ++ tailWord_5626574) baseStart_5626574 baseEnd_5626574 := by
    simpa [prefixWord, tailWord_5626574, baseEnd_5626574] using wordTrace_append hprefix tailTrace_5626574
  have hstable : (prefixWord ++ tailWord_5626574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626574).length < 2 ^ (prefixWord ++ tailWord_5626574).sum := by decide
  have hdescent : baseEnd_5626574 < baseStart_5626574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626638 : List Nat := [4, 1, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_5626638 : Nat := 118140960795 + 5626638 * 2 ^ 59
def prefixEnd_5626638 : Nat := 4983230072969 + 3 ^ 40 * 5626638 * 2
def baseEnd_5626638 : Nat := 963056587617553995549523

theorem tailTrace_5626638 : CollatzResearch.WordTrace tailWord_5626638 prefixEnd_5626638 963056587617553995549523 := by
  unfold tailWord_5626638
  simp only [CollatzResearch.WordTrace]
  refine ⟨25652543423707369263764071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136813564926439302740075045 25652543423707369263764071)
  ·
    refine ⟨38478815135561053895646107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25652543423707369263764071 38478815135561053895646107)
    ·
      refine ⟨57718222703341580843469161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38478815135561053895646107 57718222703341580843469161)
      ·
        refine ⟨43288667027506185632601871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57718222703341580843469161 43288667027506185632601871)
        ·
          refine ⟨64933000541259278448902807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43288667027506185632601871 64933000541259278448902807)
          ·
            refine ⟨97399500811888917673354211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64933000541259278448902807 97399500811888917673354211)
            ·
              refine ⟨146099251217833376510031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97399500811888917673354211 146099251217833376510031317)
              ·
                refine ⟨3424201200417969761953859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 146099251217833376510031317 3424201200417969761953859)
                ·
                  refine ⟨5136301800626954642930789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424201200417969761953859 5136301800626954642930789)
                  ·
                    refine ⟨963056587617553995549523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136301800626954642930789 963056587617553995549523)
                    ·
                      rfl

theorem cell23_5626638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_5626638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626638 prefixEnd_5626638 := by exact prefixLift 5626638
  have htrace : WordTrace (prefixWord ++ tailWord_5626638) baseStart_5626638 baseEnd_5626638 := by
    simpa [prefixWord, tailWord_5626638, baseEnd_5626638] using wordTrace_append hprefix tailTrace_5626638
  have hstable : (prefixWord ++ tailWord_5626638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626638).length < 2 ^ (prefixWord ++ tailWord_5626638).sum := by decide
  have hdescent : baseEnd_5626638 < baseStart_5626638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626655 : List Nat := [1, 1, 2, 4, 2, 2, 4, 2, 1, 4]
def baseStart_5626655 : Nat := 118140960795 + 5626655 * 2 ^ 59
def prefixEnd_5626655 : Nat := 4983230072969 + 3 ^ 40 * 5626655 * 2
def baseEnd_5626655 : Nat := 963059497341262806711997

theorem tailTrace_5626655 : CollatzResearch.WordTrace tailWord_5626655 prefixEnd_5626655 963059497341262806711997 := by
  unfold tailWord_5626655
  simp only [CollatzResearch.WordTrace]
  refine ⟨205220967430597366013481419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136813978287064910675654279 205220967430597366013481419)
  ·
    refine ⟨307831451145896049020222129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205220967430597366013481419 307831451145896049020222129)
    ·
      refine ⟨230873588359422036765166597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307831451145896049020222129 230873588359422036765166597)
      ·
        refine ⟨43288797817391631893468737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230873588359422036765166597 43288797817391631893468737)
        ·
          refine ⟨32466598363043723920101553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43288797817391631893468737 32466598363043723920101553)
          ·
            refine ⟨24349948772282792940076165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32466598363043723920101553 24349948772282792940076165)
            ·
              refine ⟨4565615394803023676264281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24349948772282792940076165 4565615394803023676264281)
              ·
                refine ⟨3424211546102267757198211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565615394803023676264281 3424211546102267757198211)
                ·
                  refine ⟨5136317319153401635797317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424211546102267757198211 5136317319153401635797317)
                  ·
                    refine ⟨963059497341262806711997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136317319153401635797317 963059497341262806711997)
                    ·
                      rfl

theorem cell23_5626655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 2, 1, 4].length) (baseStart_5626655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626655 prefixEnd_5626655 := by exact prefixLift 5626655
  have htrace : WordTrace (prefixWord ++ tailWord_5626655) baseStart_5626655 baseEnd_5626655 := by
    simpa [prefixWord, tailWord_5626655, baseEnd_5626655] using wordTrace_append hprefix tailTrace_5626655
  have hstable : (prefixWord ++ tailWord_5626655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626655).length < 2 ^ (prefixWord ++ tailWord_5626655).sum := by decide
  have hdescent : baseEnd_5626655 < baseStart_5626655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626674 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5626674 : Nat := 118140960795 + 5626674 * 2 ^ 59
def prefixEnd_5626674 : Nat := 4983230072969 + 3 ^ 40 * 5626674 * 2
def baseEnd_5626674 : Nat := 2889188248156223845798403

theorem tailTrace_5626674 : CollatzResearch.WordTrace tailWord_5626674 prefixEnd_5626674 2889188248156223845798403 := by
  unfold tailWord_5626674
  simp only [CollatzResearch.WordTrace]
  refine ⟨51305415104382133064605769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136814440278352354838948717 51305415104382133064605769)
  ·
    refine ⟨38479061328286599798454327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51305415104382133064605769 38479061328286599798454327)
    ·
      refine ⟨57718591992429899697681491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38479061328286599798454327 57718591992429899697681491)
      ·
        refine ⟨86577887988644849546522237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57718591992429899697681491 86577887988644849546522237)
        ·
          refine ⟨32466707995741818579945839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86577887988644849546522237 32466707995741818579945839)
          ·
            refine ⟨48700061993612727869918759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32466707995741818579945839 48700061993612727869918759)
            ·
              refine ⟨73050092990419091804878139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48700061993612727869918759 73050092990419091804878139)
              ·
                refine ⟨109575139485628637707317209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73050092990419091804878139 109575139485628637707317209)
                ·
                  refine ⟨82181354614221478280487907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109575139485628637707317209 82181354614221478280487907)
                  ·
                    refine ⟨123272031921332217420731861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82181354614221478280487907 123272031921332217420731861)
                    ·
                      refine ⟨2889188248156223845798403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123272031921332217420731861 2889188248156223845798403)
                      ·
                        rfl

theorem cell23_5626674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5626674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626674 prefixEnd_5626674 := by exact prefixLift 5626674
  have htrace : WordTrace (prefixWord ++ tailWord_5626674) baseStart_5626674 baseEnd_5626674 := by
    simpa [prefixWord, tailWord_5626674, baseEnd_5626674] using wordTrace_append hprefix tailTrace_5626674
  have hstable : (prefixWord ++ tailWord_5626674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626674).length < 2 ^ (prefixWord ++ tailWord_5626674).sum := by decide
  have hdescent : baseEnd_5626674 < baseStart_5626674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626721 : List Nat := [1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_5626721 : Nat := 118140960795 + 5626721 * 2 ^ 59
def prefixEnd_5626721 : Nat := 4983230072969 + 3 ^ 40 * 5626721 * 2
def baseEnd_5626721 : Nat := 2889212381746985161910687

theorem tailTrace_5626721 : CollatzResearch.WordTrace tailWord_5626721 prefixEnd_5626721 2889212381746985161910687 := by
  unfold tailWord_5626721
  simp only [CollatzResearch.WordTrace]
  refine ⟨205223374648358259285384017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136815583098905506190256011 205223374648358259285384017)
  ·
    refine ⟨153917530986268694464038013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205223374648358259285384017 153917530986268694464038013)
    ·
      refine ⟨57719074119850760424014255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153917530986268694464038013 57719074119850760424014255)
      ·
        refine ⟨86578611179776140636021383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57719074119850760424014255 86578611179776140636021383)
        ·
          refine ⟨129867916769664210954032075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86578611179776140636021383 129867916769664210954032075)
          ·
            refine ⟨194801875154496316431048113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129867916769664210954032075 194801875154496316431048113)
            ·
              refine ⟨146101406365872237323286085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194801875154496316431048113 146101406365872237323286085)
              ·
                refine ⟨27394013693601044498116141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 146101406365872237323286085 27394013693601044498116141)
                ·
                  refine ⟨10272755135100391686793553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27394013693601044498116141 10272755135100391686793553)
                  ·
                    refine ⟨7704566351325293765095165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10272755135100391686793553 7704566351325293765095165)
                    ·
                      refine ⟨2889212381746985161910687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704566351325293765095165 2889212381746985161910687)
                      ·
                        rfl

theorem cell23_5626721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_5626721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626721 prefixEnd_5626721 := by exact prefixLift 5626721
  have htrace : WordTrace (prefixWord ++ tailWord_5626721) baseStart_5626721 baseEnd_5626721 := by
    simpa [prefixWord, tailWord_5626721, baseEnd_5626721] using wordTrace_append hprefix tailTrace_5626721
  have hstable : (prefixWord ++ tailWord_5626721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626721).length < 2 ^ (prefixWord ++ tailWord_5626721).sum := by decide
  have hdescent : baseEnd_5626721 < baseStart_5626721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626728 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_5626728 : Nat := 118140960795 + 5626728 * 2 ^ 59
def prefixEnd_5626728 : Nat := 4983230072969 + 3 ^ 40 * 5626728 * 2
def baseEnd_5626728 : Nat := 963071992037188878174385

theorem tailTrace_5626728 : CollatzResearch.WordTrace tailWord_5626728 prefixEnd_5626728 963071992037188878174385 := by
  unfold tailWord_5626728
  simp only [CollatzResearch.WordTrace]
  refine ⟨102611814979666449740444419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136815753306221932987259225 102611814979666449740444419)
  ·
    refine ⟨153917722469499674610666629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102611814979666449740444419 153917722469499674610666629)
    ·
      refine ⟨28859572963031188989499993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153917722469499674610666629 28859572963031188989499993)
      ·
        refine ⟨21644679722273391742124995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28859572963031188989499993 21644679722273391742124995)
        ·
          refine ⟨32467019583410087613187493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644679722273391742124995 32467019583410087613187493)
          ·
            refine ⟨6087566171889391427472655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32467019583410087613187493 6087566171889391427472655)
            ·
              refine ⟨9131349257834087141208983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087566171889391427472655 9131349257834087141208983)
              ·
                refine ⟨13697023886751130711813475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9131349257834087141208983 13697023886751130711813475)
                ·
                  refine ⟨20545535830126696067720213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697023886751130711813475 20545535830126696067720213)
                  ·
                    refine ⟨963071992037188878174385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20545535830126696067720213 963071992037188878174385)
                    ·
                      rfl

theorem cell23_5626728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_5626728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626728 prefixEnd_5626728 := by exact prefixLift 5626728
  have htrace : WordTrace (prefixWord ++ tailWord_5626728) baseStart_5626728 baseEnd_5626728 := by
    simpa [prefixWord, tailWord_5626728, baseEnd_5626728] using wordTrace_append hprefix tailTrace_5626728
  have hstable : (prefixWord ++ tailWord_5626728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626728).length < 2 ^ (prefixWord ++ tailWord_5626728).sum := by decide
  have hdescent : baseEnd_5626728 < baseStart_5626728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626731 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4]
def baseStart_5626731 : Nat := 118140960795 + 5626731 * 2 ^ 59
def prefixEnd_5626731 : Nat := 4983230072969 + 3 ^ 40 * 5626731 * 2
def baseEnd_5626731 : Nat := 2889217516553530122785641

theorem tailTrace_5626731 : CollatzResearch.WordTrace tailWord_5626731 prefixEnd_5626731 2889217516553530122785641 := by
  unfold tailWord_5626731
  simp only [CollatzResearch.WordTrace]
  refine ⟨205223739378322030993248047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136815826252214687328832031 205223739378322030993248047)
  ·
    refine ⟨307835609067483046489872071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205223739378322030993248047 307835609067483046489872071)
    ·
      refine ⟨461753413601224569734808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307835609067483046489872071 461753413601224569734808107)
      ·
        refine ⟨692630120401836854602212161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461753413601224569734808107 692630120401836854602212161)
        ·
          refine ⟨519472590301377640951659121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 692630120401836854602212161 519472590301377640951659121)
          ·
            refine ⟨389604442726033230713744341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519472590301377640951659121 389604442726033230713744341)
            ·
              refine ⟨9131354126391403844853383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 389604442726033230713744341 9131354126391403844853383)
              ·
                refine ⟨13697031189587105767280075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9131354126391403844853383 13697031189587105767280075)
                ·
                  refine ⟨20545546784380658650920113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697031189587105767280075 20545546784380658650920113)
                  ·
                    refine ⟨15409160088285493988190085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20545546784380658650920113 15409160088285493988190085)
                    ·
                      refine ⟨2889217516553530122785641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15409160088285493988190085 2889217516553530122785641)
                      ·
                        rfl

theorem cell23_5626731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 4].length) (baseStart_5626731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626731 prefixEnd_5626731 := by exact prefixLift 5626731
  have htrace : WordTrace (prefixWord ++ tailWord_5626731) baseStart_5626731 baseEnd_5626731 := by
    simpa [prefixWord, tailWord_5626731, baseEnd_5626731] using wordTrace_append hprefix tailTrace_5626731
  have hstable : (prefixWord ++ tailWord_5626731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626731).length < 2 ^ (prefixWord ++ tailWord_5626731).sum := by decide
  have hdescent : baseEnd_5626731 < baseStart_5626731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626738 : List Nat := [3, 2, 1, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_5626738 : Nat := 118140960795 + 5626738 * 2 ^ 59
def prefixEnd_5626738 : Nat := 4983230072969 + 3 ^ 40 * 5626738 * 2
def baseEnd_5626738 : Nat := 2889221110918111595398109

theorem tailTrace_5626738 : CollatzResearch.WordTrace tailWord_5626738 prefixEnd_5626738 2889221110918111595398109 := by
  unfold tailWord_5626738
  simp only [CollatzResearch.WordTrace]
  refine ⟨51305998672324167797188217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136815996459531114125835245 51305998672324167797188217)
  ·
    refine ⟨38479499004243125847891163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51305998672324167797188217 38479499004243125847891163)
    ·
      refine ⟨57719248506364688771836745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38479499004243125847891163 57719248506364688771836745)
      ·
        refine ⟨43289436379773516578877559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57719248506364688771836745 43289436379773516578877559)
        ·
          refine ⟨64934154569660274868316339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43289436379773516578877559 64934154569660274868316339)
          ·
            refine ⟨97401231854490412302474509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64934154569660274868316339 97401231854490412302474509)
            ·
              refine ⟨36525461945433904613427941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97401231854490412302474509 36525461945433904613427941)
              ·
                refine ⟨6848524114768857115017739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36525461945433904613427941 6848524114768857115017739)
                ·
                  refine ⟨10272786172153285672526609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6848524114768857115017739 10272786172153285672526609)
                  ·
                    refine ⟨7704589629114964254394957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10272786172153285672526609 7704589629114964254394957)
                    ·
                      refine ⟨2889221110918111595398109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704589629114964254394957 2889221110918111595398109)
                      ·
                        rfl

theorem cell23_5626738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_5626738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626738 prefixEnd_5626738 := by exact prefixLift 5626738
  have htrace : WordTrace (prefixWord ++ tailWord_5626738) baseStart_5626738 baseEnd_5626738 := by
    simpa [prefixWord, tailWord_5626738, baseEnd_5626738] using wordTrace_append hprefix tailTrace_5626738
  have hstable : (prefixWord ++ tailWord_5626738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626738).length < 2 ^ (prefixWord ++ tailWord_5626738).sum := by decide
  have hdescent : baseEnd_5626738 < baseStart_5626738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626741 : List Nat := [1, 3, 4, 1, 1, 3, 1, 9]
def baseStart_5626741 : Nat := 118140960795 + 5626741 * 2 ^ 59
def prefixEnd_5626741 : Nat := 4983230072969 + 3 ^ 40 * 5626741 * 2
def baseEnd_5626741 : Nat := 107008246346669447542985

theorem tailTrace_5626741 : CollatzResearch.WordTrace tailWord_5626741 prefixEnd_5626741 107008246346669447542985 := by
  unfold tailWord_5626741
  simp only [CollatzResearch.WordTrace]
  refine ⟨205224104108285802701112077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136816069405523868467408051 205224104108285802701112077)
  ·
    refine ⟨76959039040607176012917029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205224104108285802701112077 76959039040607176012917029)
    ·
      refine ⟨14429819820113845502421943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76959039040607176012917029 14429819820113845502421943)
      ·
        refine ⟨21644729730170768253632915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14429819820113845502421943 21644729730170768253632915)
        ·
          refine ⟨32467094595256152380449373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21644729730170768253632915 32467094595256152380449373)
          ·
            refine ⟨12175160473221057142668515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32467094595256152380449373 12175160473221057142668515)
            ·
              refine ⟨18262740709831585714002773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12175160473221057142668515 18262740709831585714002773)
              ·
                refine ⟨107008246346669447542985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18262740709831585714002773 107008246346669447542985)
                ·
                  rfl

theorem cell23_5626741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 9].length) (baseStart_5626741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626741 prefixEnd_5626741 := by exact prefixLift 5626741
  have htrace : WordTrace (prefixWord ++ tailWord_5626741) baseStart_5626741 baseEnd_5626741 := by
    simpa [prefixWord, tailWord_5626741, baseEnd_5626741] using wordTrace_append hprefix tailTrace_5626741
  have hstable : (prefixWord ++ tailWord_5626741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626741).length < 2 ^ (prefixWord ++ tailWord_5626741).sum := by decide
  have hdescent : baseEnd_5626741 < baseStart_5626741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626751 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3]
def baseStart_5626751 : Nat := 118140960795 + 5626751 * 2 ^ 59
def prefixEnd_5626751 : Nat := 4983230072969 + 3 ^ 40 * 5626751 * 2
def baseEnd_5626751 : Nat := 2889227786166620044535549

theorem tailTrace_5626751 : CollatzResearch.WordTrace tailWord_5626751 prefixEnd_5626751 2889227786166620044535549 := by
  unfold tailWord_5626751
  simp only [CollatzResearch.WordTrace]
  refine ⟨205224468838249574408976107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136816312558833049605984071 205224468838249574408976107)
  ·
    refine ⟨307836703257374361613464161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205224468838249574408976107 307836703257374361613464161)
    ·
      refine ⟨230877527443030771210098121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307836703257374361613464161 230877527443030771210098121)
      ·
        refine ⟨173158145582273078407573591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230877527443030771210098121 173158145582273078407573591)
        ·
          refine ⟨259737218373409617611360387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173158145582273078407573591 259737218373409617611360387)
          ·
            refine ⟨389605827560114426417040581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259737218373409617611360387 389605827560114426417040581)
            ·
              refine ⟨73051092667521454953195109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 389605827560114426417040581 73051092667521454953195109)
              ·
                refine ⟨13697079875160272803724083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73051092667521454953195109 13697079875160272803724083)
                ·
                  refine ⟨20545619812740409205586125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697079875160272803724083 20545619812740409205586125)
                  ·
                    refine ⟨7704607429777653452094797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20545619812740409205586125 7704607429777653452094797)
                    ·
                      refine ⟨2889227786166620044535549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704607429777653452094797 2889227786166620044535549)
                      ·
                        rfl

theorem cell23_5626751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_5626751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626751 prefixEnd_5626751 := by exact prefixLift 5626751
  have htrace : WordTrace (prefixWord ++ tailWord_5626751) baseStart_5626751 baseEnd_5626751 := by
    simpa [prefixWord, tailWord_5626751, baseEnd_5626751] using wordTrace_append hprefix tailTrace_5626751
  have hstable : (prefixWord ++ tailWord_5626751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626751).length < 2 ^ (prefixWord ++ tailWord_5626751).sum := by decide
  have hdescent : baseEnd_5626751 < baseStart_5626751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626806 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_5626806 : Nat := 118140960795 + 5626806 * 2 ^ 59
def prefixEnd_5626806 : Nat := 4983230072969 + 3 ^ 40 * 5626806 * 2
def baseEnd_5626806 : Nat := 2889256027602617329347797

theorem tailTrace_5626806 : CollatzResearch.WordTrace tailWord_5626806 prefixEnd_5626806 2889256027602617329347797 := by
  unfold tailWord_5626806
  simp only [CollatzResearch.WordTrace]
  refine ⟨12826654678315644925139267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136817649902033545868152181 12826654678315644925139267)
  ·
    refine ⟨19239982017473467387708901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12826654678315644925139267 19239982017473467387708901)
    ·
      refine ⟨3607496628276275135195419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19239982017473467387708901 3607496628276275135195419)
      ·
        refine ⟨5411244942414412702793129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607496628276275135195419 5411244942414412702793129)
        ·
          refine ⟨4058433706810809527094847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411244942414412702793129 4058433706810809527094847)
          ·
            refine ⟨6087650560216214290642271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058433706810809527094847 6087650560216214290642271)
            ·
              refine ⟨9131475840324321435963407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6087650560216214290642271 9131475840324321435963407)
              ·
                refine ⟨13697213760486482153945111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9131475840324321435963407 13697213760486482153945111)
                ·
                  refine ⟨20545820640729723230917667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697213760486482153945111 20545820640729723230917667)
                  ·
                    refine ⟨30818730961094584846376501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20545820640729723230917667 30818730961094584846376501)
                    ·
                      refine ⟨2889256027602617329347797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30818730961094584846376501 2889256027602617329347797)
                      ·
                        rfl

theorem cell23_5626806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_5626806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626806 prefixEnd_5626806 := by exact prefixLift 5626806
  have htrace : WordTrace (prefixWord ++ tailWord_5626806) baseStart_5626806 baseEnd_5626806 := by
    simpa [prefixWord, tailWord_5626806, baseEnd_5626806] using wordTrace_append hprefix tailTrace_5626806
  have hstable : (prefixWord ++ tailWord_5626806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626806).length < 2 ^ (prefixWord ++ tailWord_5626806).sum := by decide
  have hdescent : baseEnd_5626806 < baseStart_5626806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626808 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_5626808 : Nat := 118140960795 + 5626808 * 2 ^ 59
def prefixEnd_5626808 : Nat := 4983230072969 + 3 ^ 40 * 5626808 * 2
def baseEnd_5626808 : Nat := 2889257054563926321522787

theorem tailTrace_5626808 : CollatzResearch.WordTrace tailWord_5626808 prefixEnd_5626808 2889257054563926321522787 := by
  unfold tailWord_5626808
  simp only [CollatzResearch.WordTrace]
  refine ⟨102613273899521536571900539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136817698532695382095867385 102613273899521536571900539)
  ·
    refine ⟨153919910849282304857850809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102613273899521536571900539 153919910849282304857850809)
    ·
      refine ⟨115439933136961728643388107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153919910849282304857850809 115439933136961728643388107)
      ·
        refine ⟨173159899705442592965082161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115439933136961728643388107 173159899705442592965082161)
        ·
          refine ⟨129869924779081944723811621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173159899705442592965082161 129869924779081944723811621)
          ·
            refine ⟨24350610896077864635714679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129869924779081944723811621 24350610896077864635714679)
            ·
              refine ⟨36525916344116796953572019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24350610896077864635714679 36525916344116796953572019)
              ·
                refine ⟨54788874516175195430358029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36525916344116796953572019 54788874516175195430358029)
                ·
                  refine ⟨20545827943565698286384261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54788874516175195430358029 20545827943565698286384261)
                  ·
                    refine ⟨3852342739418568428697049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20545827943565698286384261 3852342739418568428697049)
                    ·
                      refine ⟨2889257054563926321522787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852342739418568428697049 2889257054563926321522787)
                      ·
                        rfl

theorem cell23_5626808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_5626808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626808 prefixEnd_5626808 := by exact prefixLift 5626808
  have htrace : WordTrace (prefixWord ++ tailWord_5626808) baseStart_5626808 baseEnd_5626808 := by
    simpa [prefixWord, tailWord_5626808, baseEnd_5626808] using wordTrace_append hprefix tailTrace_5626808
  have hstable : (prefixWord ++ tailWord_5626808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626808).length < 2 ^ (prefixWord ++ tailWord_5626808).sum := by decide
  have hdescent : baseEnd_5626808 < baseStart_5626808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626820 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5626820 : Nat := 118140960795 + 5626820 * 2 ^ 59
def prefixEnd_5626820 : Nat := 4983230072969 + 3 ^ 40 * 5626820 * 2
def baseEnd_5626820 : Nat := 2889263216331780274572733

theorem tailTrace_5626820 : CollatzResearch.WordTrace tailWord_5626820 prefixEnd_5626820 2889263216331780274572733 := by
  unfold tailWord_5626820
  simp only [CollatzResearch.WordTrace]
  refine ⟨102613492737499799596618957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136817990316666399462158609 102613492737499799596618957)
  ·
    refine ⟨38480059776562424848732109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102613492737499799596618957 38480059776562424848732109)
    ·
      refine ⟨14430022416210909318274541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38480059776562424848732109 14430022416210909318274541)
      ·
        refine ⟨5411258406079090994352953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14430022416210909318274541 5411258406079090994352953)
        ·
          refine ⟨4058443804559318245764715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411258406079090994352953 4058443804559318245764715)
          ·
            refine ⟨6087665706838977368647073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4058443804559318245764715 6087665706838977368647073)
            ·
              refine ⟨4565749280129233026485305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087665706838977368647073 4565749280129233026485305)
              ·
                refine ⟨3424311960096924769863979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4565749280129233026485305 3424311960096924769863979)
                ·
                  refine ⟨5136467940145387154795969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424311960096924769863979 5136467940145387154795969)
                  ·
                    refine ⟨3852350955109040366096977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5136467940145387154795969 3852350955109040366096977)
                    ·
                      refine ⟨2889263216331780274572733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852350955109040366096977 2889263216331780274572733)
                      ·
                        rfl

theorem cell23_5626820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5626820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626820 prefixEnd_5626820 := by exact prefixLift 5626820
  have htrace : WordTrace (prefixWord ++ tailWord_5626820) baseStart_5626820 baseEnd_5626820 := by
    simpa [prefixWord, tailWord_5626820, baseEnd_5626820] using wordTrace_append hprefix tailTrace_5626820
  have hstable : (prefixWord ++ tailWord_5626820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626820).length < 2 ^ (prefixWord ++ tailWord_5626820).sum := by decide
  have hdescent : baseEnd_5626820 < baseStart_5626820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626842 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_5626842 : Nat := 118140960795 + 5626842 * 2 ^ 59
def prefixEnd_5626842 : Nat := 4983230072969 + 3 ^ 40 * 5626842 * 2
def baseEnd_5626842 : Nat := 2889274512906179188497631

theorem tailTrace_5626842 : CollatzResearch.WordTrace tailWord_5626842 prefixEnd_5626842 2889274512906179188497631 := by
  unfold tailWord_5626842
  simp only [CollatzResearch.WordTrace]
  refine ⟨51306946970229974237634695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136818525253946597967025853 51306946970229974237634695)
  ·
    refine ⟨76960420455344961356452043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51306946970229974237634695 76960420455344961356452043)
    ·
      refine ⟨115440630683017442034678065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76960420455344961356452043 115440630683017442034678065)
      ·
        refine ⟨86580473012263081526008549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115440630683017442034678065 86580473012263081526008549)
        ·
          refine ⟨16233838689799327786126603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86580473012263081526008549 16233838689799327786126603)
          ·
            refine ⟨24350758034698991679189905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16233838689799327786126603 24350758034698991679189905)
            ·
              refine ⟨18263068526024243759392429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24350758034698991679189905 18263068526024243759392429)
              ·
                refine ⟨6848650697259091409772161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18263068526024243759392429 6848650697259091409772161)
                ·
                  refine ⟨5136488022944318557329121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6848650697259091409772161 5136488022944318557329121)
                  ·
                    refine ⟨3852366017208238917996841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5136488022944318557329121 3852366017208238917996841)
                    ·
                      refine ⟨2889274512906179188497631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852366017208238917996841 2889274512906179188497631)
                      ·
                        rfl

theorem cell23_5626842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_5626842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626842 prefixEnd_5626842 := by exact prefixLift 5626842
  have htrace : WordTrace (prefixWord ++ tailWord_5626842) baseStart_5626842 baseEnd_5626842 := by
    simpa [prefixWord, tailWord_5626842, baseEnd_5626842] using wordTrace_append hprefix tailTrace_5626842
  have hstable : (prefixWord ++ tailWord_5626842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626842).length < 2 ^ (prefixWord ++ tailWord_5626842).sum := by decide
  have hdescent : baseEnd_5626842 < baseStart_5626842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626865 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 5]
def baseStart_5626865 : Nat := 118140960795 + 5626865 * 2 ^ 59
def prefixEnd_5626865 : Nat := 4983230072969 + 3 ^ 40 * 5626865 * 2
def baseEnd_5626865 : Nat := 321031813662359177612225

theorem tailTrace_5626865 : CollatzResearch.WordTrace tailWord_5626865 prefixEnd_5626865 321031813662359177612225 := by
  unfold tailWord_5626865
  simp only [CollatzResearch.WordTrace]
  refine ⟨205228626759836571878626049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136819084506557714585750699 205228626759836571878626049)
  ·
    refine ⟨153921470069877428908969537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205228626759836571878626049 153921470069877428908969537)
    ·
      refine ⟨115441102552408071681727153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153921470069877428908969537 115441102552408071681727153)
      ·
        refine ⟨86580826914306053761295365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115441102552408071681727153 86580826914306053761295365)
        ·
          refine ⟨16233905046432385080242881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86580826914306053761295365 16233905046432385080242881)
          ·
            refine ⟨12175428784824288810182161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16233905046432385080242881 12175428784824288810182161)
            ·
              refine ⟨9131571588618216607636621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175428784824288810182161 9131571588618216607636621)
              ·
                refine ⟨3424339345731831227863733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9131571588618216607636621 3424339345731831227863733)
                ·
                  refine ⟨321031813662359177612225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3424339345731831227863733 321031813662359177612225)
                  ·
                    rfl

theorem cell23_5626865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 5].length) (baseStart_5626865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626865 prefixEnd_5626865 := by exact prefixLift 5626865
  have htrace : WordTrace (prefixWord ++ tailWord_5626865) baseStart_5626865 baseEnd_5626865 := by
    simpa [prefixWord, tailWord_5626865, baseEnd_5626865] using wordTrace_append hprefix tailTrace_5626865
  have hstable : (prefixWord ++ tailWord_5626865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626865).length < 2 ^ (prefixWord ++ tailWord_5626865).sum := by decide
  have hdescent : baseEnd_5626865 < baseStart_5626865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626882 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_5626882 : Nat := 118140960795 + 5626882 * 2 ^ 59
def prefixEnd_5626882 : Nat := 4983230072969 + 3 ^ 40 * 5626882 * 2
def baseEnd_5626882 : Nat := 321032783570262114666383

theorem tailTrace_5626882 : CollatzResearch.WordTrace tailWord_5626882 prefixEnd_5626882 321032783570262114666383 := by
  unfold tailWord_5626882
  simp only [CollatzResearch.WordTrace]
  refine ⟨51307311700193745945498725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136819497867183322521329933 51307311700193745945498725)
  ·
    refine ⟨9620120943786327364781011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51307311700193745945498725 9620120943786327364781011)
    ·
      refine ⟨14430181415679491047171517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9620120943786327364781011 14430181415679491047171517)
      ·
        refine ⟨5411318030879809142689319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14430181415679491047171517 5411318030879809142689319)
        ·
          refine ⟨8116977046319713714033979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5411318030879809142689319 8116977046319713714033979)
          ·
            refine ⟨12175465569479570571050969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8116977046319713714033979 12175465569479570571050969)
            ·
              refine ⟨9131599177109677928288227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12175465569479570571050969 9131599177109677928288227)
              ·
                refine ⟨13697398765664516892432341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9131599177109677928288227 13697398765664516892432341)
                ·
                  refine ⟨321032783570262114666383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13697398765664516892432341 321032783570262114666383)
                  ·
                    rfl

theorem cell23_5626882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_5626882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626882 prefixEnd_5626882 := by exact prefixLift 5626882
  have htrace : WordTrace (prefixWord ++ tailWord_5626882) baseStart_5626882 baseEnd_5626882 := by
    simpa [prefixWord, tailWord_5626882, baseEnd_5626882] using wordTrace_append hprefix tailTrace_5626882
  have hstable : (prefixWord ++ tailWord_5626882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626882).length < 2 ^ (prefixWord ++ tailWord_5626882).sum := by decide
  have hdescent : baseEnd_5626882 < baseStart_5626882 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626932 : List Nat := [2, 5, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_5626932 : Nat := 118140960795 + 5626932 * 2 ^ 59
def prefixEnd_5626932 : Nat := 4983230072969 + 3 ^ 40 * 5626932 * 2
def baseEnd_5626932 : Nat := 2889320726165083836372217

theorem tailTrace_5626932 : CollatzResearch.WordTrace tailWord_5626932 prefixEnd_5626932 2889320726165083836372217 := by
  unfold tailWord_5626932
  simp only [CollatzResearch.WordTrace]
  refine ⟨102615535225296921160657525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136820713633729228214210033 102615535225296921160657525)
  ·
    refine ⟨9620206427371586358811643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102615535225296921160657525 9620206427371586358811643)
    ·
      refine ⟨14430309641057379538217465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9620206427371586358811643 14430309641057379538217465)
      ·
        refine ⟨10822732230793034653663099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14430309641057379538217465 10822732230793034653663099)
        ·
          refine ⟨16234098346189551980494649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822732230793034653663099 16234098346189551980494649)
          ·
            refine ⟨12175573759642163985370987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16234098346189551980494649 12175573759642163985370987)
            ·
              refine ⟨18263360639463245978056481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12175573759642163985370987 18263360639463245978056481)
              ·
                refine ⟨13697520479597434483542361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18263360639463245978056481 13697520479597434483542361)
                ·
                  refine ⟨10273140359698075862656771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13697520479597434483542361 10273140359698075862656771)
                  ·
                    refine ⟨15409710539547113793985157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10273140359698075862656771 15409710539547113793985157)
                    ·
                      refine ⟨2889320726165083836372217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15409710539547113793985157 2889320726165083836372217)
                      ·
                        rfl

theorem cell23_5626932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_5626932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626932 prefixEnd_5626932 := by exact prefixLift 5626932
  have htrace : WordTrace (prefixWord ++ tailWord_5626932) baseStart_5626932 baseEnd_5626932 := by
    simpa [prefixWord, tailWord_5626932, baseEnd_5626932] using wordTrace_append hprefix tailTrace_5626932
  have hstable : (prefixWord ++ tailWord_5626932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626932).length < 2 ^ (prefixWord ++ tailWord_5626932).sum := by decide
  have hdescent : baseEnd_5626932 < baseStart_5626932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626942 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_5626942 : Nat := 118140960795 + 5626942 * 2 ^ 59
def prefixEnd_5626942 : Nat := 4983230072969 + 3 ^ 40 * 5626942 * 2
def baseEnd_5626942 : Nat := 963108620323876265749057

theorem tailTrace_5626942 : CollatzResearch.WordTrace tailWord_5626942 prefixEnd_5626942 963108620323876265749057 := by
  unfold tailWord_5626942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25653929397569701753647385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136820956787038409352786053 25653929397569701753647385)
  ·
    refine ⟨19240447048177276315235539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25653929397569701753647385 19240447048177276315235539)
    ·
      refine ⟨28860670572265914472853309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19240447048177276315235539 28860670572265914472853309)
      ·
        refine ⟨10822751464599717927319991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28860670572265914472853309 10822751464599717927319991)
        ·
          refine ⟨16234127196899576890979987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10822751464599717927319991 16234127196899576890979987)
          ·
            refine ⟨24351190795349365336469981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16234127196899576890979987 24351190795349365336469981)
            ·
              refine ⟨9131696548256012001176243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24351190795349365336469981 9131696548256012001176243)
              ·
                refine ⟨13697544822384018001764365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9131696548256012001176243 13697544822384018001764365)
                ·
                  refine ⟨5136579308394006750661637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13697544822384018001764365 5136579308394006750661637)
                  ·
                    refine ⟨963108620323876265749057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5136579308394006750661637 963108620323876265749057)
                    ·
                      rfl

theorem cell23_5626942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_5626942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626942 prefixEnd_5626942 := by exact prefixLift 5626942
  have htrace : WordTrace (prefixWord ++ tailWord_5626942) baseStart_5626942 baseEnd_5626942 := by
    simpa [prefixWord, tailWord_5626942, baseEnd_5626942] using wordTrace_append hprefix tailTrace_5626942
  have hstable : (prefixWord ++ tailWord_5626942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626942).length < 2 ^ (prefixWord ++ tailWord_5626942).sum := by decide
  have hdescent : baseEnd_5626942 < baseStart_5626942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626965 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5626965 : Nat := 118140960795 + 5626965 * 2 ^ 59
def prefixEnd_5626965 : Nat := 4983230072969 + 3 ^ 40 * 5626965 * 2
def baseEnd_5626965 : Nat := 2889337671026682207259565

theorem tailTrace_5626965 : CollatzResearch.WordTrace tailWord_5626965 prefixEnd_5626965 2889337671026682207259565 := by
  unfold tailWord_5626965
  simp only [CollatzResearch.WordTrace]
  refine ⟨205232274059474288957266349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136821516039649525971510899 205232274059474288957266349)
  ·
    refine ⟨76962102772302858358974881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205232274059474288957266349 76962102772302858358974881)
    ·
      refine ⟨57721577079227143769231161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76962102772302858358974881 57721577079227143769231161)
      ·
        refine ⟨43291182809420357826923371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57721577079227143769231161 43291182809420357826923371)
        ·
          refine ⟨64936774214130536740385057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43291182809420357826923371 64936774214130536740385057)
          ·
            refine ⟨48702580660597902555288793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64936774214130536740385057 48702580660597902555288793)
            ·
              refine ⟨36526935495448426916466595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48702580660597902555288793 36526935495448426916466595)
              ·
                refine ⟨54790403243172640374699893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36526935495448426916466595 54790403243172640374699893)
                ·
                  refine ⟨5136600304047435035128115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54790403243172640374699893 5136600304047435035128115)
                  ·
                    refine ⟨7704900456071152552692173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5136600304047435035128115 7704900456071152552692173)
                    ·
                      refine ⟨2889337671026682207259565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7704900456071152552692173 2889337671026682207259565)
                      ·
                        rfl

theorem cell23_5626965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5626965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626965 prefixEnd_5626965 := by exact prefixLift 5626965
  have htrace : WordTrace (prefixWord ++ tailWord_5626965) baseStart_5626965 baseEnd_5626965 := by
    simpa [prefixWord, tailWord_5626965, baseEnd_5626965] using wordTrace_append hprefix tailTrace_5626965
  have hstable : (prefixWord ++ tailWord_5626965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626965).length < 2 ^ (prefixWord ++ tailWord_5626965).sum := by decide
  have hdescent : baseEnd_5626965 < baseStart_5626965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5626968 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_5626968 : Nat := 118140960795 + 5626968 * 2 ^ 59
def prefixEnd_5626968 : Nat := 4983230072969 + 3 ^ 40 * 5626968 * 2
def baseEnd_5626968 : Nat := 963113070489548565174017

theorem tailTrace_5626968 : CollatzResearch.WordTrace tailWord_5626968 prefixEnd_5626968 963113070489548565174017 := by
  unfold tailWord_5626968
  simp only [CollatzResearch.WordTrace]
  refine ⟨102616191739231710234812779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136821588985642280313083705 102616191739231710234812779)
  ·
    refine ⟨153924287608847565352219169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102616191739231710234812779 153924287608847565352219169)
    ·
      refine ⟨115443215706635674014164377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153924287608847565352219169 115443215706635674014164377)
      ·
        refine ⟨86582411779976755510623283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115443215706635674014164377 86582411779976755510623283)
        ·
          refine ⟨129873617669965133265934925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86582411779976755510623283 129873617669965133265934925)
          ·
            refine ⟨48702606626236924974725597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129873617669965133265934925 48702606626236924974725597)
            ·
              refine ⟨18263477484838846865522099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48702606626236924974725597 18263477484838846865522099)
              ·
                refine ⟨27395216227258270298283149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18263477484838846865522099 27395216227258270298283149)
                ·
                  refine ⟨10273206085221851361856181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27395216227258270298283149 10273206085221851361856181)
                  ·
                    refine ⟨963113070489548565174017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10273206085221851361856181 963113070489548565174017)
                    ·
                      rfl

theorem cell23_5626968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_5626968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5626968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5626968 prefixEnd_5626968 := by exact prefixLift 5626968
  have htrace : WordTrace (prefixWord ++ tailWord_5626968) baseStart_5626968 baseEnd_5626968 := by
    simpa [prefixWord, tailWord_5626968, baseEnd_5626968] using wordTrace_append hprefix tailTrace_5626968
  have hstable : (prefixWord ++ tailWord_5626968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5626968).length < 2 ^ (prefixWord ++ tailWord_5626968).sum := by decide
  have hdescent : baseEnd_5626968 < baseStart_5626968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5626968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627008 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_5627008 : Nat := 118140960795 + 5627008 * 2 ^ 59
def prefixEnd_5627008 : Nat := 4983230072969 + 3 ^ 40 * 5627008 * 2
def baseEnd_5627008 : Nat := 2889359750694825539021867

theorem tailTrace_5627008 : CollatzResearch.WordTrace tailWord_5627008 prefixEnd_5627008 2889359750694825539021867 := by
  unfold tailWord_5627008
  simp only [CollatzResearch.WordTrace]
  refine ⟨102616921199159253650540839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136822561598879004867387785 102616921199159253650540839)
  ·
    refine ⟨153925381798738880475811259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102616921199159253650540839 153925381798738880475811259)
    ·
      refine ⟨230888072698108320713716889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153925381798738880475811259 230888072698108320713716889)
      ·
        refine ⟨173166054523581240535287667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230888072698108320713716889 173166054523581240535287667)
        ·
          refine ⟨259749081785371860802931501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173166054523581240535287667 259749081785371860802931501)
          ·
            refine ⟨97405905669514447801099313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259749081785371860802931501 97405905669514447801099313)
            ·
              refine ⟨73054429252135835850824485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97405905669514447801099313 73054429252135835850824485)
              ·
                refine ⟨13697705484775469222029591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73054429252135835850824485 13697705484775469222029591)
                ·
                  refine ⟨20546558227163203833044387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13697705484775469222029591 20546558227163203833044387)
                  ·
                    refine ⟨30819837340744805749566581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20546558227163203833044387 30819837340744805749566581)
                    ·
                      refine ⟨2889359750694825539021867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30819837340744805749566581 2889359750694825539021867)
                      ·
                        rfl

theorem cell23_5627008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_5627008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627008 prefixEnd_5627008 := by exact prefixLift 5627008
  have htrace : WordTrace (prefixWord ++ tailWord_5627008) baseStart_5627008 baseEnd_5627008 := by
    simpa [prefixWord, tailWord_5627008, baseEnd_5627008] using wordTrace_append hprefix tailTrace_5627008
  have hstable : (prefixWord ++ tailWord_5627008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627008).length < 2 ^ (prefixWord ++ tailWord_5627008).sum := by decide
  have hdescent : baseEnd_5627008 < baseStart_5627008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627129 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 2, 2, 2]
def baseStart_5627129 : Nat := 118140960795 + 5627129 * 2 ^ 59
def prefixEnd_5627129 : Nat := 4983230072969 + 3 ^ 40 * 5627129 * 2
def baseEnd_5627129 : Nat := 2889421881854019565608811

theorem tailTrace_5627129 : CollatzResearch.WordTrace tailWord_5627129 prefixEnd_5627129 2889421881854019565608811 := by
  unfold tailWord_5627129
  simp only [CollatzResearch.WordTrace]
  refine ⟨205238255630880144966236441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136825503753920096644157627 205238255630880144966236441)
  ·
    refine ⟨153928691723160108724677331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205238255630880144966236441 153928691723160108724677331)
    ·
      refine ⟨230893037584740163087015997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153928691723160108724677331 230893037584740163087015997)
      ·
        refine ⟨86584889094277561157630999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230893037584740163087015997 86584889094277561157630999)
        ·
          refine ⟨129877333641416341736446499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86584889094277561157630999 129877333641416341736446499)
          ·
            refine ⟨194816000462124512604669749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129877333641416341736446499 194816000462124512604669749)
            ·
              refine ⟨18264000043324173056687789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194816000462124512604669749 18264000043324173056687789)
              ·
                refine ⟨6849000016246564896257921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18264000043324173056687789 6849000016246564896257921)
                ·
                  refine ⟨5136750012184923672193441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6849000016246564896257921 5136750012184923672193441)
                  ·
                    refine ⟨3852562509138692754145081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5136750012184923672193441 3852562509138692754145081)
                    ·
                      refine ⟨2889421881854019565608811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852562509138692754145081 2889421881854019565608811)
                      ·
                        rfl

theorem cell23_5627129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_5627129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627129 prefixEnd_5627129 := by exact prefixLift 5627129
  have htrace : WordTrace (prefixWord ++ tailWord_5627129) baseStart_5627129 baseEnd_5627129 := by
    simpa [prefixWord, tailWord_5627129, baseEnd_5627129] using wordTrace_append hprefix tailTrace_5627129
  have hstable : (prefixWord ++ tailWord_5627129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627129).length < 2 ^ (prefixWord ++ tailWord_5627129).sum := by decide
  have hdescent : baseEnd_5627129 < baseStart_5627129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627172 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_5627172 : Nat := 118140960795 + 5627172 * 2 ^ 59
def prefixEnd_5627172 : Nat := 4983230072969 + 3 ^ 40 * 5627172 * 2
def baseEnd_5627172 : Nat := 2889443961522162897371113

theorem tailTrace_5627172 : CollatzResearch.WordTrace tailWord_5627172 prefixEnd_5627172 2889443961522162897371113 := by
  unfold tailWord_5627172
  simp only [CollatzResearch.WordTrace]
  refine ⟨102619911984862181655025885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136826549313149575540034513 102619911984862181655025885)
  ·
    refine ⟨38482466994323318120634707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102619911984862181655025885 38482466994323318120634707)
    ·
      refine ⟨57723700491484977180952061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38482466994323318120634707 57723700491484977180952061)
      ·
        refine ⟨21646387684306866442857023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57723700491484977180952061 21646387684306866442857023)
        ·
          refine ⟨32469581526460299664285535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21646387684306866442857023 32469581526460299664285535)
          ·
            refine ⟨48704372289690449496428303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32469581526460299664285535 48704372289690449496428303)
            ·
              refine ⟨73056558434535674244642455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48704372289690449496428303 73056558434535674244642455)
              ·
                refine ⟨109584837651803511366963683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73056558434535674244642455 109584837651803511366963683)
                ·
                  refine ⟨164377256477705267050445525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109584837651803511366963683 164377256477705267050445525)
                  ·
                    refine ⟨3852591948696217196494817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 164377256477705267050445525 3852591948696217196494817)
                    ·
                      refine ⟨2889443961522162897371113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852591948696217196494817 2889443961522162897371113)
                      ·
                        rfl

theorem cell23_5627172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_5627172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627172 prefixEnd_5627172 := by exact prefixLift 5627172
  have htrace : WordTrace (prefixWord ++ tailWord_5627172) baseStart_5627172 baseEnd_5627172 := by
    simpa [prefixWord, tailWord_5627172, baseEnd_5627172] using wordTrace_append hprefix tailTrace_5627172
  have hstable : (prefixWord ++ tailWord_5627172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627172).length < 2 ^ (prefixWord ++ tailWord_5627172).sum := by decide
  have hdescent : baseEnd_5627172 < baseStart_5627172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627332 : List Nat := [2, 3, 3, 2, 1, 12]
def baseStart_5627332 : Nat := 118140960795 + 5627332 * 2 ^ 59
def prefixEnd_5627332 : Nat := 4983230072969 + 3 ^ 40 * 5627332 * 2
def baseEnd_5627332 : Nat := 11891053985295811816339

theorem tailTrace_5627332 : CollatzResearch.WordTrace tailWord_5627332 prefixEnd_5627332 11891053985295811816339 := by
  unfold tailWord_5627332
  simp only [CollatzResearch.WordTrace]
  refine ⟨102622829824572355317938125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136830439766096473757250833 102622829824572355317938125)
  ·
    refine ⟨38483561184214633244226797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102622829824572355317938125 38483561184214633244226797)
    ·
      refine ⟨14431335444080487466585049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38483561184214633244226797 14431335444080487466585049)
      ·
        refine ⟨10823501583060365599938787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14431335444080487466585049 10823501583060365599938787)
        ·
          refine ⟨16235252374590548399908181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10823501583060365599938787 16235252374590548399908181)
          ·
            refine ⟨11891053985295811816339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16235252374590548399908181 11891053985295811816339)
            ·
              rfl

theorem cell23_5627332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 12].length) (baseStart_5627332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627332 prefixEnd_5627332 := by exact prefixLift 5627332
  have htrace : WordTrace (prefixWord ++ tailWord_5627332) baseStart_5627332 baseEnd_5627332 := by
    simpa [prefixWord, tailWord_5627332, baseEnd_5627332] using wordTrace_append hprefix tailTrace_5627332
  have hstable : (prefixWord ++ tailWord_5627332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627332).length < 2 ^ (prefixWord ++ tailWord_5627332).sum := by decide
  have hdescent : baseEnd_5627332 < baseStart_5627332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627355 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7]
def baseStart_5627355 : Nat := 118140960795 + 5627355 * 2 ^ 59
def prefixEnd_5627355 : Nat := 4983230072969 + 3 ^ 40 * 5627355 * 2
def baseEnd_5627355 : Nat := 2889537928481935681382771

theorem tailTrace_5627355 : CollatzResearch.WordTrace tailWord_5627355 prefixEnd_5627355 2889537928481935681382771 := by
  unfold tailWord_5627355
  simp only [CollatzResearch.WordTrace]
  refine ⟨205246498528061385563963519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136830999018707590375975679 205246498528061385563963519)
  ·
    refine ⟨307869747792092078345945279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205246498528061385563963519 307869747792092078345945279)
    ·
      refine ⟨461804621688138117518917919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307869747792092078345945279 461804621688138117518917919)
      ·
        refine ⟨692706932532207176278376879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461804621688138117518917919 692706932532207176278376879)
        ·
          refine ⟨1039060398798310764417565319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692706932532207176278376879 1039060398798310764417565319)
          ·
            refine ⟨1558590598197466146626347979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039060398798310764417565319 1558590598197466146626347979)
            ·
              refine ⟨2337885897296199219939521969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558590598197466146626347979 2337885897296199219939521969)
              ·
                refine ⟨1753414422972149414954641477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2337885897296199219939521969 1753414422972149414954641477)
                ·
                  refine ⟨328765204307278015303995277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1753414422972149414954641477 328765204307278015303995277)
                  ·
                    refine ⟨123286951615229255738998229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328765204307278015303995277 123286951615229255738998229)
                    ·
                      refine ⟨2889537928481935681382771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123286951615229255738998229 2889537928481935681382771)
                      ·
                        rfl

theorem cell23_5627355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_5627355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627355 prefixEnd_5627355 := by exact prefixLift 5627355
  have htrace : WordTrace (prefixWord ++ tailWord_5627355) baseStart_5627355 baseEnd_5627355 := by
    simpa [prefixWord, tailWord_5627355, baseEnd_5627355] using wordTrace_append hprefix tailTrace_5627355
  have hstable : (prefixWord ++ tailWord_5627355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627355).length < 2 ^ (prefixWord ++ tailWord_5627355).sum := by decide
  have hdescent : baseEnd_5627355 < baseStart_5627355 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627359 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3]
def baseStart_5627359 : Nat := 118140960795 + 5627359 * 2 ^ 59
def prefixEnd_5627359 : Nat := 4983230072969 + 3 ^ 40 * 5627359 * 2
def baseEnd_5627359 : Nat := 2889539982404553665732753

theorem tailTrace_5627359 : CollatzResearch.WordTrace tailWord_5627359 prefixEnd_5627359 2889539982404553665732753 := by
  unfold tailWord_5627359
  simp only [CollatzResearch.WordTrace]
  refine ⟨205246644420046894247109131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136831096280031262831406087 205246644420046894247109131)
  ·
    refine ⟨307869966630070341370663697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205246644420046894247109131 307869966630070341370663697)
    ·
      refine ⟨230902474972552756027997773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307869966630070341370663697 230902474972552756027997773)
      ·
        refine ⟨86588428114707283510499165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230902474972552756027997773 86588428114707283510499165)
        ·
          refine ⟨32470660543015231316437187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86588428114707283510499165 32470660543015231316437187)
          ·
            refine ⟨48705990814522846974655781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32470660543015231316437187 48705990814522846974655781)
            ·
              refine ⟨9132373277723033807747959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48705990814522846974655781 9132373277723033807747959)
              ·
                refine ⟨13698559916584550711621939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132373277723033807747959 13698559916584550711621939)
                ·
                  refine ⟨20547839874876826067432909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13698559916584550711621939 20547839874876826067432909)
                  ·
                    refine ⟨7705439953078809775287341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20547839874876826067432909 7705439953078809775287341)
                    ·
                      refine ⟨2889539982404553665732753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7705439953078809775287341 2889539982404553665732753)
                      ·
                        rfl

theorem cell23_5627359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_5627359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627359 prefixEnd_5627359 := by exact prefixLift 5627359
  have htrace : WordTrace (prefixWord ++ tailWord_5627359) baseStart_5627359 baseEnd_5627359 := by
    simpa [prefixWord, tailWord_5627359, baseEnd_5627359] using wordTrace_append hprefix tailTrace_5627359
  have hstable : (prefixWord ++ tailWord_5627359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627359).length < 2 ^ (prefixWord ++ tailWord_5627359).sum := by decide
  have hdescent : baseEnd_5627359 < baseStart_5627359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627386 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_5627386 : Nat := 118140960795 + 5627386 * 2 ^ 59
def prefixEnd_5627386 : Nat := 4983230072969 + 3 ^ 40 * 5627386 * 2
def baseEnd_5627386 : Nat := 2889553846382225060095129

theorem tailTrace_5627386 : CollatzResearch.WordTrace tailWord_5627386 prefixEnd_5627386 2889553846382225060095129 := by
  unfold tailWord_5627386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51311907297737269464585503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136831752793966051905561341 51311907297737269464585503)
  ·
    refine ⟨76967860946605904196878255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51311907297737269464585503 76967860946605904196878255)
    ·
      refine ⟨115451791419908856295317383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76967860946605904196878255 115451791419908856295317383)
      ·
        refine ⟨173177687129863284442976075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115451791419908856295317383 173177687129863284442976075)
        ·
          refine ⟨259766530694794926664464113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173177687129863284442976075 259766530694794926664464113)
          ·
            refine ⟨194824898021096194998348085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259766530694794926664464113 194824898021096194998348085)
            ·
              refine ⟨18264834189477768281095133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194824898021096194998348085 18264834189477768281095133)
              ·
                refine ⟨6849312821054163105410675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18264834189477768281095133 6849312821054163105410675)
                ·
                  refine ⟨10273969231581244658116013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849312821054163105410675 10273969231581244658116013)
                  ·
                    refine ⟨3852738461842966746793505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10273969231581244658116013 3852738461842966746793505)
                    ·
                      refine ⟨2889553846382225060095129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852738461842966746793505 2889553846382225060095129)
                      ·
                        rfl

theorem cell23_5627386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_5627386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627386 prefixEnd_5627386 := by exact prefixLift 5627386
  have htrace : WordTrace (prefixWord ++ tailWord_5627386) baseStart_5627386 baseEnd_5627386 := by
    simpa [prefixWord, tailWord_5627386, baseEnd_5627386] using wordTrace_append hprefix tailTrace_5627386
  have hstable : (prefixWord ++ tailWord_5627386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627386).length < 2 ^ (prefixWord ++ tailWord_5627386).sum := by decide
  have hdescent : baseEnd_5627386 < baseStart_5627386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627482 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_5627482 : Nat := 118140960795 + 5627482 * 2 ^ 59
def prefixEnd_5627482 : Nat := 4983230072969 + 3 ^ 40 * 5627482 * 2
def baseEnd_5627482 : Nat := 963201046841685561498229

theorem tailTrace_5627482 : CollatzResearch.WordTrace tailWord_5627482 prefixEnd_5627482 963201046841685561498229 := by
  unfold tailWord_5627482
  simp only [CollatzResearch.WordTrace]
  refine ⟨51312782649650321563459175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136834087065734190835891133 51312782649650321563459175)
  ·
    refine ⟨76969173974475482345188763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51312782649650321563459175 76969173974475482345188763)
    ·
      refine ⟨115453760961713223517783145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76969173974475482345188763 115453760961713223517783145)
      ·
        refine ⟨86590320721284917638337359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115453760961713223517783145 86590320721284917638337359)
        ·
          refine ⟨129885481081927376457506039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86590320721284917638337359 129885481081927376457506039)
          ·
            refine ⟨194828221622891064686259059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129885481081927376457506039 194828221622891064686259059)
            ·
              refine ⟨292242332434336597029388589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194828221622891064686259059 292242332434336597029388589)
              ·
                refine ⟨109590874662876223886020721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292242332434336597029388589 109590874662876223886020721)
                ·
                  refine ⟨82193155997157167914515541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109590874662876223886020721 82193155997157167914515541)
                  ·
                    refine ⟨963201046841685561498229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82193155997157167914515541 963201046841685561498229)
                    ·
                      rfl

theorem cell23_5627482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_5627482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627482 prefixEnd_5627482 := by exact prefixLift 5627482
  have htrace : WordTrace (prefixWord ++ tailWord_5627482) baseStart_5627482 baseEnd_5627482 := by
    simpa [prefixWord, tailWord_5627482, baseEnd_5627482] using wordTrace_append hprefix tailTrace_5627482
  have hstable : (prefixWord ++ tailWord_5627482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627482).length < 2 ^ (prefixWord ++ tailWord_5627482).sum := by decide
  have hdescent : baseEnd_5627482 < baseStart_5627482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627506 : List Nat := [3, 2, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5627506 : Nat := 118140960795 + 5627506 * 2 ^ 59
def prefixEnd_5627506 : Nat := 4983230072969 + 3 ^ 40 * 5627506 * 2
def baseEnd_5627506 : Nat := 2889615464060764590594577

theorem tailTrace_5627506 : CollatzResearch.WordTrace tailWord_5627506 prefixEnd_5627506 2889615464060764590594577 := by
  unfold tailWord_5627506
  simp only [CollatzResearch.WordTrace]
  refine ⟨51313001487628584588177593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136834670633676225568473581 51313001487628584588177593)
  ·
    refine ⟨38484751115721438441133195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51313001487628584588177593 38484751115721438441133195)
    ·
      refine ⟨57727126673582157661699793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38484751115721438441133195 57727126673582157661699793)
      ·
        refine ⟨43295345005186618246274845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57727126673582157661699793 43295345005186618246274845)
        ·
          refine ⟨16235754376944981842353067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43295345005186618246274845 16235754376944981842353067)
          ·
            refine ⟨24353631565417472763529601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16235754376944981842353067 24353631565417472763529601)
            ·
              refine ⟨18265223674063104572647201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24353631565417472763529601 18265223674063104572647201)
              ·
                refine ⟨13698917755547328429485401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18265223674063104572647201 13698917755547328429485401)
                ·
                  refine ⟨10274188316660496322114051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13698917755547328429485401 10274188316660496322114051)
                  ·
                    refine ⟨15411282474990744483171077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274188316660496322114051 15411282474990744483171077)
                    ·
                      refine ⟨2889615464060764590594577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15411282474990744483171077 2889615464060764590594577)
                      ·
                        rfl

theorem cell23_5627506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5627506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627506 prefixEnd_5627506 := by exact prefixLift 5627506
  have htrace : WordTrace (prefixWord ++ tailWord_5627506) baseStart_5627506 baseEnd_5627506 := by
    simpa [prefixWord, tailWord_5627506, baseEnd_5627506] using wordTrace_append hprefix tailTrace_5627506
  have hstable : (prefixWord ++ tailWord_5627506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627506).length < 2 ^ (prefixWord ++ tailWord_5627506).sum := by decide
  have hdescent : baseEnd_5627506 < baseStart_5627506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627529 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 6]
def baseStart_5627529 : Nat := 118140960795 + 5627529 * 2 ^ 59
def prefixEnd_5627529 : Nat := 4983230072969 + 3 ^ 40 * 5627529 * 2
def baseEnd_5627529 : Nat := 321069697123979777845219

theorem tailTrace_5627529 : CollatzResearch.WordTrace tailWord_5627529 prefixEnd_5627529 321069697123979777845219 := by
  unfold tailWord_5627529
  simp only [CollatzResearch.WordTrace]
  refine ⟨205252844829431013280797641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136835229886287342187198427 205252844829431013280797641)
  ·
    refine ⟨153939633622073259960598231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205252844829431013280797641 153939633622073259960598231)
    ·
      refine ⟨230909450433109889940897347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153939633622073259960598231 230909450433109889940897347)
      ·
        refine ⟨346364175649664834911346021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230909450433109889940897347 346364175649664834911346021)
        ·
          refine ⟨64943282934312156545877379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 346364175649664834911346021 64943282934312156545877379)
          ·
            refine ⟨97414924401468234818816069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64943282934312156545877379 97414924401468234818816069)
            ·
              refine ⟨18265298325275294028528013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97414924401468234818816069 18265298325275294028528013)
              ·
                refine ⟨6849486871978235260698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18265298325275294028528013 6849486871978235260698005)
                ·
                  refine ⟨321069697123979777845219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6849486871978235260698005 321069697123979777845219)
                  ·
                    rfl

theorem cell23_5627529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_5627529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627529 prefixEnd_5627529 := by exact prefixLift 5627529
  have htrace : WordTrace (prefixWord ++ tailWord_5627529) baseStart_5627529 baseEnd_5627529 := by
    simpa [prefixWord, tailWord_5627529, baseEnd_5627529] using wordTrace_append hprefix tailTrace_5627529
  have hstable : (prefixWord ++ tailWord_5627529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627529).length < 2 ^ (prefixWord ++ tailWord_5627529).sum := by decide
  have hdescent : baseEnd_5627529 < baseStart_5627529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627540 : List Nat := [2, 4, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_5627540 : Nat := 118140960795 + 5627540 * 2 ^ 59
def prefixEnd_5627540 : Nat := 4983230072969 + 3 ^ 40 * 5627540 * 2
def baseEnd_5627540 : Nat := 2889632922403017457569421

theorem tailTrace_5627540 : CollatzResearch.WordTrace tailWord_5627540 prefixEnd_5627540 2889632922403017457569421 := by
  unfold tailWord_5627540
  simp only [CollatzResearch.WordTrace]
  refine ⟨102626623016195581079724037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136835497354927441439632049 102626623016195581079724037)
  ·
    refine ⟨19242491815536671452448257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102626623016195581079724037 19242491815536671452448257)
    ·
      refine ⟨14431868861652503589336193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19242491815536671452448257 14431868861652503589336193)
      ·
        refine ⟨10823901646239377692002145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14431868861652503589336193 10823901646239377692002145)
        ·
          refine ⟨8117926234679533269001609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10823901646239377692002145 8117926234679533269001609)
          ·
            refine ⟨6088444676009649951751207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8117926234679533269001609 6088444676009649951751207)
            ·
              refine ⟨9132667014014474927626811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088444676009649951751207 9132667014014474927626811)
              ·
                refine ⟨13699000521021712391440217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132667014014474927626811 13699000521021712391440217)
                ·
                  refine ⟨10274250390766284293580163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13699000521021712391440217 10274250390766284293580163)
                  ·
                    refine ⟨15411375586149426440370245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274250390766284293580163 15411375586149426440370245)
                    ·
                      refine ⟨2889632922403017457569421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15411375586149426440370245 2889632922403017457569421)
                      ·
                        rfl

theorem cell23_5627540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_5627540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627540 prefixEnd_5627540 := by exact prefixLift 5627540
  have htrace : WordTrace (prefixWord ++ tailWord_5627540) baseStart_5627540 baseEnd_5627540 := by
    simpa [prefixWord, tailWord_5627540, baseEnd_5627540] using wordTrace_append hprefix tailTrace_5627540
  have hstable : (prefixWord ++ tailWord_5627540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627540).length < 2 ^ (prefixWord ++ tailWord_5627540).sum := by decide
  have hdescent : baseEnd_5627540 < baseStart_5627540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627543 : List Nat := [1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 3]
def baseStart_5627543 : Nat := 118140960795 + 5627543 * 2 ^ 59
def prefixEnd_5627543 : Nat := 4983230072969 + 3 ^ 40 * 5627543 * 2
def baseEnd_5627543 : Nat := 2889634462844980945831907

theorem tailTrace_5627543 : CollatzResearch.WordTrace tailWord_5627543 prefixEnd_5627543 2889634462844980945831907 := by
  unfold tailWord_5627543
  simp only [CollatzResearch.WordTrace]
  refine ⟨205253355451380293671807283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136835570300920195781204855 205253355451380293671807283)
  ·
    refine ⟨307880033177070440507710925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205253355451380293671807283 307880033177070440507710925)
    ·
      refine ⟨115455012441401415190391597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307880033177070440507710925 115455012441401415190391597)
      ·
        refine ⟨43295629665525530696396849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115455012441401415190391597 43295629665525530696396849)
        ·
          refine ⟨32471722249144148022297637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43295629665525530696396849 32471722249144148022297637)
          ·
            refine ⟨6088447921714527754180807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32471722249144148022297637 6088447921714527754180807)
            ·
              refine ⟨9132671882571791631271211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088447921714527754180807 9132671882571791631271211)
              ·
                refine ⟨13699007823857687446906817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9132671882571791631271211 13699007823857687446906817)
                ·
                  refine ⟨10274255867893265585180113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13699007823857687446906817 10274255867893265585180113)
                  ·
                    refine ⟨7705691900919949188885085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10274255867893265585180113 7705691900919949188885085)
                    ·
                      refine ⟨2889634462844980945831907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7705691900919949188885085 2889634462844980945831907)
                      ·
                        rfl

theorem cell23_5627543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_5627543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627543 prefixEnd_5627543 := by exact prefixLift 5627543
  have htrace : WordTrace (prefixWord ++ tailWord_5627543) baseStart_5627543 baseEnd_5627543 := by
    simpa [prefixWord, tailWord_5627543, baseEnd_5627543] using wordTrace_append hprefix tailTrace_5627543
  have hstable : (prefixWord ++ tailWord_5627543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627543).length < 2 ^ (prefixWord ++ tailWord_5627543).sum := by decide
  have hdescent : baseEnd_5627543 < baseStart_5627543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627550 : List Nat := [4, 3, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5627550 : Nat := 118140960795 + 5627550 * 2 ^ 59
def prefixEnd_5627550 : Nat := 4983230072969 + 3 ^ 40 * 5627550 * 2
def baseEnd_5627550 : Nat := 963212685736520806148125

theorem tailTrace_5627550 : CollatzResearch.WordTrace tailWord_5627550 prefixEnd_5627550 963212685736520806148125 := by
  unfold tailWord_5627550
  simp only [CollatzResearch.WordTrace]
  refine ⟨25656701345294366733414013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136835740508236622578208069 25656701345294366733414013)
  ·
    refine ⟨9621263004485387525030255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25656701345294366733414013 9621263004485387525030255)
    ·
      refine ⟨14431894506728081287545383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9621263004485387525030255 14431894506728081287545383)
      ·
        refine ⟨21647841760092121931318075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14431894506728081287545383 21647841760092121931318075)
        ·
          refine ⟨32471762640138182896977113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21647841760092121931318075 32471762640138182896977113)
          ·
            refine ⟨24353821980103637172732835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32471762640138182896977113 24353821980103637172732835)
            ·
              refine ⟨36530732970155455759099253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24353821980103637172732835 36530732970155455759099253)
              ·
                refine ⟨3424756215952073977415555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36530732970155455759099253 3424756215952073977415555)
                ·
                  refine ⟨5137134323928110966123333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3424756215952073977415555 5137134323928110966123333)
                  ·
                    refine ⟨963212685736520806148125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137134323928110966123333 963212685736520806148125)
                    ·
                      rfl

theorem cell23_5627550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5627550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627550 prefixEnd_5627550 := by exact prefixLift 5627550
  have htrace : WordTrace (prefixWord ++ tailWord_5627550) baseStart_5627550 baseEnd_5627550 := by
    simpa [prefixWord, tailWord_5627550, baseEnd_5627550] using wordTrace_append hprefix tailTrace_5627550
  have hstable : (prefixWord ++ tailWord_5627550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627550).length < 2 ^ (prefixWord ++ tailWord_5627550).sum := by decide
  have hdescent : baseEnd_5627550 < baseStart_5627550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627579 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4]
def baseStart_5627579 : Nat := 118140960795 + 5627579 * 2 ^ 59
def prefixEnd_5627579 : Nat := 4983230072969 + 3 ^ 40 * 5627579 * 2
def baseEnd_5627579 : Nat := 2889652948148542804981741

theorem tailTrace_5627579 : CollatzResearch.WordTrace tailWord_5627579 prefixEnd_5627579 2889652948148542804981741 := by
  unfold tailWord_5627579
  simp only [CollatzResearch.WordTrace]
  refine ⟨205254668479249871820117791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136836445652833247880078527 205254668479249871820117791)
  ·
    refine ⟨307882002718874807730176687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205254668479249871820117791 307882002718874807730176687)
    ·
      refine ⟨461823004078312211595265031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307882002718874807730176687 461823004078312211595265031)
      ·
        refine ⟨692734506117468317392897547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461823004078312211595265031 692734506117468317392897547)
        ·
          refine ⟨1039101759176202476089346321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692734506117468317392897547 1039101759176202476089346321)
          ·
            refine ⟨779326319382151857067009741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039101759176202476089346321 779326319382151857067009741)
            ·
              refine ⟨292247369768306946400128653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 779326319382151857067009741 292247369768306946400128653)
              ·
                refine ⟨109592763663115104900048245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292247369768306946400128653 109592763663115104900048245)
                ·
                  refine ⟨10274321593417041084379523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109592763663115104900048245 10274321593417041084379523)
                  ·
                    refine ⟨15411482390125561626569285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274321593417041084379523 15411482390125561626569285)
                    ·
                      refine ⟨2889652948148542804981741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15411482390125561626569285 2889652948148542804981741)
                      ·
                        rfl

theorem cell23_5627579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 4].length) (baseStart_5627579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627579 prefixEnd_5627579 := by exact prefixLift 5627579
  have htrace : WordTrace (prefixWord ++ tailWord_5627579) baseStart_5627579 baseEnd_5627579 := by
    simpa [prefixWord, tailWord_5627579, baseEnd_5627579] using wordTrace_append hprefix tailTrace_5627579
  have hstable : (prefixWord ++ tailWord_5627579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627579).length < 2 ^ (prefixWord ++ tailWord_5627579).sum := by decide
  have hdescent : baseEnd_5627579 < baseStart_5627579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627599 : List Nat := [1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3]
def baseStart_5627599 : Nat := 118140960795 + 5627599 * 2 ^ 59
def prefixEnd_5627599 : Nat := 4983230072969 + 3 ^ 40 * 5627599 * 2
def baseEnd_5627599 : Nat := 2889663217761632726731649

theorem tailTrace_5627599 : CollatzResearch.WordTrace tailWord_5627599 prefixEnd_5627599 2889663217761632726731649 := by
  unfold tailWord_5627599
  simp only [CollatzResearch.WordTrace]
  refine ⟨205255397939177415235845851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136836931959451610157230567 205255397939177415235845851)
  ·
    refine ⟨307883096908766122853768777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205255397939177415235845851 307883096908766122853768777)
    ·
      refine ⟨230912322681574592140326583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307883096908766122853768777 230912322681574592140326583)
      ·
        refine ⟨346368484022361888210489875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230912322681574592140326583 346368484022361888210489875)
        ·
          refine ⟨519552726033542832315734813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346368484022361888210489875 519552726033542832315734813)
          ·
            refine ⟨194832272262578562118400555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519552726033542832315734813 194832272262578562118400555)
            ·
              refine ⟨292248408393867843177600833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194832272262578562118400555 292248408393867843177600833)
              ·
                refine ⟨219186306295400882383200625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292248408393867843177600833 219186306295400882383200625)
                ·
                  refine ⟨164389729721550661787400469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219186306295400882383200625 164389729721550661787400469)
                  ·
                    refine ⟨7705768580697687271284397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 164389729721550661787400469 7705768580697687271284397)
                    ·
                      refine ⟨2889663217761632726731649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7705768580697687271284397 2889663217761632726731649)
                      ·
                        rfl

theorem cell23_5627599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_5627599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627599 prefixEnd_5627599 := by exact prefixLift 5627599
  have htrace : WordTrace (prefixWord ++ tailWord_5627599) baseStart_5627599 baseEnd_5627599 := by
    simpa [prefixWord, tailWord_5627599, baseEnd_5627599] using wordTrace_append hprefix tailTrace_5627599
  have hstable : (prefixWord ++ tailWord_5627599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627599).length < 2 ^ (prefixWord ++ tailWord_5627599).sum := by decide
  have hdescent : baseEnd_5627599 < baseStart_5627599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627659 : List Nat := [1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5]
def baseStart_5627659 : Nat := 118140960795 + 5627659 * 2 ^ 59
def prefixEnd_5627659 : Nat := 4983230072969 + 3 ^ 40 * 5627659 * 2
def baseEnd_5627659 : Nat := 2889694026600902491981373

theorem tailTrace_5627659 : CollatzResearch.WordTrace tailWord_5627659 prefixEnd_5627659 2889694026600902491981373 := by
  unfold tailWord_5627659
  simp only [CollatzResearch.WordTrace]
  refine ⟨205257586318960045483030031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136838390879306696988686687 205257586318960045483030031)
  ·
    refine ⟨307886379478440068224545047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205257586318960045483030031 307886379478440068224545047)
    ·
      refine ⟨461829569217660102336817571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307886379478440068224545047 461829569217660102336817571)
      ·
        refine ⟨692744353826490153505226357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461829569217660102336817571 692744353826490153505226357)
        ·
          refine ⟨64944783171233451891114971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 692744353826490153505226357 64944783171233451891114971)
          ·
            refine ⟨97417174756850177836672457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64944783171233451891114971 97417174756850177836672457)
            ·
              refine ⟨73062881067637633377504343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97417174756850177836672457 73062881067637633377504343)
              ·
                refine ⟨109594321601456450066256515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73062881067637633377504343 109594321601456450066256515)
                ·
                  refine ⟨164391482402184675099384773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109594321601456450066256515 164391482402184675099384773)
                  ·
                    refine ⟨30823402950409626581134645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 164391482402184675099384773 30823402950409626581134645)
                    ·
                      refine ⟨2889694026600902491981373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30823402950409626581134645 2889694026600902491981373)
                      ·
                        rfl

theorem cell23_5627659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_5627659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627659 prefixEnd_5627659 := by exact prefixLift 5627659
  have htrace : WordTrace (prefixWord ++ tailWord_5627659) baseStart_5627659 baseEnd_5627659 := by
    simpa [prefixWord, tailWord_5627659, baseEnd_5627659] using wordTrace_append hprefix tailTrace_5627659
  have hstable : (prefixWord ++ tailWord_5627659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627659).length < 2 ^ (prefixWord ++ tailWord_5627659).sum := by decide
  have hdescent : baseEnd_5627659 < baseStart_5627659 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627661 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 1, 5]
def baseStart_5627661 : Nat := 118140960795 + 5627661 * 2 ^ 59
def prefixEnd_5627661 : Nat := 4983230072969 + 3 ^ 40 * 5627661 * 2
def baseEnd_5627661 : Nat := 963231684520737161385455

theorem tailTrace_5627661 : CollatzResearch.WordTrace tailWord_5627661 prefixEnd_5627661 963231684520737161385455 := by
  unfold tailWord_5627661
  simp only [CollatzResearch.WordTrace]
  refine ⟨205257659264952799824602837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136838439509968533216401891 205257659264952799824602837)
  ·
    refine ⟨4810726389022331245889129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 205257659264952799824602837 4810726389022331245889129)
    ·
      refine ⟨3608044791766748434416847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4810726389022331245889129 3608044791766748434416847)
      ·
        refine ⟨5412067187650122651625271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3608044791766748434416847 5412067187650122651625271)
        ·
          refine ⟨8118100781475183977437907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412067187650122651625271 8118100781475183977437907)
          ·
            refine ⟨12177151172212775966156861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118100781475183977437907 12177151172212775966156861)
            ·
              refine ⟨4566431689579790987308823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12177151172212775966156861 4566431689579790987308823)
              ·
                refine ⟨6849647534369686480963235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566431689579790987308823 6849647534369686480963235)
                ·
                  refine ⟨10274471301554529721444853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849647534369686480963235 10274471301554529721444853)
                  ·
                    refine ⟨963231684520737161385455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10274471301554529721444853 963231684520737161385455)
                    ·
                      rfl

theorem cell23_5627661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_5627661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627661 prefixEnd_5627661 := by exact prefixLift 5627661
  have htrace : WordTrace (prefixWord ++ tailWord_5627661) baseStart_5627661 baseEnd_5627661 := by
    simpa [prefixWord, tailWord_5627661, baseEnd_5627661] using wordTrace_append hprefix tailTrace_5627661
  have hstable : (prefixWord ++ tailWord_5627661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627661).length < 2 ^ (prefixWord ++ tailWord_5627661).sum := by decide
  have hdescent : baseEnd_5627661 < baseStart_5627661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627680 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5627680 : Nat := 118140960795 + 5627680 * 2 ^ 59
def prefixEnd_5627680 : Nat := 4983230072969 + 3 ^ 40 * 5627680 * 2
def baseEnd_5627680 : Nat := 2889704809694646909818777

theorem tailTrace_5627680 : CollatzResearch.WordTrace tailWord_5627680 prefixEnd_5627680 2889704809694646909818777 := by
  unfold tailWord_5627680
  simp only [CollatzResearch.WordTrace]
  refine ⟨102629176125941983034772247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136838901501255977379696329 102629176125941983034772247)
  ·
    refine ⟨153943764188912974552158371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102629176125941983034772247 153943764188912974552158371)
    ·
      refine ⟨230915646283369461828237557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153943764188912974552158371 230915646283369461828237557)
      ·
        refine ⟨21648341839065887046397271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230915646283369461828237557 21648341839065887046397271)
        ·
          refine ⟨32472512758598830569595907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21648341839065887046397271 32472512758598830569595907)
          ·
            refine ⟨48708769137898245854393861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32472512758598830569595907 48708769137898245854393861)
            ·
              refine ⟨9132894213355921097698849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48708769137898245854393861 9132894213355921097698849)
              ·
                refine ⟨6849670660016940823274137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9132894213355921097698849 6849670660016940823274137)
                ·
                  refine ⟨5137252995012705617455603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6849670660016940823274137 5137252995012705617455603)
                  ·
                    refine ⟨7705879492519058426183405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5137252995012705617455603 7705879492519058426183405)
                    ·
                      refine ⟨2889704809694646909818777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7705879492519058426183405 2889704809694646909818777)
                      ·
                        rfl

theorem cell23_5627680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5627680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627680 prefixEnd_5627680 := by exact prefixLift 5627680
  have htrace : WordTrace (prefixWord ++ tailWord_5627680) baseStart_5627680 baseEnd_5627680 := by
    simpa [prefixWord, tailWord_5627680, baseEnd_5627680] using wordTrace_append hprefix tailTrace_5627680
  have hstable : (prefixWord ++ tailWord_5627680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627680).length < 2 ^ (prefixWord ++ tailWord_5627680).sum := by decide
  have hdescent : baseEnd_5627680 < baseStart_5627680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627724 : List Nat := [2, 2, 1, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_5627724 : Nat := 118140960795 + 5627724 * 2 ^ 59
def prefixEnd_5627724 : Nat := 4983230072969 + 3 ^ 40 * 5627724 * 2
def baseEnd_5627724 : Nat := 2889727402843444737668575

theorem tailTrace_5627724 : CollatzResearch.WordTrace tailWord_5627724 prefixEnd_5627724 2889727402843444737668575 := by
  unfold tailWord_5627724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102629978531862280792073113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136839971375816374389430817 102629978531862280792073113)
  ·
    refine ⟨76972483898896710594054835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102629978531862280792073113 76972483898896710594054835)
    ·
      refine ⟨115458725848345065891082253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76972483898896710594054835 115458725848345065891082253)
      ·
        refine ⟨43297022193129399709155845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115458725848345065891082253 43297022193129399709155845)
        ·
          refine ⟨8118191661211762445466721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43297022193129399709155845 8118191661211762445466721)
          ·
            refine ⟨6088643745908821834100041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118191661211762445466721 6088643745908821834100041)
            ·
              refine ⟨4566482809431616375575031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088643745908821834100041 4566482809431616375575031)
              ·
                refine ⟨6849724214147424563362547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566482809431616375575031 6849724214147424563362547)
                ·
                  refine ⟨10274586321221136845043821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849724214147424563362547 10274586321221136845043821)
                  ·
                    refine ⟨3852969870457926316891433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10274586321221136845043821 3852969870457926316891433)
                    ·
                      refine ⟨2889727402843444737668575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852969870457926316891433 2889727402843444737668575)
                      ·
                        rfl

theorem cell23_5627724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_5627724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627724 prefixEnd_5627724 := by exact prefixLift 5627724
  have htrace : WordTrace (prefixWord ++ tailWord_5627724) baseStart_5627724 baseEnd_5627724 := by
    simpa [prefixWord, tailWord_5627724, baseEnd_5627724] using wordTrace_append hprefix tailTrace_5627724
  have hstable : (prefixWord ++ tailWord_5627724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627724).length < 2 ^ (prefixWord ++ tailWord_5627724).sum := by decide
  have hdescent : baseEnd_5627724 < baseStart_5627724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627743 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 5]
def baseStart_5627743 : Nat := 118140960795 + 5627743 * 2 ^ 59
def prefixEnd_5627743 : Nat := 4983230072969 + 3 ^ 40 * 5627743 * 2
def baseEnd_5627743 : Nat := 321081906552875573703443

theorem tailTrace_5627743 : CollatzResearch.WordTrace tailWord_5627743 prefixEnd_5627743 321081906552875573703443 := by
  unfold tailWord_5627743
  simp only [CollatzResearch.WordTrace]
  refine ⟨205260650050655727829087883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136840433367103818552725255 205260650050655727829087883)
  ·
    refine ⟨307890975075983591743631825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205260650050655727829087883 307890975075983591743631825)
    ·
      refine ⟨230918231306987693807723869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307890975075983591743631825 230918231306987693807723869)
      ·
        refine ⟨86594336740120385177896451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230918231306987693807723869 86594336740120385177896451)
        ·
          refine ⟨129891505110180577766844677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86594336740120385177896451 129891505110180577766844677)
          ·
            refine ⟨24354657208158858331283377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129891505110180577766844677 24354657208158858331283377)
            ·
              refine ⟨18265992906119143748462533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24354657208158858331283377 18265992906119143748462533)
              ·
                refine ⟨3424873669897339452836725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18265992906119143748462533 3424873669897339452836725)
                ·
                  refine ⟨321081906552875573703443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3424873669897339452836725 321081906552875573703443)
                  ·
                    rfl

theorem cell23_5627743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 5].length) (baseStart_5627743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627743 prefixEnd_5627743 := by exact prefixLift 5627743
  have htrace : WordTrace (prefixWord ++ tailWord_5627743) baseStart_5627743 baseEnd_5627743 := by
    simpa [prefixWord, tailWord_5627743, baseEnd_5627743] using wordTrace_append hprefix tailTrace_5627743
  have hstable : (prefixWord ++ tailWord_5627743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627743).length < 2 ^ (prefixWord ++ tailWord_5627743).sum := by decide
  have hdescent : baseEnd_5627743 < baseStart_5627743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627754 : List Nat := [3, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5627754 : Nat := 118140960795 + 5627754 * 2 ^ 59
def prefixEnd_5627754 : Nat := 4983230072969 + 3 ^ 40 * 5627754 * 2
def baseEnd_5627754 : Nat := 2889742807263079620293437

theorem tailTrace_5627754 : CollatzResearch.WordTrace tailWord_5627754 prefixEnd_5627754 2889742807263079620293437 := by
  unfold tailWord_5627754
  simp only [CollatzResearch.WordTrace]
  refine ⟨51315262813403969176934579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136840700835743917805158877 51315262813403969176934579)
  ·
    refine ⟨76972894220105953765401869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51315262813403969176934579 76972894220105953765401869)
    ·
      refine ⟨28864835332539732662025701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76972894220105953765401869 28864835332539732662025701)
      ·
        refine ⟨5412156624851199874129819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28864835332539732662025701 5412156624851199874129819)
        ·
          refine ⟨8118234937276799811194729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412156624851199874129819 8118234937276799811194729)
          ·
            refine ⟨6088676202957599858396047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118234937276799811194729 6088676202957599858396047)
            ·
              refine ⟨9133014304436399787594071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088676202957599858396047 9133014304436399787594071)
              ·
                refine ⟨13699521456654599681391107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133014304436399787594071 13699521456654599681391107)
                ·
                  refine ⟨20549282184981899522086661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13699521456654599681391107 20549282184981899522086661)
                  ·
                    refine ⟨3852990409684106160391249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20549282184981899522086661 3852990409684106160391249)
                    ·
                      refine ⟨2889742807263079620293437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3852990409684106160391249 2889742807263079620293437)
                      ·
                        rfl

theorem cell23_5627754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5627754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627754 prefixEnd_5627754 := by exact prefixLift 5627754
  have htrace : WordTrace (prefixWord ++ tailWord_5627754) baseStart_5627754 baseEnd_5627754 := by
    simpa [prefixWord, tailWord_5627754, baseEnd_5627754] using wordTrace_append hprefix tailTrace_5627754
  have hstable : (prefixWord ++ tailWord_5627754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627754).length < 2 ^ (prefixWord ++ tailWord_5627754).sum := by decide
  have hdescent : baseEnd_5627754 < baseStart_5627754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627756 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_5627756 : Nat := 118140960795 + 5627756 * 2 ^ 59
def prefixEnd_5627756 : Nat := 4983230072969 + 3 ^ 40 * 5627756 * 2
def baseEnd_5627756 : Nat := 963247944741462870822809

theorem tailTrace_5627756 : CollatzResearch.WordTrace tailWord_5627756 prefixEnd_5627756 963247944741462870822809 := by
  unfold tailWord_5627756
  simp only [CollatzResearch.WordTrace]
  refine ⟨102630562099804315524655561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136840749466405754032874081 102630562099804315524655561)
  ·
    refine ⟨76972921574853236643491671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102630562099804315524655561 76972921574853236643491671)
    ·
      refine ⟨115459382362279854965237507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76972921574853236643491671 115459382362279854965237507)
      ·
        refine ⟨173189073543419782447856261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115459382362279854965237507 173189073543419782447856261)
        ·
          refine ⟨32472951289391209208973049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173189073543419782447856261 32472951289391209208973049)
          ·
            refine ⟨24354713467043406906729787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32472951289391209208973049 24354713467043406906729787)
            ·
              refine ⟨36532070200565110360094681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24354713467043406906729787 36532070200565110360094681)
              ·
                refine ⟨27399052650423832770071011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36532070200565110360094681 27399052650423832770071011)
                ·
                  refine ⟨41098578975635749155106517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27399052650423832770071011 41098578975635749155106517)
                  ·
                    refine ⟨963247944741462870822809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41098578975635749155106517 963247944741462870822809)
                    ·
                      rfl

theorem cell23_5627756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_5627756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627756 prefixEnd_5627756 := by exact prefixLift 5627756
  have htrace : WordTrace (prefixWord ++ tailWord_5627756) baseStart_5627756 baseEnd_5627756 := by
    simpa [prefixWord, tailWord_5627756, baseEnd_5627756] using wordTrace_append hprefix tailTrace_5627756
  have hstable : (prefixWord ++ tailWord_5627756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627756).length < 2 ^ (prefixWord ++ tailWord_5627756).sum := by decide
  have hdescent : baseEnd_5627756 < baseStart_5627756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627776 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_5627776 : Nat := 118140960795 + 5627776 * 2 ^ 59
def prefixEnd_5627776 : Nat := 4983230072969 + 3 ^ 40 * 5627776 * 2
def baseEnd_5627776 : Nat := 2889754103837478534218335

theorem tailTrace_5627776 : CollatzResearch.WordTrace tailWord_5627776 prefixEnd_5627776 2889754103837478534218335 := by
  unfold tailWord_5627776
  simp only [CollatzResearch.WordTrace]
  refine ⟨102630926829768087232519591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136841235773024116310026121 102630926829768087232519591)
  ·
    refine ⟨153946390244652130848779387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102630926829768087232519591 153946390244652130848779387)
    ·
      refine ⟨230919585366978196273169081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153946390244652130848779387 230919585366978196273169081)
      ·
        refine ⟨173189689025233647204876811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230919585366978196273169081 173189689025233647204876811)
        ·
          refine ⟨259784533537850470807315217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173189689025233647204876811 259784533537850470807315217)
          ·
            refine ⟨194838400153387853105486413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259784533537850470807315217 194838400153387853105486413)
            ·
              refine ⟨73064400057520444914557405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194838400153387853105486413 73064400057520444914557405)
              ·
                refine ⟨27399150021570166842959027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73064400057520444914557405 27399150021570166842959027)
                ·
                  refine ⟨41098725032355250264438541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27399150021570166842959027 41098725032355250264438541)
                  ·
                    refine ⟨15412021887133218849164453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41098725032355250264438541 15412021887133218849164453)
                    ·
                      refine ⟨2889754103837478534218335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15412021887133218849164453 2889754103837478534218335)
                      ·
                        rfl

theorem cell23_5627776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_5627776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627776 prefixEnd_5627776 := by exact prefixLift 5627776
  have htrace : WordTrace (prefixWord ++ tailWord_5627776) baseStart_5627776 baseEnd_5627776 := by
    simpa [prefixWord, tailWord_5627776, baseEnd_5627776] using wordTrace_append hprefix tailTrace_5627776
  have hstable : (prefixWord ++ tailWord_5627776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627776).length < 2 ^ (prefixWord ++ tailWord_5627776).sum := by decide
  have hdescent : baseEnd_5627776 < baseStart_5627776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627793 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_5627793 : Nat := 118140960795 + 5627793 * 2 ^ 59
def prefixEnd_5627793 : Nat := 4983230072969 + 3 ^ 40 * 5627793 * 2
def baseEnd_5627793 : Nat := 2889762833008604967705757

theorem tailTrace_5627793 : CollatzResearch.WordTrace tailWord_5627793 prefixEnd_5627793 2889762833008604967705757 := by
  unfold tailWord_5627793
  simp only [CollatzResearch.WordTrace]
  refine ⟨205262473700474586368408033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136841649133649724245605355 205262473700474586368408033)
  ·
    refine ⟨153946855275355939776306025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205262473700474586368408033 153946855275355939776306025)
    ·
      refine ⟨115460141456516954832229519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153946855275355939776306025 115460141456516954832229519)
      ·
        refine ⟨173190212184775432248344279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115460141456516954832229519 173190212184775432248344279)
        ·
          refine ⟨259785318277163148372516419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173190212184775432248344279 259785318277163148372516419)
          ·
            refine ⟨389677977415744722558774629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259785318277163148372516419 389677977415744722558774629)
            ·
              refine ⟨73064620765452135479770243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 389677977415744722558774629 73064620765452135479770243)
              ·
                refine ⟨109596931148178203219655365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73064620765452135479770243 109596931148178203219655365)
                ·
                  refine ⟨20549424590283413103685381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109596931148178203219655365 20549424590283413103685381)
                  ·
                    refine ⟨3853017110678139956941009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20549424590283413103685381 3853017110678139956941009)
                    ·
                      refine ⟨2889762833008604967705757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853017110678139956941009 2889762833008604967705757)
                      ·
                        rfl

theorem cell23_5627793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_5627793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627793 prefixEnd_5627793 := by exact prefixLift 5627793
  have htrace : WordTrace (prefixWord ++ tailWord_5627793) baseStart_5627793 baseEnd_5627793 := by
    simpa [prefixWord, tailWord_5627793, baseEnd_5627793] using wordTrace_append hprefix tailTrace_5627793
  have hstable : (prefixWord ++ tailWord_5627793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627793).length < 2 ^ (prefixWord ++ tailWord_5627793).sum := by decide
  have hdescent : baseEnd_5627793 < baseStart_5627793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627800 : List Nat := [2, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5627800 : Nat := 118140960795 + 5627800 * 2 ^ 59
def prefixEnd_5627800 : Nat := 4983230072969 + 3 ^ 40 * 5627800 * 2
def baseEnd_5627800 : Nat := 2889766427373186440318225

theorem tailTrace_5627800 : CollatzResearch.WordTrace tailWord_5627800 prefixEnd_5627800 2889766427373186440318225 := by
  unfold tailWord_5627800
  simp only [CollatzResearch.WordTrace]
  refine ⟨102631364505724613281956427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136841819340966151042608569 102631364505724613281956427)
  ·
    refine ⟨153947046758586919922934641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102631364505724613281956427 153947046758586919922934641)
    ·
      refine ⟨115460285068940189942200981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153947046758586919922934641 115460285068940189942200981)
      ·
        refine ⟨5412200862606571403540671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115460285068940189942200981 5412200862606571403540671)
        ·
          refine ⟨8118301293909857105311007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412200862606571403540671 8118301293909857105311007)
          ·
            refine ⟨12177451940864785657966511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118301293909857105311007 12177451940864785657966511)
            ·
              refine ⟨18266177911297178486949767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12177451940864785657966511 18266177911297178486949767)
              ·
                refine ⟨27399266866945767730424651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18266177911297178486949767 27399266866945767730424651)
                ·
                  refine ⟨41098900300418651595636977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27399266866945767730424651 41098900300418651595636977)
                  ·
                    refine ⟨30824175225313988696727733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41098900300418651595636977 30824175225313988696727733)
                    ·
                      refine ⟨2889766427373186440318225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30824175225313988696727733 2889766427373186440318225)
                      ·
                        rfl

theorem cell23_5627800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5627800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627800 prefixEnd_5627800 := by exact prefixLift 5627800
  have htrace : WordTrace (prefixWord ++ tailWord_5627800) baseStart_5627800 baseEnd_5627800 := by
    simpa [prefixWord, tailWord_5627800, baseEnd_5627800] using wordTrace_append hprefix tailTrace_5627800
  have hstable : (prefixWord ++ tailWord_5627800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627800).length < 2 ^ (prefixWord ++ tailWord_5627800).sum := by decide
  have hdescent : baseEnd_5627800 < baseStart_5627800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627897 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_5627897 : Nat := 118140960795 + 5627897 * 2 ^ 59
def prefixEnd_5627897 : Nat := 4983230072969 + 3 ^ 40 * 5627897 * 2
def baseEnd_5627897 : Nat := 963272078332224186935093

theorem tailTrace_5627897 : CollatzResearch.WordTrace tailWord_5627897 prefixEnd_5627897 963272078332224186935093 := by
  unfold tailWord_5627897
  simp only [CollatzResearch.WordTrace]
  refine ⟨205266266892097812130193945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136844177928065208086795963 205266266892097812130193945)
  ·
    refine ⟨153949700169073359097645459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205266266892097812130193945 153949700169073359097645459)
    ·
      refine ⟨230924550253610038646468189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153949700169073359097645459 230924550253610038646468189)
      ·
        refine ⟨86596706345103764492425571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230924550253610038646468189 86596706345103764492425571)
        ·
          refine ⟨129895059517655646738638357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86596706345103764492425571 129895059517655646738638357)
          ·
            refine ⟨6088830914890108440873673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129895059517655646738638357 6088830914890108440873673)
            ·
              refine ⟨4566623186167581330655255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088830914890108440873673 4566623186167581330655255)
              ·
                refine ⟨6849934779251371995982883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566623186167581330655255 6849934779251371995982883)
                ·
                  refine ⟨10274902168877057993974325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849934779251371995982883 10274902168877057993974325)
                  ·
                    refine ⟨963272078332224186935093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10274902168877057993974325 963272078332224186935093)
                    ·
                      rfl

theorem cell23_5627897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_5627897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627897 prefixEnd_5627897 := by exact prefixLift 5627897
  have htrace : WordTrace (prefixWord ++ tailWord_5627897) baseStart_5627897 baseEnd_5627897 := by
    simpa [prefixWord, tailWord_5627897, baseEnd_5627897] using wordTrace_append hprefix tailTrace_5627897
  have hstable : (prefixWord ++ tailWord_5627897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627897).length < 2 ^ (prefixWord ++ tailWord_5627897).sum := by decide
  have hdescent : baseEnd_5627897 < baseStart_5627897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627900 : List Nat := [2, 2, 2, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_5627900 : Nat := 118140960795 + 5627900 * 2 ^ 59
def prefixEnd_5627900 : Nat := 4983230072969 + 3 ^ 40 * 5627900 * 2
def baseEnd_5627900 : Nat := 2889817775438636049067765

theorem tailTrace_5627900 : CollatzResearch.WordTrace tailWord_5627900 prefixEnd_5627900 2889817775438636049067765 := by
  unfold tailWord_5627900
  simp only [CollatzResearch.WordTrace]
  refine ⟨102633188155543471821276577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136844250874057962428368769 102633188155543471821276577)
  ·
    refine ⟨76974891116657603865957433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102633188155543471821276577 76974891116657603865957433)
    ·
      refine ⟨57731168337493202899468075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76974891116657603865957433 57731168337493202899468075)
      ·
        refine ⟨86596752506239804349202113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57731168337493202899468075 86596752506239804349202113)
        ·
          refine ⟨64947564379679853261901585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86596752506239804349202113 64947564379679853261901585)
          ·
            refine ⟨48710673284759889946426189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64947564379679853261901585 48710673284759889946426189)
            ·
              refine ⟨18266502481784958729909821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48710673284759889946426189 18266502481784958729909821)
              ·
                refine ⟨6849938430669359523716183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18266502481784958729909821 6849938430669359523716183)
                ·
                  refine ⟨10274907646004039285574275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6849938430669359523716183 10274907646004039285574275)
                  ·
                    refine ⟨15412361469006058928361413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10274907646004039285574275 15412361469006058928361413)
                    ·
                      refine ⟨2889817775438636049067765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15412361469006058928361413 2889817775438636049067765)
                      ·
                        rfl

theorem cell23_5627900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_5627900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627900 prefixEnd_5627900 := by exact prefixLift 5627900
  have htrace : WordTrace (prefixWord ++ tailWord_5627900) baseStart_5627900 baseEnd_5627900 := by
    simpa [prefixWord, tailWord_5627900, baseEnd_5627900] using wordTrace_append hprefix tailTrace_5627900
  have hstable : (prefixWord ++ tailWord_5627900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627900).length < 2 ^ (prefixWord ++ tailWord_5627900).sum := by decide
  have hdescent : baseEnd_5627900 < baseStart_5627900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627927 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 1, 6]
def baseStart_5627927 : Nat := 118140960795 + 5627927 * 2 ^ 59
def prefixEnd_5627927 : Nat := 4983230072969 + 3 ^ 40 * 5627927 * 2
def baseEnd_5627927 : Nat := 963277213138769147810047

theorem tailTrace_5627927 : CollatzResearch.WordTrace tailWord_5627927 prefixEnd_5627927 963277213138769147810047 := by
  unfold tailWord_5627927
  simp only [CollatzResearch.WordTrace]
  refine ⟨205267361081989127253786035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136844907387992751502524023 205267361081989127253786035)
  ·
    refine ⟨307901041622983690880679053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205267361081989127253786035 307901041622983690880679053)
    ·
      refine ⟨115462890608618884080254645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307901041622983690880679053 115462890608618884080254645)
      ·
        refine ⟨10824645994558020382523873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115462890608618884080254645 10824645994558020382523873)
        ·
          refine ⟨8118484495918515286892905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824645994558020382523873 8118484495918515286892905)
          ·
            refine ⟨6088863371938886465169679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118484495918515286892905 6088863371938886465169679)
            ·
              refine ⟨9133295057908329697754519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6088863371938886465169679 9133295057908329697754519)
              ·
                refine ⟨13699942586862494546631779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133295057908329697754519 13699942586862494546631779)
                ·
                  refine ⟨20549913880293741819947669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13699942586862494546631779 20549913880293741819947669)
                  ·
                    refine ⟨963277213138769147810047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20549913880293741819947669 963277213138769147810047)
                    ·
                      rfl

theorem cell23_5627927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 6].length) (baseStart_5627927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627927 prefixEnd_5627927 := by exact prefixLift 5627927
  have htrace : WordTrace (prefixWord ++ tailWord_5627927) baseStart_5627927 baseEnd_5627927 := by
    simpa [prefixWord, tailWord_5627927, baseEnd_5627927] using wordTrace_append hprefix tailTrace_5627927
  have hstable : (prefixWord ++ tailWord_5627927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627927).length < 2 ^ (prefixWord ++ tailWord_5627927).sum := by decide
  have hdescent : baseEnd_5627927 < baseStart_5627927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627930 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_5627930 : Nat := 118140960795 + 5627930 * 2 ^ 59
def prefixEnd_5627930 : Nat := 4983230072969 + 3 ^ 40 * 5627930 * 2
def baseEnd_5627930 : Nat := 2889833179858270931692627

theorem tailTrace_5627930 : CollatzResearch.WordTrace tailWord_5627930 prefixEnd_5627930 2889833179858270931692627 := by
  unfold tailWord_5627930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51316867625244564691536311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136844980333985505844096829 51316867625244564691536311)
  ·
    refine ⟨76975301437866847037304467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51316867625244564691536311 76975301437866847037304467)
    ·
      refine ⟨115462952156800270555956701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76975301437866847037304467 115462952156800270555956701)
      ·
        refine ⟨43298607058800101458483763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115462952156800270555956701 43298607058800101458483763)
        ·
          refine ⟨64947910588200152187725645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43298607058800101458483763 64947910588200152187725645)
          ·
            refine ⟨24355466470575057070397117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64947910588200152187725645 24355466470575057070397117)
            ·
              refine ⟨9133299926465646401398919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24355466470575057070397117 9133299926465646401398919)
              ·
                refine ⟨13699949889698469602098379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133299926465646401398919 13699949889698469602098379)
                ·
                  refine ⟨20549924834547704403147569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13699949889698469602098379 20549924834547704403147569)
                  ·
                    refine ⟨15412443625910778302360677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20549924834547704403147569 15412443625910778302360677)
                    ·
                      refine ⟨2889833179858270931692627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15412443625910778302360677 2889833179858270931692627)
                      ·
                        rfl

theorem cell23_5627930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_5627930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627930 prefixEnd_5627930 := by exact prefixLift 5627930
  have htrace : WordTrace (prefixWord ++ tailWord_5627930) baseStart_5627930 baseEnd_5627930 := by
    simpa [prefixWord, tailWord_5627930, baseEnd_5627930] using wordTrace_append hprefix tailTrace_5627930
  have hstable : (prefixWord ++ tailWord_5627930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627930).length < 2 ^ (prefixWord ++ tailWord_5627930).sum := by decide
  have hdescent : baseEnd_5627930 < baseStart_5627930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627940 : List Nat := [2, 3, 1, 4, 2, 1, 1, 9]
def baseStart_5627940 : Nat := 118140960795 + 5627940 * 2 ^ 59
def prefixEnd_5627940 : Nat := 4983230072969 + 3 ^ 40 * 5627940 * 2
def baseEnd_5627940 : Nat := 107031048691289477502503

theorem tailTrace_5627940 : CollatzResearch.WordTrace tailWord_5627940 prefixEnd_5627940 107031048691289477502503 := by
  unfold tailWord_5627940
  simp only [CollatzResearch.WordTrace]
  refine ⟨102633917615471015237004637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136845223487294686982672849 102633917615471015237004637)
  ·
    refine ⟨38487719105801630713876739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102633917615471015237004637 38487719105801630713876739)
    ·
      refine ⟨57731578658702446070815109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38487719105801630713876739 57731578658702446070815109)
      ·
        refine ⟨10824670998506708638277833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57731578658702446070815109 10824670998506708638277833)
        ·
          refine ⟨8118503248880031478708375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10824670998506708638277833 8118503248880031478708375)
          ·
            refine ⟨12177754873320047218062563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118503248880031478708375 12177754873320047218062563)
            ·
              refine ⟨18266632309980070827093845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12177754873320047218062563 18266632309980070827093845)
              ·
                refine ⟨107031048691289477502503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18266632309980070827093845 107031048691289477502503)
                ·
                  rfl

theorem cell23_5627940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 9].length) (baseStart_5627940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627940 prefixEnd_5627940 := by exact prefixLift 5627940
  have htrace : WordTrace (prefixWord ++ tailWord_5627940) baseStart_5627940 baseEnd_5627940 := by
    simpa [prefixWord, tailWord_5627940, baseEnd_5627940] using wordTrace_append hprefix tailTrace_5627940
  have hstable : (prefixWord ++ tailWord_5627940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627940).length < 2 ^ (prefixWord ++ tailWord_5627940).sum := by decide
  have hdescent : baseEnd_5627940 < baseStart_5627940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627973 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 4]
def baseStart_5627973 : Nat := 118140960795 + 5627973 * 2 ^ 59
def prefixEnd_5627973 : Nat := 4983230072969 + 3 ^ 40 * 5627973 * 2
def baseEnd_5627973 : Nat := 2889855259526414263454929

theorem tailTrace_5627973 : CollatzResearch.WordTrace tailWord_5627973 prefixEnd_5627973 2889855259526414263454929 := by
  unfold tailWord_5627973
  simp only [CollatzResearch.WordTrace]
  refine ⟨205269038839822477109960573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136846025893214984739973715 205269038839822477109960573)
  ·
    refine ⟨76975889564933428916235215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205269038839822477109960573 76975889564933428916235215)
    ·
      refine ⟨115463834347400143374352823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76975889564933428916235215 115463834347400143374352823)
      ·
        refine ⟨173195751521100215061529235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115463834347400143374352823 173195751521100215061529235)
        ·
          refine ⟨259793627281650322592293853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173195751521100215061529235 259793627281650322592293853)
          ·
            refine ⟨97422610230618870972110195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259793627281650322592293853 97422610230618870972110195)
            ·
              refine ⟨146133915345928306458165293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97422610230618870972110195 146133915345928306458165293)
              ·
                refine ⟨54800218254723114921811985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146133915345928306458165293 54800218254723114921811985)
                ·
                  refine ⟨41100163691042336191358989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54800218254723114921811985 41100163691042336191358989)
                  ·
                    refine ⟨15412561384140876071759621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41100163691042336191358989 15412561384140876071759621)
                    ·
                      refine ⟨2889855259526414263454929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15412561384140876071759621 2889855259526414263454929)
                      ·
                        rfl

theorem cell23_5627973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_5627973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627973 prefixEnd_5627973 := by exact prefixLift 5627973
  have htrace : WordTrace (prefixWord ++ tailWord_5627973) baseStart_5627973 baseEnd_5627973 := by
    simpa [prefixWord, tailWord_5627973, baseEnd_5627973] using wordTrace_append hprefix tailTrace_5627973
  have hstable : (prefixWord ++ tailWord_5627973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627973).length < 2 ^ (prefixWord ++ tailWord_5627973).sum := by decide
  have hdescent : baseEnd_5627973 < baseStart_5627973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5627993 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_5627993 : Nat := 118140960795 + 5627993 * 2 ^ 59
def prefixEnd_5627993 : Nat := 4983230072969 + 3 ^ 40 * 5627993 * 2
def baseEnd_5627993 : Nat := 2889865529139504185204837

theorem tailTrace_5627993 : CollatzResearch.WordTrace tailWord_5627993 prefixEnd_5627993 2889865529139504185204837 := by
  unfold tailWord_5627993
  simp only [CollatzResearch.WordTrace]
  refine ⟨205269768299750020525688633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136846512199833347017125755 205269768299750020525688633)
  ·
    refine ⟨153952326224812515394266475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205269768299750020525688633 153952326224812515394266475)
    ·
      refine ⟨230928489337218773091399713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153952326224812515394266475 230928489337218773091399713)
      ·
        refine ⟨173196367002914079818549785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230928489337218773091399713 173196367002914079818549785)
        ·
          refine ⟨129897275252185559863912339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173196367002914079818549785 129897275252185559863912339)
          ·
            refine ⟨194845912878278339795868509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129897275252185559863912339 194845912878278339795868509)
            ·
              refine ⟨73067217329354377423450691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194845912878278339795868509 73067217329354377423450691)
              ·
                refine ⟨109600825994031566135176037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73067217329354377423450691 109600825994031566135176037)
                ·
                  refine ⟨20550154873880918650345507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109600825994031566135176037 20550154873880918650345507)
                  ·
                    refine ⟨30825232310821377975518261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20550154873880918650345507 30825232310821377975518261)
                    ·
                      refine ⟨2889865529139504185204837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30825232310821377975518261 2889865529139504185204837)
                      ·
                        rfl

theorem cell23_5627993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_5627993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5627993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5627993 prefixEnd_5627993 := by exact prefixLift 5627993
  have htrace : WordTrace (prefixWord ++ tailWord_5627993) baseStart_5627993 baseEnd_5627993 := by
    simpa [prefixWord, tailWord_5627993, baseEnd_5627993] using wordTrace_append hprefix tailTrace_5627993
  have hstable : (prefixWord ++ tailWord_5627993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5627993).length < 2 ^ (prefixWord ++ tailWord_5627993).sum := by decide
  have hdescent : baseEnd_5627993 < baseStart_5627993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5627993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628007 : List Nat := [1, 1, 5, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_5628007 : Nat := 118140960795 + 5628007 * 2 ^ 59
def prefixEnd_5628007 : Nat := 4983230072969 + 3 ^ 40 * 5628007 * 2
def baseEnd_5628007 : Nat := 2889872717868667130429773

theorem tailTrace_5628007 : CollatzResearch.WordTrace tailWord_5628007 prefixEnd_5628007 2889872717868667130429773 := by
  unfold tailWord_5628007
  simp only [CollatzResearch.WordTrace]
  refine ⟨205270278921699300916698275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136846852614466200611132183 205270278921699300916698275)
  ·
    refine ⟨307905418382548951375047413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205270278921699300916698275 307905418382548951375047413)
    ·
      refine ⟨28866132973363964191410695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 307905418382548951375047413 28866132973363964191410695)
      ·
        refine ⟨43299199460045946287116043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28866132973363964191410695 43299199460045946287116043)
        ·
          refine ⟨64948799190068919430674065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43299199460045946287116043 64948799190068919430674065)
          ·
            refine ⟨48711599392551689573005549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64948799190068919430674065 48711599392551689573005549)
            ·
              refine ⟨18266849772206883589877081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48711599392551689573005549 18266849772206883589877081)
              ·
                refine ⟨13700137329155162692407811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18266849772206883589877081 13700137329155162692407811)
                ·
                  refine ⟨20550205993732744038611717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13700137329155162692407811 20550205993732744038611717)
                  ·
                    refine ⟨3853163623824889507239697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20550205993732744038611717 3853163623824889507239697)
                    ·
                      refine ⟨2889872717868667130429773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853163623824889507239697 2889872717868667130429773)
                      ·
                        rfl

theorem cell23_5628007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_5628007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628007 prefixEnd_5628007 := by exact prefixLift 5628007
  have htrace : WordTrace (prefixWord ++ tailWord_5628007) baseStart_5628007 baseEnd_5628007 := by
    simpa [prefixWord, tailWord_5628007, baseEnd_5628007] using wordTrace_append hprefix tailTrace_5628007
  have hstable : (prefixWord ++ tailWord_5628007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628007).length < 2 ^ (prefixWord ++ tailWord_5628007).sum := by decide
  have hdescent : baseEnd_5628007 < baseStart_5628007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628060 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5628060 : Nat := 118140960795 + 5628060 * 2 ^ 59
def prefixEnd_5628060 : Nat := 4983230072969 + 3 ^ 40 * 5628060 * 2
def baseEnd_5628060 : Nat := 963299977447785141022343

theorem tailTrace_5628060 : CollatzResearch.WordTrace tailWord_5628060 prefixEnd_5628060 963299977447785141022343 := by
  unfold tailWord_5628060
  simp only [CollatzResearch.WordTrace]
  refine ⟨102636105995253645484188817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136848141327004860645585089 102636105995253645484188817)
  ·
    refine ⟨76977079496440234113141613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102636105995253645484188817 76977079496440234113141613)
    ·
      refine ⟨28866404811165087792428105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76977079496440234113141613 28866404811165087792428105)
      ·
        refine ⟨21649803608373815844321079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28866404811165087792428105 21649803608373815844321079)
        ·
          refine ⟨32474705412560723766481619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21649803608373815844321079 32474705412560723766481619)
          ·
            refine ⟨48712058118841085649722429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32474705412560723766481619 48712058118841085649722429)
            ·
              refine ⟨18267021794565407118645911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48712058118841085649722429 18267021794565407118645911)
              ·
                refine ⟨27400532691848110677968867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18267021794565407118645911 27400532691848110677968867)
                ·
                  refine ⟨41100799037772166016953301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27400532691848110677968867 41100799037772166016953301)
                  ·
                    refine ⟨963299977447785141022343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41100799037772166016953301 963299977447785141022343)
                    ·
                      rfl

theorem cell23_5628060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5628060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628060 prefixEnd_5628060 := by exact prefixLift 5628060
  have htrace : WordTrace (prefixWord ++ tailWord_5628060) baseStart_5628060 baseEnd_5628060 := by
    simpa [prefixWord, tailWord_5628060, baseEnd_5628060] using wordTrace_append hprefix tailTrace_5628060
  have hstable : (prefixWord ++ tailWord_5628060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628060).length < 2 ^ (prefixWord ++ tailWord_5628060).sum := by decide
  have hdescent : baseEnd_5628060 < baseStart_5628060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628120 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 8]
def baseStart_5628120 : Nat := 118140960795 + 5628120 * 2 ^ 59
def prefixEnd_5628120 : Nat := 4983230072969 + 3 ^ 40 * 5628120 * 2
def baseEnd_5628120 : Nat := 321103415686958354257417

theorem tailTrace_5628120 : CollatzResearch.WordTrace tailWord_5628120 prefixEnd_5628120 321103415686958354257417 := by
  unfold tailWord_5628120
  simp only [CollatzResearch.WordTrace]
  refine ⟨102637200185144960607780907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136849600246859947477041209 102637200185144960607780907)
  ·
    refine ⟨153955800277717440911671361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102637200185144960607780907 153955800277717440911671361)
    ·
      refine ⟨115466850208288080683753521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153955800277717440911671361 115466850208288080683753521)
      ·
        refine ⟨86600137656216060512815141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115466850208288080683753521 86600137656216060512815141)
        ·
          refine ⟨16237525810540511346152839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86600137656216060512815141 16237525810540511346152839)
          ·
            refine ⟨24356288715810767019229259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16237525810540511346152839 24356288715810767019229259)
            ·
              refine ⟨36534433073716150528843889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24356288715810767019229259 36534433073716150528843889)
              ·
                refine ⟨27400824805287112896632917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36534433073716150528843889 27400824805287112896632917)
                ·
                  refine ⟨321103415686958354257417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27400824805287112896632917 321103415686958354257417)
                  ·
                    rfl

theorem cell23_5628120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_5628120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628120 prefixEnd_5628120 := by exact prefixLift 5628120
  have htrace : WordTrace (prefixWord ++ tailWord_5628120) baseStart_5628120 baseEnd_5628120 := by
    simpa [prefixWord, tailWord_5628120, baseEnd_5628120] using wordTrace_append hprefix tailTrace_5628120
  have hstable : (prefixWord ++ tailWord_5628120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628120).length < 2 ^ (prefixWord ++ tailWord_5628120).sum := by decide
  have hdescent : baseEnd_5628120 < baseStart_5628120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628141 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 3, 4]
def baseStart_5628141 : Nat := 118140960795 + 5628141 * 2 ^ 59
def prefixEnd_5628141 : Nat := 4983230072969 + 3 ^ 40 * 5628141 * 2
def baseEnd_5628141 : Nat := 963313841425456535384719

theorem tailTrace_5628141 : CollatzResearch.WordTrace tailWord_5628141 prefixEnd_5628141 963313841425456535384719 := by
  unfold tailWord_5628141
  simp only [CollatzResearch.WordTrace]
  refine ⟨205275166303213841802076277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136850110868809227868050851 205275166303213841802076277)
  ·
    refine ⟨19244546840926297668944651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205275166303213841802076277 19244546840926297668944651)
    ·
      refine ⟨28866820261389446503416977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19244546840926297668944651 28866820261389446503416977)
      ·
        refine ⟨21650115196042084877562733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28866820261389446503416977 21650115196042084877562733)
        ·
          refine ⟨8118793198515781829086025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21650115196042084877562733 8118793198515781829086025)
          ·
            refine ⟨6089094898886836371814519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118793198515781829086025 6089094898886836371814519)
            ·
              refine ⟨9133642348330254557721779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089094898886836371814519 9133642348330254557721779)
              ·
                refine ⟨13700463522495381836582669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133642348330254557721779 13700463522495381836582669)
                ·
                  refine ⟨5137673820935768188718501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13700463522495381836582669 5137673820935768188718501)
                  ·
                    refine ⟨963313841425456535384719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137673820935768188718501 963313841425456535384719)
                    ·
                      rfl

theorem cell23_5628141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_5628141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628141 prefixEnd_5628141 := by exact prefixLift 5628141
  have htrace : WordTrace (prefixWord ++ tailWord_5628141) baseStart_5628141 baseEnd_5628141 := by
    simpa [prefixWord, tailWord_5628141, baseEnd_5628141] using wordTrace_append hprefix tailTrace_5628141
  have hstable : (prefixWord ++ tailWord_5628141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628141).length < 2 ^ (prefixWord ++ tailWord_5628141).sum := by decide
  have hdescent : baseEnd_5628141 < baseStart_5628141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628154 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_5628154 : Nat := 118140960795 + 5628154 * 2 ^ 59
def prefixEnd_5628154 : Nat := 4983230072969 + 3 ^ 40 * 5628154 * 2
def baseEnd_5628154 : Nat := 321105355502764228365733

theorem tailTrace_5628154 : CollatzResearch.WordTrace tailWord_5628154 prefixEnd_5628154 321105355502764228365733 := by
  unfold tailWord_5628154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51318910113041686255574879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136850426968111163348199677 51318910113041686255574879)
  ·
    refine ⟨76978365169562529383362319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51318910113041686255574879 76978365169562529383362319)
    ·
      refine ⟨115467547754343794075043479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76978365169562529383362319 115467547754343794075043479)
      ·
        refine ⟨173201321631515691112565219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115467547754343794075043479 173201321631515691112565219)
        ·
          refine ⟨259801982447273536668847829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173201321631515691112565219 259801982447273536668847829)
          ·
            refine ⟨6089108963607973515676121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 259801982447273536668847829 6089108963607973515676121)
            ·
              refine ⟨4566831722705980136757091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6089108963607973515676121 4566831722705980136757091)
              ·
                refine ⟨6850247584058970205135637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566831722705980136757091 6850247584058970205135637)
                ·
                  refine ⟨321105355502764228365733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6850247584058970205135637 321105355502764228365733)
                  ·
                    rfl

theorem cell23_5628154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_5628154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628154 prefixEnd_5628154 := by exact prefixLift 5628154
  have htrace : WordTrace (prefixWord ++ tailWord_5628154) baseStart_5628154 baseEnd_5628154 := by
    simpa [prefixWord, tailWord_5628154, baseEnd_5628154] using wordTrace_append hprefix tailTrace_5628154
  have hstable : (prefixWord ++ tailWord_5628154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628154).length < 2 ^ (prefixWord ++ tailWord_5628154).sum := by decide
  have hdescent : baseEnd_5628154 < baseStart_5628154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628157 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 3, 5, 2]
def baseStart_5628157 : Nat := 118140960795 + 5628157 * 2 ^ 59
def prefixEnd_5628157 : Nat := 4983230072969 + 3 ^ 40 * 5628157 * 2
def baseEnd_5628157 : Nat := 2889949739966841543554083

theorem tailTrace_5628157 : CollatzResearch.WordTrace tailWord_5628157 prefixEnd_5628157 2889949739966841543554083 := by
  unfold tailWord_5628157
  simp only [CollatzResearch.WordTrace]
  refine ⟨205275749871155876534658725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136850499914103917689772483 205275749871155876534658725)
  ·
    refine ⟨38489203100841726850248511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205275749871155876534658725 38489203100841726850248511)
    ·
      refine ⟨57733804651262590275372767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38489203100841726850248511 57733804651262590275372767)
      ·
        refine ⟨86600706976893885413059151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57733804651262590275372767 86600706976893885413059151)
        ·
          refine ⟨129901060465340828119588727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86600706976893885413059151 129901060465340828119588727)
          ·
            refine ⟨194851590698011242179383091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129901060465340828119588727 194851590698011242179383091)
            ·
              refine ⟨292277386047016863269074637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194851590698011242179383091 292277386047016863269074637)
              ·
                refine ⟨109604019767631323725902989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292277386047016863269074637 109604019767631323725902989)
                ·
                  refine ⟨41101507412861746397213621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109604019767631323725902989 41101507412861746397213621)
                  ·
                    refine ⟨3853266319955788724738777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41101507412861746397213621 3853266319955788724738777)
                    ·
                      refine ⟨2889949739966841543554083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853266319955788724738777 2889949739966841543554083)
                      ·
                        rfl

theorem cell23_5628157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_5628157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628157 prefixEnd_5628157 := by exact prefixLift 5628157
  have htrace : WordTrace (prefixWord ++ tailWord_5628157) baseStart_5628157 baseEnd_5628157 := by
    simpa [prefixWord, tailWord_5628157, baseEnd_5628157] using wordTrace_append hprefix tailTrace_5628157
  have hstable : (prefixWord ++ tailWord_5628157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628157).length < 2 ^ (prefixWord ++ tailWord_5628157).sum := by decide
  have hdescent : baseEnd_5628157 < baseStart_5628157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628184 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_5628184 : Nat := 118140960795 + 5628184 * 2 ^ 59
def prefixEnd_5628184 : Nat := 4983230072969 + 3 ^ 40 * 5628184 * 2
def baseEnd_5628184 : Nat := 963321201314837645972153

theorem tailTrace_5628184 : CollatzResearch.WordTrace tailWord_5628184 prefixEnd_5628184 963321201314837645972153 := by
  unfold tailWord_5628184
  simp only [CollatzResearch.WordTrace]
  refine ⟨102638367321029030072945803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136851156428038706763927737 102638367321029030072945803)
  ·
    refine ⟨153957550981543545109418705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102638367321029030072945803 153957550981543545109418705)
    ·
      refine ⟨115468163236157658832064029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153957550981543545109418705 115468163236157658832064029)
      ·
        refine ⟨43300561213559122062024011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115468163236157658832064029 43300561213559122062024011)
        ·
          refine ⟨64950841820338683093036017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43300561213559122062024011 64950841820338683093036017)
          ·
            refine ⟨48713131365254012319777013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64950841820338683093036017 48713131365254012319777013)
            ·
              refine ⟨4566856065492563654979095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48713131365254012319777013 4566856065492563654979095)
              ·
                refine ⟨6850284098238845482468643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566856065492563654979095 6850284098238845482468643)
                ·
                  refine ⟨10275426147358268223702965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850284098238845482468643 10275426147358268223702965)
                  ·
                    refine ⟨963321201314837645972153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10275426147358268223702965 963321201314837645972153)
                    ·
                      rfl

theorem cell23_5628184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_5628184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628184 prefixEnd_5628184 := by exact prefixLift 5628184
  have htrace : WordTrace (prefixWord ++ tailWord_5628184) baseStart_5628184 baseEnd_5628184 := by
    simpa [prefixWord, tailWord_5628184, baseEnd_5628184] using wordTrace_append hprefix tailTrace_5628184
  have hstable : (prefixWord ++ tailWord_5628184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628184).length < 2 ^ (prefixWord ++ tailWord_5628184).sum := by decide
  have hdescent : baseEnd_5628184 < baseStart_5628184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628187 : List Nat := [1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 4]
def baseStart_5628187 : Nat := 118140960795 + 5628187 * 2 ^ 59
def prefixEnd_5628187 : Nat := 4983230072969 + 3 ^ 40 * 5628187 * 2
def baseEnd_5628187 : Nat := 2889965144386476426178945

theorem tailTrace_5628187 : CollatzResearch.WordTrace tailWord_5628187 prefixEnd_5628187 2889965144386476426178945 := by
  unfold tailWord_5628187
  simp only [CollatzResearch.WordTrace]
  refine ⟨205276844061047191658250815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136851229374031461105500543 205276844061047191658250815)
  ·
    refine ⟨307915266091570787487376223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205276844061047191658250815 307915266091570787487376223)
    ·
      refine ⟨461872899137356181231064335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307915266091570787487376223 461872899137356181231064335)
      ·
        refine ⟨692809348706034271846596503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461872899137356181231064335 692809348706034271846596503)
        ·
          refine ⟨1039214023059051407769894755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692809348706034271846596503 1039214023059051407769894755)
          ·
            refine ⟨1558821034588577111654842133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039214023059051407769894755 1558821034588577111654842133)
            ·
              refine ⟨73069735996339552108820725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1558821034588577111654842133 73069735996339552108820725)
              ·
                refine ⟨6850287749656833010201943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73069735996339552108820725 6850287749656833010201943)
                ·
                  refine ⟨10275431624485249515302915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850287749656833010201943 10275431624485249515302915)
                  ·
                    refine ⟨15413147436727874272954373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10275431624485249515302915 15413147436727874272954373)
                    ·
                      refine ⟨2889965144386476426178945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15413147436727874272954373 2889965144386476426178945)
                      ·
                        rfl

theorem cell23_5628187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 1, 4].length) (baseStart_5628187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628187 prefixEnd_5628187 := by exact prefixLift 5628187
  have htrace : WordTrace (prefixWord ++ tailWord_5628187) baseStart_5628187 baseEnd_5628187 := by
    simpa [prefixWord, tailWord_5628187, baseEnd_5628187] using wordTrace_append hprefix tailTrace_5628187
  have hstable : (prefixWord ++ tailWord_5628187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628187).length < 2 ^ (prefixWord ++ tailWord_5628187).sum := by decide
  have hdescent : baseEnd_5628187 < baseStart_5628187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628207 : List Nat := [1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3]
def baseStart_5628207 : Nat := 118140960795 + 5628207 * 2 ^ 59
def prefixEnd_5628207 : Nat := 4983230072969 + 3 ^ 40 * 5628207 * 2
def baseEnd_5628207 : Nat := 2889975413999566347928853

theorem tailTrace_5628207 : CollatzResearch.WordTrace tailWord_5628207 prefixEnd_5628207 2889975413999566347928853 := by
  unfold tailWord_5628207
  simp only [CollatzResearch.WordTrace]
  refine ⟨205277573520974735073978875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136851715680649823382652583 205277573520974735073978875)
  ·
    refine ⟨307916360281462102610968313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205277573520974735073978875 307916360281462102610968313)
    ·
      refine ⟨230937270211096576958226235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307916360281462102610968313 230937270211096576958226235)
      ·
        refine ⟨346405905316644865437339353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230937270211096576958226235 346405905316644865437339353)
        ·
          refine ⟨259804428987483649078004515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346405905316644865437339353 259804428987483649078004515)
          ·
            refine ⟨389706643481225473617006773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259804428987483649078004515 389706643481225473617006773)
            ·
              refine ⟨36534997826364888151594385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389706643481225473617006773 36534997826364888151594385)
              ·
                refine ⟨27401248369773666113695789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36534997826364888151594385 27401248369773666113695789)
                ·
                  refine ⟨10275468138665124792635921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27401248369773666113695789 10275468138665124792635921)
                  ·
                    refine ⟨7706601103998843594476941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10275468138665124792635921 7706601103998843594476941)
                    ·
                      refine ⟨2889975413999566347928853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7706601103998843594476941 2889975413999566347928853)
                      ·
                        rfl

theorem cell23_5628207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_5628207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628207 prefixEnd_5628207 := by exact prefixLift 5628207
  have htrace : WordTrace (prefixWord ++ tailWord_5628207) baseStart_5628207 baseEnd_5628207 := by
    simpa [prefixWord, tailWord_5628207, baseEnd_5628207] using wordTrace_append hprefix tailTrace_5628207
  have hstable : (prefixWord ++ tailWord_5628207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628207).length < 2 ^ (prefixWord ++ tailWord_5628207).sum := by decide
  have hdescent : baseEnd_5628207 < baseStart_5628207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628225 : List Nat := [1, 2, 5, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_5628225 : Nat := 118140960795 + 5628225 * 2 ^ 59
def prefixEnd_5628225 : Nat := 4983230072969 + 3 ^ 40 * 5628225 * 2
def baseEnd_5628225 : Nat := 2889984656651347277503771

theorem tailTrace_5628225 : CollatzResearch.WordTrace tailWord_5628225 prefixEnd_5628225 2889984656651347277503771 := by
  unfold tailWord_5628225
  simp only [CollatzResearch.WordTrace]
  refine ⟨205278230034909524148134129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136852153356606349432089419 205278230034909524148134129)
  ·
    refine ⟨153958672526182143111100597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205278230034909524148134129 153958672526182143111100597)
    ·
      refine ⟨14433625549329575916665681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153958672526182143111100597 14433625549329575916665681)
      ·
        refine ⟨10825219161997181937499261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14433625549329575916665681 10825219161997181937499261)
        ·
          refine ⟨4059457185748943226562223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10825219161997181937499261 4059457185748943226562223)
          ·
            refine ⟨6089185778623414839843335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059457185748943226562223 6089185778623414839843335)
            ·
              refine ⟨9133778667935122259765003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089185778623414839843335 9133778667935122259765003)
              ·
                refine ⟨13700668001902683389647505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9133778667935122259765003 13700668001902683389647505)
                ·
                  refine ⟨10275501001427012542235629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13700668001902683389647505 10275501001427012542235629)
                  ·
                    refine ⟨3853312875535129703338361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10275501001427012542235629 3853312875535129703338361)
                    ·
                      refine ⟨2889984656651347277503771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853312875535129703338361 2889984656651347277503771)
                      ·
                        rfl

theorem cell23_5628225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_5628225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628225 prefixEnd_5628225 := by exact prefixLift 5628225
  have htrace : WordTrace (prefixWord ++ tailWord_5628225) baseStart_5628225 baseEnd_5628225 := by
    simpa [prefixWord, tailWord_5628225, baseEnd_5628225] using wordTrace_append hprefix tailTrace_5628225
  have hstable : (prefixWord ++ tailWord_5628225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628225).length < 2 ^ (prefixWord ++ tailWord_5628225).sum := by decide
  have hdescent : baseEnd_5628225 < baseStart_5628225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628241 : List Nat := [1, 2, 2, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_5628241 : Nat := 118140960795 + 5628241 * 2 ^ 59
def prefixEnd_5628241 : Nat := 4983230072969 + 3 ^ 40 * 5628241 * 2
def baseEnd_5628241 : Nat := 2889992872341819214903697

theorem tailTrace_5628241 : CollatzResearch.WordTrace tailWord_5628241 prefixEnd_5628241 2889992872341819214903697 := by
  unfold tailWord_5628241
  simp only [CollatzResearch.WordTrace]
  refine ⟨205278813602851558880716577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136852542401901039253811051 205278813602851558880716577)
  ·
    refine ⟨153959110202138669160537433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205278813602851558880716577 153959110202138669160537433)
    ·
      refine ⟨115469332651604001870403075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153959110202138669160537433 115469332651604001870403075)
      ·
        refine ⟨173203998977406002805604613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115469332651604001870403075 173203998977406002805604613)
        ·
          refine ⟨32475749808263625526050865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173203998977406002805604613 32475749808263625526050865)
          ·
            refine ⟨24356812356197719144538149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32475749808263625526050865 24356812356197719144538149)
            ·
              refine ⟨4566902316787072339600903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24356812356197719144538149 4566902316787072339600903)
              ·
                refine ⟨6850353475180608509401355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4566902316787072339600903 6850353475180608509401355)
                ·
                  refine ⟨10275530212770912764102033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850353475180608509401355 10275530212770912764102033)
                  ·
                    refine ⟨7706647659578184573076525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10275530212770912764102033 7706647659578184573076525)
                    ·
                      refine ⟨2889992872341819214903697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7706647659578184573076525 2889992872341819214903697)
                      ·
                        rfl

theorem cell23_5628241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_5628241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628241 prefixEnd_5628241 := by exact prefixLift 5628241
  have htrace : WordTrace (prefixWord ++ tailWord_5628241) baseStart_5628241 baseEnd_5628241 := by
    simpa [prefixWord, tailWord_5628241, baseEnd_5628241] using wordTrace_append hprefix tailTrace_5628241
  have hstable : (prefixWord ++ tailWord_5628241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628241).length < 2 ^ (prefixWord ++ tailWord_5628241).sum := by decide
  have hdescent : baseEnd_5628241 < baseStart_5628241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628278 : List Nat := [5, 1, 1, 4, 1, 2, 2, 7]
def baseStart_5628278 : Nat := 118140960795 + 5628278 * 2 ^ 59
def prefixEnd_5628278 : Nat := 4983230072969 + 3 ^ 40 * 5628278 * 2
def baseEnd_5628278 : Nat := 107037476708371687783001

theorem tailTrace_5628278 : CollatzResearch.WordTrace tailWord_5628278 prefixEnd_5628278 107037476708371687783001 := by
  unfold tailWord_5628278
  simp only [CollatzResearch.WordTrace]
  refine ⟨12830010193982344637488343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136853442069145009466542325 12830010193982344637488343)
  ·
    refine ⟨19245015290973516956232515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12830010193982344637488343 19245015290973516956232515)
    ·
      refine ⟨28867522936460275434348773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245015290973516956232515 28867522936460275434348773)
      ·
        refine ⟨5412660550586301643940395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28867522936460275434348773 5412660550586301643940395)
        ·
          refine ⟨8118990825879452465910593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412660550586301643940395 8118990825879452465910593)
          ·
            refine ⟨6089243119409589349432945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8118990825879452465910593 6089243119409589349432945)
            ·
              refine ⟨4566932339557192012074709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6089243119409589349432945 4566932339557192012074709)
              ·
                refine ⟨107037476708371687783001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4566932339557192012074709 107037476708371687783001)
                ·
                  rfl

theorem cell23_5628278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_5628278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628278 prefixEnd_5628278 := by exact prefixLift 5628278
  have htrace : WordTrace (prefixWord ++ tailWord_5628278) baseStart_5628278 baseEnd_5628278 := by
    simpa [prefixWord, tailWord_5628278, baseEnd_5628278] using wordTrace_append hprefix tailTrace_5628278
  have hstable : (prefixWord ++ tailWord_5628278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628278).length < 2 ^ (prefixWord ++ tailWord_5628278).sum := by decide
  have hdescent : baseEnd_5628278 < baseStart_5628278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628297 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_5628297 : Nat := 118140960795 + 5628297 * 2 ^ 59
def prefixEnd_5628297 : Nat := 4983230072969 + 3 ^ 40 * 5628297 * 2
def baseEnd_5628297 : Nat := 2890021627258470995803439

theorem tailTrace_5628297 : CollatzResearch.WordTrace tailWord_5628297 prefixEnd_5628297 2890021627258470995803439 := by
  unfold tailWord_5628297
  simp only [CollatzResearch.WordTrace]
  refine ⟨205280856090648680444755145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136853904060432453629836763 205280856090648680444755145)
  ·
    refine ⟨153960642067986510333566359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205280856090648680444755145 153960642067986510333566359)
    ·
      refine ⟨230940963101979765500349539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153960642067986510333566359 230940963101979765500349539)
      ·
        refine ⟨346411444652969648250524309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230940963101979765500349539 346411444652969648250524309)
        ·
          refine ⟨16238036468107952261743327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 346411444652969648250524309 16238036468107952261743327)
          ·
            refine ⟨24357054702161928392614991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16238036468107952261743327 24357054702161928392614991)
            ·
              refine ⟨36535582053242892588922487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24357054702161928392614991 36535582053242892588922487)
              ·
                refine ⟨54803373079864338883383731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36535582053242892588922487 54803373079864338883383731)
                ·
                  refine ⟨82205059619796508325075597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54803373079864338883383731 82205059619796508325075597)
                  ·
                    refine ⟨30826897357423690621903349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82205059619796508325075597 30826897357423690621903349)
                    ·
                      refine ⟨2890021627258470995803439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30826897357423690621903349 2890021627258470995803439)
                      ·
                        rfl

theorem cell23_5628297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_5628297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628297 prefixEnd_5628297 := by exact prefixLift 5628297
  have htrace : WordTrace (prefixWord ++ tailWord_5628297) baseStart_5628297 baseEnd_5628297 := by
    simpa [prefixWord, tailWord_5628297, baseEnd_5628297] using wordTrace_append hprefix tailTrace_5628297
  have hstable : (prefixWord ++ tailWord_5628297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628297).length < 2 ^ (prefixWord ++ tailWord_5628297).sum := by decide
  have hdescent : baseEnd_5628297 < baseStart_5628297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628311 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 4, 2, 2]
def baseStart_5628311 : Nat := 118140960795 + 5628311 * 2 ^ 59
def prefixEnd_5628311 : Nat := 4983230072969 + 3 ^ 40 * 5628311 * 2
def baseEnd_5628311 : Nat := 2890028815987633941028375

theorem tailTrace_5628311 : CollatzResearch.WordTrace tailWord_5628311 prefixEnd_5628311 2890028815987633941028375 := by
  unfold tailWord_5628311
  simp only [CollatzResearch.WordTrace]
  refine ⟨205281366712597960835764787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136854244475065307223843191 205281366712597960835764787)
  ·
    refine ⟨307922050068896941253647181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205281366712597960835764787 307922050068896941253647181)
    ·
      refine ⟨115470768775836352970117693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307922050068896941253647181 115470768775836352970117693)
      ·
        refine ⟨43301538290938632363794135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115470768775836352970117693 43301538290938632363794135)
        ·
          refine ⟨64952307436407948545691203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43301538290938632363794135 64952307436407948545691203)
          ·
            refine ⟨97428461154611922818536805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64952307436407948545691203 97428461154611922818536805)
            ·
              refine ⟨18267836466489735528475651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97428461154611922818536805 18267836466489735528475651)
              ·
                refine ⟨27401754699734603292713477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18267836466489735528475651 27401754699734603292713477)
                ·
                  refine ⟨5137829006200238117383777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27401754699734603292713477 5137829006200238117383777)
                  ·
                    refine ⟨3853371754650178588037833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5137829006200238117383777 3853371754650178588037833)
                    ·
                      refine ⟨2890028815987633941028375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853371754650178588037833 2890028815987633941028375)
                      ·
                        rfl

theorem cell23_5628311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_5628311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628311 prefixEnd_5628311 := by exact prefixLift 5628311
  have htrace : WordTrace (prefixWord ++ tailWord_5628311) baseStart_5628311 baseEnd_5628311 := by
    simpa [prefixWord, tailWord_5628311, baseEnd_5628311] using wordTrace_append hprefix tailTrace_5628311
  have hstable : (prefixWord ++ tailWord_5628311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628311).length < 2 ^ (prefixWord ++ tailWord_5628311).sum := by decide
  have hdescent : baseEnd_5628311 < baseStart_5628311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628367 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4]
def baseStart_5628367 : Nat := 118140960795 + 5628367 * 2 ^ 59
def prefixEnd_5628367 : Nat := 4983230072969 + 3 ^ 40 * 5628367 * 2
def baseEnd_5628367 : Nat := 2890057570904285721928117

theorem tailTrace_5628367 : CollatzResearch.WordTrace tailWord_5628367 prefixEnd_5628367 2890057570904285721928117 := by
  unfold tailWord_5628367
  simp only [CollatzResearch.WordTrace]
  refine ⟨205283409200395082399803355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136855606133596721599868903 205283409200395082399803355)
  ·
    refine ⟨307925113800592623599705033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205283409200395082399803355 307925113800592623599705033)
    ·
      refine ⟨230943835350444467699778775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307925113800592623599705033 230943835350444467699778775)
      ·
        refine ⟨346415753025666701549668163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230943835350444467699778775 346415753025666701549668163)
        ·
          refine ⟨519623629538500052324502245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346415753025666701549668163 519623629538500052324502245)
          ·
            refine ⟨97429430538468759810844171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 519623629538500052324502245 97429430538468759810844171)
            ·
              refine ⟨146144145807703139716266257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97429430538468759810844171 146144145807703139716266257)
              ·
                refine ⟨109608109355777354787199693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 146144145807703139716266257 109608109355777354787199693)
                ·
                  refine ⟨41103041008416508045199885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109608109355777354787199693 41103041008416508045199885)
                  ·
                    refine ⟨15413640378156190516949957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41103041008416508045199885 15413640378156190516949957)
                    ·
                      refine ⟨2890057570904285721928117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15413640378156190516949957 2890057570904285721928117)
                      ·
                        rfl

theorem cell23_5628367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_5628367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628367 prefixEnd_5628367 := by exact prefixLift 5628367
  have htrace : WordTrace (prefixWord ++ tailWord_5628367) baseStart_5628367 baseEnd_5628367 := by
    simpa [prefixWord, tailWord_5628367, baseEnd_5628367] using wordTrace_append hprefix tailTrace_5628367
  have hstable : (prefixWord ++ tailWord_5628367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628367).length < 2 ^ (prefixWord ++ tailWord_5628367).sum := by decide
  have hdescent : baseEnd_5628367 < baseStart_5628367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628428 : List Nat := [2, 2, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_5628428 : Nat := 118140960795 + 5628428 * 2 ^ 59
def prefixEnd_5628428 : Nat := 4983230072969 + 3 ^ 40 * 5628428 * 2
def baseEnd_5628428 : Nat := 963362964408069994421779

theorem tailTrace_5628428 : CollatzResearch.WordTrace tailWord_5628428 prefixEnd_5628428 963362964408069994421779 := by
  unfold tailWord_5628428
  simp only [CollatzResearch.WordTrace]
  refine ⟨102642817026587044908886969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136857089368782726545182625 102642817026587044908886969)
  ·
    refine ⟨76982112769940283681665227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102642817026587044908886969 76982112769940283681665227)
    ·
      refine ⟨115473169154910425522497841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76982112769940283681665227 115473169154910425522497841)
      ·
        refine ⟨86604876866182819141873381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115473169154910425522497841 86604876866182819141873381)
        ·
          refine ⟨16238414412409278589101259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86604876866182819141873381 16238414412409278589101259)
          ·
            refine ⟨24357621618613917883651889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16238414412409278589101259 24357621618613917883651889)
            ·
              refine ⟨18268216213960438412738917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24357621618613917883651889 18268216213960438412738917)
              ·
                refine ⟨3425290540117582202388547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18268216213960438412738917 3425290540117582202388547)
                ·
                  refine ⟨5137935810176373303582821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425290540117582202388547 5137935810176373303582821)
                  ·
                    refine ⟨963362964408069994421779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137935810176373303582821 963362964408069994421779)
                    ·
                      rfl

theorem cell23_5628428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_5628428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628428 prefixEnd_5628428 := by exact prefixLift 5628428
  have htrace : WordTrace (prefixWord ++ tailWord_5628428) baseStart_5628428 baseEnd_5628428 := by
    simpa [prefixWord, tailWord_5628428, baseEnd_5628428] using wordTrace_append hprefix tailTrace_5628428
  have hstable : (prefixWord ++ tailWord_5628428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628428).length < 2 ^ (prefixWord ++ tailWord_5628428).sum := by decide
  have hdescent : baseEnd_5628428 < baseStart_5628428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628462 : List Nat := [4, 1, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5628462 : Nat := 118140960795 + 5628462 * 2 ^ 59
def prefixEnd_5628462 : Nat := 4983230072969 + 3 ^ 40 * 5628462 * 2
def baseEnd_5628462 : Nat := 963368783855487616746727

theorem tailTrace_5628462 : CollatzResearch.WordTrace tailWord_5628462 prefixEnd_5628462 963368783855487616746727 := by
  unfold tailWord_5628462
  simp only [CollatzResearch.WordTrace]
  refine ⟨25660859266881364203063955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136857916090033942416341093 25660859266881364203063955)
  ·
    refine ⟨38491288900322046304595933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25660859266881364203063955 38491288900322046304595933)
    ·
      refine ⟨14434233337620767364223475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38491288900322046304595933 14434233337620767364223475)
      ·
        refine ⟨21651350006431151046335213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434233337620767364223475 21651350006431151046335213)
        ·
          refine ⟨8119256252411681642375705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21651350006431151046335213 8119256252411681642375705)
          ·
            refine ⟨6089442189308761231781779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119256252411681642375705 6089442189308761231781779)
            ·
              refine ⟨9134163283963141847672669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089442189308761231781779 9134163283963141847672669)
              ·
                refine ⟨3425311231486178192877251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9134163283963141847672669 3425311231486178192877251)
                ·
                  refine ⟨5137966847229267289315877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425311231486178192877251 5137966847229267289315877)
                  ·
                    refine ⟨963368783855487616746727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5137966847229267289315877 963368783855487616746727)
                    ·
                      rfl

theorem cell23_5628462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5628462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628462 prefixEnd_5628462 := by exact prefixLift 5628462
  have htrace : WordTrace (prefixWord ++ tailWord_5628462) baseStart_5628462 baseEnd_5628462 := by
    simpa [prefixWord, tailWord_5628462, baseEnd_5628462] using wordTrace_append hprefix tailTrace_5628462
  have hstable : (prefixWord ++ tailWord_5628462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628462).length < 2 ^ (prefixWord ++ tailWord_5628462).sum := by decide
  have hdescent : baseEnd_5628462 < baseStart_5628462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628504 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_5628504 : Nat := 118140960795 + 5628504 * 2 ^ 59
def prefixEnd_5628504 : Nat := 4983230072969 + 3 ^ 40 * 5628504 * 2
def baseEnd_5628504 : Nat := 2890127917753951685914987

theorem tailTrace_5628504 : CollatzResearch.WordTrace tailWord_5628504 prefixEnd_5628504 2890127917753951685914987 := by
  unfold tailWord_5628504
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644203000449377398770283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136858937333932503198360377 102644203000449377398770283)
  ·
    refine ⟨153966304500674066098155425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102644203000449377398770283 153966304500674066098155425)
    ·
      refine ⟨115474728375505549573616569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153966304500674066098155425 115474728375505549573616569)
      ·
        refine ⟨86606046281629162180212427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115474728375505549573616569 86606046281629162180212427)
        ·
          refine ⟨129909069422443743270318641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86606046281629162180212427 129909069422443743270318641)
          ·
            refine ⟨97431802066832807452738981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129909069422443743270318641 97431802066832807452738981)
            ·
              refine ⟨18268462887531151397388559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97431802066832807452738981 18268462887531151397388559)
              ·
                refine ⟨27402694331296727096082839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18268462887531151397388559 27402694331296727096082839)
                ·
                  refine ⟨41104041496945090644124259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27402694331296727096082839 41104041496945090644124259)
                  ·
                    refine ⟨61656062245417635966186389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41104041496945090644124259 61656062245417635966186389)
                    ·
                      refine ⟨2890127917753951685914987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61656062245417635966186389 2890127917753951685914987)
                      ·
                        rfl

theorem cell23_5628504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_5628504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628504 prefixEnd_5628504 := by exact prefixLift 5628504
  have htrace : WordTrace (prefixWord ++ tailWord_5628504) baseStart_5628504 baseEnd_5628504 := by
    simpa [prefixWord, tailWord_5628504, baseEnd_5628504] using wordTrace_append hprefix tailTrace_5628504
  have hstable : (prefixWord ++ tailWord_5628504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628504).length < 2 ^ (prefixWord ++ tailWord_5628504).sum := by decide
  have hdescent : baseEnd_5628504 < baseStart_5628504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628508 : List Nat := [2, 2, 4, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5628508 : Nat := 118140960795 + 5628508 * 2 ^ 59
def prefixEnd_5628508 : Nat := 4983230072969 + 3 ^ 40 * 5628508 * 2
def baseEnd_5628508 : Nat := 2890129971676569670264969

theorem tailTrace_5628508 : CollatzResearch.WordTrace tailWord_5628508 prefixEnd_5628508 2890129971676569670264969 := by
  unfold tailWord_5628508
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644275946442131740343089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136859034595256175653790785 102644275946442131740343089)
  ·
    refine ⟨76983206959831598805257317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102644275946442131740343089 76983206959831598805257317)
    ·
      refine ⟨14434351304968424775985747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76983206959831598805257317 14434351304968424775985747)
      ·
        refine ⟨21651526957452637163978621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14434351304968424775985747 21651526957452637163978621)
        ·
          refine ⟨8119322609044738936491983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21651526957452637163978621 8119322609044738936491983)
          ·
            refine ⟨12178983913567108404737975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119322609044738936491983 12178983913567108404737975)
            ·
              refine ⟨18268475870350662607106963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12178983913567108404737975 18268475870350662607106963)
              ·
                refine ⟨27402713805525993910660445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18268475870350662607106963 27402713805525993910660445)
                ·
                  refine ⟨10276017677072247716497667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27402713805525993910660445 10276017677072247716497667)
                  ·
                    refine ⟨15414026515608371574746501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10276017677072247716497667 15414026515608371574746501)
                    ·
                      refine ⟨2890129971676569670264969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15414026515608371574746501 2890129971676569670264969)
                      ·
                        rfl

theorem cell23_5628508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5628508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628508 prefixEnd_5628508 := by exact prefixLift 5628508
  have htrace : WordTrace (prefixWord ++ tailWord_5628508) baseStart_5628508 baseEnd_5628508 := by
    simpa [prefixWord, tailWord_5628508, baseEnd_5628508] using wordTrace_append hprefix tailTrace_5628508
  have hstable : (prefixWord ++ tailWord_5628508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628508).length < 2 ^ (prefixWord ++ tailWord_5628508).sum := by decide
  have hdescent : baseEnd_5628508 < baseStart_5628508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628525 : List Nat := [1, 5, 1, 1, 3, 2, 3, 1, 1, 1, 4]
def baseStart_5628525 : Nat := 118140960795 + 5628525 * 2 ^ 59
def prefixEnd_5628525 : Nat := 4983230072969 + 3 ^ 40 * 5628525 * 2
def baseEnd_5628525 : Nat := 2890138700847696103752391

theorem tailTrace_5628525 : CollatzResearch.WordTrace tailWord_5628525 prefixEnd_5628525 2890138700847696103752391 := by
  unfold tailWord_5628525
  simp only [CollatzResearch.WordTrace]
  refine ⟨205289171933822675384055029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136859447955881783589370019 205289171933822675384055029)
  ·
    refine ⟨19245859868795875817255159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205289171933822675384055029 19245859868795875817255159)
    ·
      refine ⟨28868789803193813725882739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19245859868795875817255159 28868789803193813725882739)
      ·
        refine ⟨43303184704790720588824109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28868789803193813725882739 43303184704790720588824109)
        ·
          refine ⟨16238694264296520220809041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43303184704790720588824109 16238694264296520220809041)
          ·
            refine ⟨12179020698222390165606781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16238694264296520220809041 12179020698222390165606781)
            ·
              refine ⟨4567132761833396312102543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12179020698222390165606781 4567132761833396312102543)
              ·
                refine ⟨6850699142750094468153815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567132761833396312102543 6850699142750094468153815)
                ·
                  refine ⟨10276048714125141702230723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6850699142750094468153815 10276048714125141702230723)
                  ·
                    refine ⟨15414073071187712553346085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10276048714125141702230723 15414073071187712553346085)
                    ·
                      refine ⟨2890138700847696103752391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15414073071187712553346085 2890138700847696103752391)
                      ·
                        rfl

theorem cell23_5628525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_5628525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628525 prefixEnd_5628525 := by exact prefixLift 5628525
  have htrace : WordTrace (prefixWord ++ tailWord_5628525) baseStart_5628525 baseEnd_5628525 := by
    simpa [prefixWord, tailWord_5628525, baseEnd_5628525] using wordTrace_append hprefix tailTrace_5628525
  have hstable : (prefixWord ++ tailWord_5628525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628525).length < 2 ^ (prefixWord ++ tailWord_5628525).sum := by decide
  have hdescent : baseEnd_5628525 < baseStart_5628525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628528 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_5628528 : Nat := 118140960795 + 5628528 * 2 ^ 59
def prefixEnd_5628528 : Nat := 4983230072969 + 3 ^ 40 * 5628528 * 2
def baseEnd_5628528 : Nat := 2890140241289659592014877

theorem tailTrace_5628528 : CollatzResearch.WordTrace tailWord_5628528 prefixEnd_5628528 2890140241289659592014877 := by
  unfold tailWord_5628528
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644640676405903448207119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136859520901874537930942825 102644640676405903448207119)
  ·
    refine ⟨153966961014608855172310679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102644640676405903448207119 153966961014608855172310679)
    ·
      refine ⟨230950441521913282758466019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153966961014608855172310679 230950441521913282758466019)
      ·
        refine ⟨346425662282869924137699029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230950441521913282758466019 346425662282869924137699029)
        ·
          refine ⟨8119351459754763846977321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 346425662282869924137699029 8119351459754763846977321)
          ·
            refine ⟨6089513594816072885232991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119351459754763846977321 6089513594816072885232991)
            ·
              refine ⟨9134270392224109327849487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089513594816072885232991 9134270392224109327849487)
              ·
                refine ⟨13701405588336163991774231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134270392224109327849487 13701405588336163991774231)
                ·
                  refine ⟨20552108382504245987661347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13701405588336163991774231 20552108382504245987661347)
                  ·
                    refine ⟨30828162573756368981492021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20552108382504245987661347 30828162573756368981492021)
                    ·
                      refine ⟨2890140241289659592014877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30828162573756368981492021 2890140241289659592014877)
                      ·
                        rfl

theorem cell23_5628528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_5628528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628528 prefixEnd_5628528 := by exact prefixLift 5628528
  have htrace : WordTrace (prefixWord ++ tailWord_5628528) baseStart_5628528 baseEnd_5628528 := by
    simpa [prefixWord, tailWord_5628528, baseEnd_5628528] using wordTrace_append hprefix tailTrace_5628528
  have hstable : (prefixWord ++ tailWord_5628528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628528).length < 2 ^ (prefixWord ++ tailWord_5628528).sum := by decide
  have hdescent : baseEnd_5628528 < baseStart_5628528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628544 : List Nat := [2, 1, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_5628544 : Nat := 118140960795 + 5628544 * 2 ^ 59
def prefixEnd_5628544 : Nat := 4983230072969 + 3 ^ 40 * 5628544 * 2
def baseEnd_5628544 : Nat := 963382818993377176471601

theorem tailTrace_5628544 : CollatzResearch.WordTrace tailWord_5628544 prefixEnd_5628544 963382818993377176471601 := by
  unfold tailWord_5628544
  simp only [CollatzResearch.WordTrace]
  refine ⟨102644932460376920814498343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136859909947169227752664457 102644932460376920814498343)
  ·
    refine ⟨153967398690565381221747515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102644932460376920814498343 153967398690565381221747515)
    ·
      refine ⟨230951098035848071832621273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153967398690565381221747515 230951098035848071832621273)
      ·
        refine ⟨173213323526886053874465955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230951098035848071832621273 173213323526886053874465955)
        ·
          refine ⟨259819985290329080811698933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173213323526886053874465955 259819985290329080811698933)
          ·
            refine ⟨24358123620968351326096775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 259819985290329080811698933 24358123620968351326096775)
            ·
              refine ⟨36537185431452526989145163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24358123620968351326096775 36537185431452526989145163)
              ·
                refine ⟨54805778147178790483717745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36537185431452526989145163 54805778147178790483717745)
                ·
                  refine ⟨41104333610384092862788309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54805778147178790483717745 41104333610384092862788309)
                  ·
                    refine ⟨963382818993377176471601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41104333610384092862788309 963382818993377176471601)
                    ·
                      rfl

theorem cell23_5628544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_5628544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628544 prefixEnd_5628544 := by exact prefixLift 5628544
  have htrace : WordTrace (prefixWord ++ tailWord_5628544) baseStart_5628544 baseEnd_5628544 := by
    simpa [prefixWord, tailWord_5628544, baseEnd_5628544] using wordTrace_append hprefix tailTrace_5628544
  have hstable : (prefixWord ++ tailWord_5628544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628544).length < 2 ^ (prefixWord ++ tailWord_5628544).sum := by decide
  have hdescent : baseEnd_5628544 < baseStart_5628544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628558 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3]
def baseStart_5628558 : Nat := 118140960795 + 5628558 * 2 ^ 59
def prefixEnd_5628558 : Nat := 4983230072969 + 3 ^ 40 * 5628558 * 2
def baseEnd_5628558 : Nat := 2890155645709294474639739

theorem tailTrace_5628558 : CollatzResearch.WordTrace tailWord_5628558 prefixEnd_5628558 2890155645709294474639739 := by
  unfold tailWord_5628558
  simp only [CollatzResearch.WordTrace]
  refine ⟨25661296942837890252500791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136860250361802081346670885 25661296942837890252500791)
  ·
    refine ⟨38491945414256835378751187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25661296942837890252500791 38491945414256835378751187)
    ·
      refine ⟨57737918121385253068126781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38491945414256835378751187 57737918121385253068126781)
      ·
        refine ⟨21651719295519469900547543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57737918121385253068126781 21651719295519469900547543)
        ·
          refine ⟨32477578943279204850821315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21651719295519469900547543 32477578943279204850821315)
          ·
            refine ⟨48716368414918807276231973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32477578943279204850821315 48716368414918807276231973)
            ·
              refine ⟨9134319077797276364293495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48716368414918807276231973 9134319077797276364293495)
              ·
                refine ⟨13701478616695914546440243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134319077797276364293495 13701478616695914546440243)
                ·
                  refine ⟨20552217925043871819660365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13701478616695914546440243 20552217925043871819660365)
                  ·
                    refine ⟨7707081721891451932372637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20552217925043871819660365 7707081721891451932372637)
                    ·
                      refine ⟨2890155645709294474639739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707081721891451932372637 2890155645709294474639739)
                      ·
                        rfl

theorem cell23_5628558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_5628558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628558 prefixEnd_5628558 := by exact prefixLift 5628558
  have htrace : WordTrace (prefixWord ++ tailWord_5628558) baseStart_5628558 baseEnd_5628558 := by
    simpa [prefixWord, tailWord_5628558, baseEnd_5628558] using wordTrace_append hprefix tailTrace_5628558
  have hstable : (prefixWord ++ tailWord_5628558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628558).length < 2 ^ (prefixWord ++ tailWord_5628558).sum := by decide
  have hdescent : baseEnd_5628558 < baseStart_5628558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628568 : List Nat := [2, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_5628568 : Nat := 118140960795 + 5628568 * 2 ^ 59
def prefixEnd_5628568 : Nat := 4983230072969 + 3 ^ 40 * 5628568 * 2
def baseEnd_5628568 : Nat := 2890160780515839435514693

theorem tailTrace_5628568 : CollatzResearch.WordTrace tailWord_5628568 prefixEnd_5628568 2890160780515839435514693 := by
  unfold tailWord_5628568
  simp only [CollatzResearch.WordTrace]
  refine ⟨102645370136333446863935179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136860493515111262485246905 102645370136333446863935179)
  ·
    refine ⟨153968055204500170295902769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102645370136333446863935179 153968055204500170295902769)
    ·
      refine ⟨115476041403375127721927077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153968055204500170295902769 115476041403375127721927077)
      ·
        refine ⟨21651757763132836447861327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115476041403375127721927077 21651757763132836447861327)
        ·
          refine ⟨32477636644699254671791991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21651757763132836447861327 32477636644699254671791991)
          ·
            refine ⟨48716454967048882007687987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32477636644699254671791991 48716454967048882007687987)
            ·
              refine ⟨73074682450573323011531981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48716454967048882007687987 73074682450573323011531981)
              ·
                refine ⟨27403005918964996129324493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73074682450573323011531981 27403005918964996129324493)
                ·
                  refine ⟨10276127219611873548496685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27403005918964996129324493 10276127219611873548496685)
                  ·
                    refine ⟨3853547707354452580686257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10276127219611873548496685 3853547707354452580686257)
                    ·
                      refine ⟨2890160780515839435514693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853547707354452580686257 2890160780515839435514693)
                      ·
                        rfl

theorem cell23_5628568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_5628568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628568 prefixEnd_5628568 := by exact prefixLift 5628568
  have htrace : WordTrace (prefixWord ++ tailWord_5628568) baseStart_5628568 baseEnd_5628568 := by
    simpa [prefixWord, tailWord_5628568, baseEnd_5628568] using wordTrace_append hprefix tailTrace_5628568
  have hstable : (prefixWord ++ tailWord_5628568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628568).length < 2 ^ (prefixWord ++ tailWord_5628568).sum := by decide
  have hdescent : baseEnd_5628568 < baseStart_5628568 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628609 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5628609 : Nat := 118140960795 + 5628609 * 2 ^ 59
def prefixEnd_5628609 : Nat := 4983230072969 + 3 ^ 40 * 5628609 * 2
def baseEnd_5628609 : Nat := 2890181833222673775102005

theorem tailTrace_5628609 : CollatzResearch.WordTrace tailWord_5628609 prefixEnd_5628609 2890181833222673775102005 := by
  unfold tailWord_5628609
  simp only [CollatzResearch.WordTrace]
  refine ⟨205292235665518357730112881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136861490443678905153408587 205292235665518357730112881)
  ·
    refine ⟨153969176749138768297584661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205292235665518357730112881 153969176749138768297584661)
    ·
      refine ⟨7217305160115879763949281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153969176749138768297584661 7217305160115879763949281)
      ·
        refine ⟨5412978870086909822961961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7217305160115879763949281 5412978870086909822961961)
        ·
          refine ⟨4059734152565182367221471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5412978870086909822961961 4059734152565182367221471)
          ·
            refine ⟨6089601228847773550832207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059734152565182367221471 6089601228847773550832207)
            ·
              refine ⟨9134401843271660326248311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089601228847773550832207 9134401843271660326248311)
              ·
                refine ⟨13701602764907490489372467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134401843271660326248311 13701602764907490489372467)
                ·
                  refine ⟨20552404147361235734058701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13701602764907490489372467 20552404147361235734058701)
                  ·
                    refine ⟨7707151555260463400272013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20552404147361235734058701 7707151555260463400272013)
                    ·
                      refine ⟨2890181833222673775102005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707151555260463400272013 2890181833222673775102005)
                      ·
                        rfl

theorem cell23_5628609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5628609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628609 prefixEnd_5628609 := by exact prefixLift 5628609
  have htrace : WordTrace (prefixWord ++ tailWord_5628609) baseStart_5628609 baseEnd_5628609 := by
    simpa [prefixWord, tailWord_5628609, baseEnd_5628609] using wordTrace_append hprefix tailTrace_5628609
  have hstable : (prefixWord ++ tailWord_5628609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628609).length < 2 ^ (prefixWord ++ tailWord_5628609).sum := by decide
  have hdescent : baseEnd_5628609 < baseStart_5628609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628624 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_5628624 : Nat := 118140960795 + 5628624 * 2 ^ 59
def prefixEnd_5628624 : Nat := 4983230072969 + 3 ^ 40 * 5628624 * 2
def baseEnd_5628624 : Nat := 2890189535432491216414435

theorem tailTrace_5628624 : CollatzResearch.WordTrace tailWord_5628624 prefixEnd_5628624 2890189535432491216414435 := by
  unfold tailWord_5628624
  simp only [CollatzResearch.WordTrace]
  refine ⟨102646391380232007645954463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136861855173642676861272617 102646391380232007645954463)
  ·
    refine ⟨153969587070348011468931695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102646391380232007645954463 153969587070348011468931695)
    ·
      refine ⟨230954380605522017203397543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153969587070348011468931695 230954380605522017203397543)
      ·
        refine ⟨346431570908283025805096315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230954380605522017203397543 346431570908283025805096315)
        ·
          refine ⟨519647356362424538707644473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346431570908283025805096315 519647356362424538707644473)
          ·
            refine ⟨389735517271818404030733355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519647356362424538707644473 389735517271818404030733355)
            ·
              refine ⟨584603275907727606046100033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389735517271818404030733355 584603275907727606046100033)
              ·
                refine ⟨438452456930795704534575025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584603275907727606046100033 438452456930795704534575025)
                ·
                  refine ⟨328839342698096778400931269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 438452456930795704534575025 328839342698096778400931269)
                  ·
                    refine ⟨61657376755893145950174613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 328839342698096778400931269 61657376755893145950174613)
                    ·
                      refine ⟨2890189535432491216414435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61657376755893145950174613 2890189535432491216414435)
                      ·
                        rfl

theorem cell23_5628624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_5628624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628624 prefixEnd_5628624 := by exact prefixLift 5628624
  have htrace : WordTrace (prefixWord ++ tailWord_5628624) baseStart_5628624 baseEnd_5628624 := by
    simpa [prefixWord, tailWord_5628624, baseEnd_5628624] using wordTrace_append hprefix tailTrace_5628624
  have hstable : (prefixWord ++ tailWord_5628624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628624).length < 2 ^ (prefixWord ++ tailWord_5628624).sum := by decide
  have hdescent : baseEnd_5628624 < baseStart_5628624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628655 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 5]
def baseStart_5628655 : Nat := 118140960795 + 5628655 * 2 ^ 59
def prefixEnd_5628655 : Nat := 4983230072969 + 3 ^ 40 * 5628655 * 2
def baseEnd_5628655 : Nat := 321133939259197843902977

theorem tailTrace_5628655 : CollatzResearch.WordTrace tailWord_5628655 prefixEnd_5628655 321133939259197843902977 := by
  unfold tailWord_5628655
  simp only [CollatzResearch.WordTrace]
  refine ⟨205293913423351707586287419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136862608948901138390858279 205293913423351707586287419)
  ·
    refine ⟨307940870135027561379431129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205293913423351707586287419 307940870135027561379431129)
    ·
      refine ⟨230955652601270671034573347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307940870135027561379431129 230955652601270671034573347)
      ·
        refine ⟨346433478901906006551860021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230955652601270671034573347 346433478901906006551860021)
        ·
          refine ⟨32478138647053688114236877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346433478901906006551860021 32478138647053688114236877)
          ·
            refine ⟨12179301992645133042838829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32478138647053688114236877 12179301992645133042838829)
            ·
              refine ⟨4567238247241924891064561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12179301992645133042838829 4567238247241924891064561)
              ·
                refine ⟨3425428685431443668298421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4567238247241924891064561 3425428685431443668298421)
                ·
                  refine ⟨321133939259197843902977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3425428685431443668298421 321133939259197843902977)
                  ·
                    rfl

theorem cell23_5628655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 5].length) (baseStart_5628655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628655 prefixEnd_5628655 := by exact prefixLift 5628655
  have htrace : WordTrace (prefixWord ++ tailWord_5628655) baseStart_5628655 baseEnd_5628655 := by
    simpa [prefixWord, tailWord_5628655, baseEnd_5628655] using wordTrace_append hprefix tailTrace_5628655
  have hstable : (prefixWord ++ tailWord_5628655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628655).length < 2 ^ (prefixWord ++ tailWord_5628655).sum := by decide
  have hdescent : baseEnd_5628655 < baseStart_5628655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628671 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4]
def baseStart_5628671 : Nat := 118140960795 + 5628671 * 2 ^ 59
def prefixEnd_5628671 : Nat := 4983230072969 + 3 ^ 40 * 5628671 * 2
def baseEnd_5628671 : Nat := 2890213669023252532526719

theorem tailTrace_5628671 : CollatzResearch.WordTrace tailWord_5628671 prefixEnd_5628671 2890213669023252532526719 := by
  unfold tailWord_5628671
  simp only [CollatzResearch.WordTrace]
  refine ⟨205294496991293742318869867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136862997994195828212579911 205294496991293742318869867)
  ·
    refine ⟨307941745486940613478304801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205294496991293742318869867 307941745486940613478304801)
    ·
      refine ⟨230956309115205460108728601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307941745486940613478304801 230956309115205460108728601)
      ·
        refine ⟨173217231836404095081546451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230956309115205460108728601 173217231836404095081546451)
        ·
          refine ⟨259825847754606142622319677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173217231836404095081546451 259825847754606142622319677)
          ·
            refine ⟨97434692907977303483369879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259825847754606142622319677 97434692907977303483369879)
            ·
              refine ⟨146152039361965955225054819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97434692907977303483369879 146152039361965955225054819)
              ·
                refine ⟨219228059042948932837582229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146152039361965955225054819 219228059042948932837582229)
                ·
                  refine ⟨10276315267638231226761667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 219228059042948932837582229 10276315267638231226761667)
                  ·
                    refine ⟨15414472901457346840142501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10276315267638231226761667 15414472901457346840142501)
                    ·
                      refine ⟨2890213669023252532526719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15414472901457346840142501 2890213669023252532526719)
                      ·
                        rfl

theorem cell23_5628671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_5628671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628671 prefixEnd_5628671 := by exact prefixLift 5628671
  have htrace : WordTrace (prefixWord ++ tailWord_5628671) baseStart_5628671 baseEnd_5628671 := by
    simpa [prefixWord, tailWord_5628671, baseEnd_5628671] using wordTrace_append hprefix tailTrace_5628671
  have hstable : (prefixWord ++ tailWord_5628671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628671).length < 2 ^ (prefixWord ++ tailWord_5628671).sum := by decide
  have hdescent : baseEnd_5628671 < baseStart_5628671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628772 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_5628772 : Nat := 118140960795 + 5628772 * 2 ^ 59
def prefixEnd_5628772 : Nat := 4983230072969 + 3 ^ 40 * 5628772 * 2
def baseEnd_5628772 : Nat := 2890265530569356637363755

theorem tailTrace_5628772 : CollatzResearch.WordTrace tailWord_5628772 prefixEnd_5628772 2890265530569356637363755 := by
  unfold tailWord_5628772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102649090381963918284148285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136865453842618557712197713 102649090381963918284148285)
  ·
    refine ⟨38493408893236469356555607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102649090381963918284148285 38493408893236469356555607)
    ·
      refine ⟨57740113339854704034833411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38493408893236469356555607 57740113339854704034833411)
      ·
        refine ⟨86610170009782056052250117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57740113339854704034833411 86610170009782056052250117)
        ·
          refine ⟨16239406876834135509796897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86610170009782056052250117 16239406876834135509796897)
          ·
            refine ⟨12179555157625601632347673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16239406876834135509796897 12179555157625601632347673)
            ·
              refine ⟨9134666368219201224260755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12179555157625601632347673 9134666368219201224260755)
              ·
                refine ⟨13701999552328801836391133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9134666368219201224260755 13701999552328801836391133)
                ·
                  refine ⟨5138249832123300688646675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13701999552328801836391133 5138249832123300688646675)
                  ·
                    refine ⟨7707374748184951032970013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138249832123300688646675 7707374748184951032970013)
                    ·
                      refine ⟨2890265530569356637363755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707374748184951032970013 2890265530569356637363755)
                      ·
                        rfl

theorem cell23_5628772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_5628772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628772 prefixEnd_5628772 := by exact prefixLift 5628772
  have htrace : WordTrace (prefixWord ++ tailWord_5628772) baseStart_5628772 baseEnd_5628772 := by
    simpa [prefixWord, tailWord_5628772, baseEnd_5628772] using wordTrace_append hprefix tailTrace_5628772
  have hstable : (prefixWord ++ tailWord_5628772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628772).length < 2 ^ (prefixWord ++ tailWord_5628772).sum := by decide
  have hdescent : baseEnd_5628772 < baseStart_5628772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628849 : List Nat := [1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_5628849 : Nat := 118140960795 + 5628849 * 2 ^ 59
def prefixEnd_5628849 : Nat := 4983230072969 + 3 ^ 40 * 5628849 * 2
def baseEnd_5628849 : Nat := 2890305068579752836100901

theorem tailTrace_5628849 : CollatzResearch.WordTrace tailWord_5628849 prefixEnd_5628849 2890305068579752836100901 := by
  unfold tailWord_5628849
  simp only [CollatzResearch.WordTrace]
  refine ⟨205300989184648878718849601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136867326123099252479233067 205300989184648878718849601)
  ·
    refine ⟨153975741888486659039137201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205300989184648878718849601 153975741888486659039137201)
    ·
      refine ⟨115481806416364994279352901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153975741888486659039137201 115481806416364994279352901)
      ·
        refine ⟨21652838703068436427378669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115481806416364994279352901 21652838703068436427378669)
        ·
          refine ⟨8119814513650663660267001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21652838703068436427378669 8119814513650663660267001)
          ·
            refine ⟨6089860885237997745200251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8119814513650663660267001 6089860885237997745200251)
            ·
              refine ⟨9134791327856996617800377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089860885237997745200251 9134791327856996617800377)
              ·
                refine ⟨6851093495892747463350283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9134791327856996617800377 6851093495892747463350283)
                ·
                  refine ⟨10276640243839121195025425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6851093495892747463350283 10276640243839121195025425)
                  ·
                    refine ⟨7707480182879340896269069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10276640243839121195025425 7707480182879340896269069)
                    ·
                      refine ⟨2890305068579752836100901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707480182879340896269069 2890305068579752836100901)
                      ·
                        rfl

theorem cell23_5628849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_5628849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628849 prefixEnd_5628849 := by exact prefixLift 5628849
  have htrace : WordTrace (prefixWord ++ tailWord_5628849) baseStart_5628849 baseEnd_5628849 := by
    simpa [prefixWord, tailWord_5628849, baseEnd_5628849] using wordTrace_append hprefix tailTrace_5628849
  have hstable : (prefixWord ++ tailWord_5628849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628849).length < 2 ^ (prefixWord ++ tailWord_5628849).sum := by decide
  have hdescent : baseEnd_5628849 < baseStart_5628849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628895 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 2, 6]
def baseStart_5628895 : Nat := 118140960795 + 5628895 * 2 ^ 59
def prefixEnd_5628895 : Nat := 4983230072969 + 3 ^ 40 * 5628895 * 2
def baseEnd_5628895 : Nat := 963442896229953218708563

theorem tailTrace_5628895 : CollatzResearch.WordTrace tailWord_5628895 prefixEnd_5628895 963442896229953218708563 := by
  unfold tailWord_5628895
  simp only [CollatzResearch.WordTrace]
  refine ⟨205302666942482228575024139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136868444628321485716682759 205302666942482228575024139)
  ·
    refine ⟨307954000413723342862536209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205302666942482228575024139 307954000413723342862536209)
    ·
      refine ⟨230965500310292507146902157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307954000413723342862536209 230965500310292507146902157)
      ·
        refine ⟨86612062616359690180088309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230965500310292507146902157 86612062616359690180088309)
        ·
          refine ⟨8119880870283720954383279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86612062616359690180088309 8119880870283720954383279)
          ·
            refine ⟨12179821305425581431574919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8119880870283720954383279 12179821305425581431574919)
            ·
              refine ⟨18269731958138372147362379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12179821305425581431574919 18269731958138372147362379)
              ·
                refine ⟨27404597937207558221043569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18269731958138372147362379 27404597937207558221043569)
                ·
                  refine ⟨20553448452905668665782677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27404597937207558221043569 20553448452905668665782677)
                  ·
                    refine ⟨963442896229953218708563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20553448452905668665782677 963442896229953218708563)
                    ·
                      rfl

theorem cell23_5628895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 6].length) (baseStart_5628895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628895 prefixEnd_5628895 := by exact prefixLift 5628895
  have htrace : WordTrace (prefixWord ++ tailWord_5628895) baseStart_5628895 baseEnd_5628895 := by
    simpa [prefixWord, tailWord_5628895, baseEnd_5628895] using wordTrace_append hprefix tailTrace_5628895
  have hstable : (prefixWord ++ tailWord_5628895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628895).length < 2 ^ (prefixWord ++ tailWord_5628895).sum := by decide
  have hdescent : baseEnd_5628895 < baseStart_5628895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628930 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5628930 : Nat := 118140960795 + 5628930 * 2 ^ 59
def prefixEnd_5628930 : Nat := 4983230072969 + 3 ^ 40 * 5628930 * 2
def baseEnd_5628930 : Nat := 2890346660512767019188029

theorem tailTrace_5628930 : CollatzResearch.WordTrace tailWord_5628930 prefixEnd_5628930 2890346660512767019188029 := by
  unfold tailWord_5628930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51325985874338857388137061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136869295664903619701698829 51325985874338857388137061)
  ·
    refine ⟨9623622351438535760275699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51325985874338857388137061 9623622351438535760275699)
    ·
      refine ⟨14435433527157803640413549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623622351438535760275699 14435433527157803640413549)
      ·
        refine ⟨5413287572684176365155081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14435433527157803640413549 5413287572684176365155081)
        ·
          refine ⟨4059965679513132273866311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5413287572684176365155081 4059965679513132273866311)
          ·
            refine ⟨6089948519269698410799467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059965679513132273866311 6089948519269698410799467)
            ·
              refine ⟨9134922778904547616199201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089948519269698410799467 9134922778904547616199201)
              ·
                refine ⟨6851192084178410712149401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9134922778904547616199201 6851192084178410712149401)
                ·
                  refine ⟨5138394063133808034112051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851192084178410712149401 5138394063133808034112051)
                  ·
                    refine ⟨7707591094700712051168077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138394063133808034112051 7707591094700712051168077)
                    ·
                      refine ⟨2890346660512767019188029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707591094700712051168077 2890346660512767019188029)
                      ·
                        rfl

theorem cell23_5628930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5628930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628930 prefixEnd_5628930 := by exact prefixLift 5628930
  have htrace : WordTrace (prefixWord ++ tailWord_5628930) baseStart_5628930 baseEnd_5628930 := by
    simpa [prefixWord, tailWord_5628930, baseEnd_5628930] using wordTrace_append hprefix tailTrace_5628930
  have hstable : (prefixWord ++ tailWord_5628930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628930).length < 2 ^ (prefixWord ++ tailWord_5628930).sum := by decide
  have hdescent : baseEnd_5628930 < baseStart_5628930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628935 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3]
def baseStart_5628935 : Nat := 118140960795 + 5628935 * 2 ^ 59
def prefixEnd_5628935 : Nat := 4983230072969 + 3 ^ 40 * 5628935 * 2
def baseEnd_5628935 : Nat := 2890349227916039499625505

theorem tailTrace_5628935 : CollatzResearch.WordTrace tailWord_5628935 prefixEnd_5628935 2890349227916039499625505 := by
  unfold tailWord_5628935
  simp only [CollatzResearch.WordTrace]
  refine ⟨205304125862337315406480259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136869417241558210270986839 205304125862337315406480259)
  ·
    refine ⟨307956188793505973109720389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205304125862337315406480259 307956188793505973109720389)
    ·
      refine ⟨57741785398782369958072573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307956188793505973109720389 57741785398782369958072573)
      ·
        refine ⟨21653169524543388734277215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57741785398782369958072573 21653169524543388734277215)
        ·
          refine ⟨32479754286815083101415823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21653169524543388734277215 32479754286815083101415823)
          ·
            refine ⟨48719631430222624652123735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32479754286815083101415823 48719631430222624652123735)
            ·
              refine ⟨73079447145333936978185603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48719631430222624652123735 73079447145333936978185603)
              ·
                refine ⟨109619170718000905467278405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73079447145333936978185603 109619170718000905467278405)
                ·
                  refine ⟨20553594509625169775114701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109619170718000905467278405 20553594509625169775114701)
                  ·
                    refine ⟨7707597941109438665668013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20553594509625169775114701 7707597941109438665668013)
                    ·
                      refine ⟨2890349227916039499625505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707597941109438665668013 2890349227916039499625505)
                      ·
                        rfl

theorem cell23_5628935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_5628935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628935 prefixEnd_5628935 := by exact prefixLift 5628935
  have htrace : WordTrace (prefixWord ++ tailWord_5628935) baseStart_5628935 baseEnd_5628935 := by
    simpa [prefixWord, tailWord_5628935, baseEnd_5628935] using wordTrace_append hprefix tailTrace_5628935
  have hstable : (prefixWord ++ tailWord_5628935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628935).length < 2 ^ (prefixWord ++ tailWord_5628935).sum := by decide
  have hdescent : baseEnd_5628935 < baseStart_5628935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628936 : List Nat := [2, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_5628936 : Nat := 118140960795 + 5628936 * 2 ^ 59
def prefixEnd_5628936 : Nat := 4983230072969 + 3 ^ 40 * 5628936 * 2
def baseEnd_5628936 : Nat := 2890349741396693995713001

theorem tailTrace_5628936 : CollatzResearch.WordTrace tailWord_5628936 prefixEnd_5628936 2890349741396693995713001 := by
  unfold tailWord_5628936
  simp only [CollatzResearch.WordTrace]
  refine ⟨102652081167666846288633331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136869441556889128384844441 102652081167666846288633331)
  ·
    refine ⟨153978121751500269432949997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102652081167666846288633331 153978121751500269432949997)
    ·
      refine ⟨57741795656812601037356249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153978121751500269432949997 57741795656812601037356249)
      ·
        refine ⟨43306346742609450778017187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57741795656812601037356249 43306346742609450778017187)
        ·
          refine ⟨64959520113914176167025781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43306346742609450778017187 64959520113914176167025781)
          ·
            refine ⟨6089955010679454015658667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64959520113914176167025781 6089955010679454015658667)
            ·
              refine ⟨9134932516019181023488001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6089955010679454015658667 9134932516019181023488001)
              ·
                refine ⟨6851199387014385767616001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9134932516019181023488001 6851199387014385767616001)
                ·
                  refine ⟨5138399540260789325712001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851199387014385767616001 5138399540260789325712001)
                  ·
                    refine ⟨3853799655195591994284001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5138399540260789325712001 3853799655195591994284001)
                    ·
                      refine ⟨2890349741396693995713001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853799655195591994284001 2890349741396693995713001)
                      ·
                        rfl

theorem cell23_5628936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_5628936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628936 prefixEnd_5628936 := by exact prefixLift 5628936
  have htrace : WordTrace (prefixWord ++ tailWord_5628936) baseStart_5628936 baseEnd_5628936 := by
    simpa [prefixWord, tailWord_5628936, baseEnd_5628936] using wordTrace_append hprefix tailTrace_5628936
  have hstable : (prefixWord ++ tailWord_5628936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628936).length < 2 ^ (prefixWord ++ tailWord_5628936).sum := by decide
  have hdescent : baseEnd_5628936 < baseStart_5628936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628942 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_5628942 : Nat := 118140960795 + 5628942 * 2 ^ 59
def prefixEnd_5628942 : Nat := 4983230072969 + 3 ^ 40 * 5628942 * 2
def baseEnd_5628942 : Nat := 321150313586735663581997

theorem tailTrace_5628942 : CollatzResearch.WordTrace tailWord_5628942 prefixEnd_5628942 321150313586735663581997 := by
  unfold tailWord_5628942
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663047646663994450248135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136869587448874637067990053 25663047646663994450248135)
  ·
    refine ⟨38494571469995991675372203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25663047646663994450248135 38494571469995991675372203)
    ·
      refine ⟨57741857204993987513058305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38494571469995991675372203 57741857204993987513058305)
      ·
        refine ⟨43306392903745490634793729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57741857204993987513058305 43306392903745490634793729)
        ·
          refine ⟨32479794677809117976095297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43306392903745490634793729 32479794677809117976095297)
          ·
            refine ⟨24359846008356838482071473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32479794677809117976095297 24359846008356838482071473)
            ·
              refine ⟨18269884506267628861553605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24359846008356838482071473 18269884506267628861553605)
              ·
                refine ⟨3425603344925180411541301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18269884506267628861553605 3425603344925180411541301)
                ·
                  refine ⟨321150313586735663581997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3425603344925180411541301 321150313586735663581997)
                  ·
                    rfl

theorem cell23_5628942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_5628942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628942 prefixEnd_5628942 := by exact prefixLift 5628942
  have htrace : WordTrace (prefixWord ++ tailWord_5628942) baseStart_5628942 baseEnd_5628942 := by
    simpa [prefixWord, tailWord_5628942, baseEnd_5628942] using wordTrace_append hprefix tailTrace_5628942
  have hstable : (prefixWord ++ tailWord_5628942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628942).length < 2 ^ (prefixWord ++ tailWord_5628942).sum := by decide
  have hdescent : baseEnd_5628942 < baseStart_5628942 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5628945 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 1, 7, 2]
def baseStart_5628945 : Nat := 118140960795 + 5628945 * 2 ^ 59
def prefixEnd_5628945 : Nat := 4983230072969 + 3 ^ 40 * 5628945 * 2
def baseEnd_5628945 : Nat := 2890354362722584460500459

theorem tailTrace_5628945 : CollatzResearch.WordTrace tailWord_5628945 prefixEnd_5628945 2890354362722584460500459 := by
  unfold tailWord_5628945
  simp only [CollatzResearch.WordTrace]
  refine ⟨205304490592301087114344289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136869660394867391409562859 205304490592301087114344289)
  ·
    refine ⟨153978367944225815335758217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205304490592301087114344289 153978367944225815335758217)
    ·
      refine ⟨115483775958169361501818663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153978367944225815335758217 115483775958169361501818663)
      ·
        refine ⟨173225663937254042252727995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115483775958169361501818663 173225663937254042252727995)
        ·
          refine ⟨259838495905881063379091993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173225663937254042252727995 259838495905881063379091993)
          ·
            refine ⟨194878871929410797534318995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259838495905881063379091993 194878871929410797534318995)
            ·
              refine ⟨292318307894116196301478493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194878871929410797534318995 292318307894116196301478493)
              ·
                refine ⟨109619365460293573613054435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292318307894116196301478493 109619365460293573613054435)
                ·
                  refine ⟨164429048190440360419581653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109619365460293573613054435 164429048190440360419581653)
                  ·
                    refine ⟨3853805816963445947333945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 164429048190440360419581653 3853805816963445947333945)
                    ·
                      refine ⟨2890354362722584460500459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853805816963445947333945 2890354362722584460500459)
                      ·
                        rfl

theorem cell23_5628945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 7, 2].length) (baseStart_5628945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5628945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5628945 prefixEnd_5628945 := by exact prefixLift 5628945
  have htrace : WordTrace (prefixWord ++ tailWord_5628945) baseStart_5628945 baseEnd_5628945 := by
    simpa [prefixWord, tailWord_5628945, baseEnd_5628945] using wordTrace_append hprefix tailTrace_5628945
  have hstable : (prefixWord ++ tailWord_5628945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5628945).length < 2 ^ (prefixWord ++ tailWord_5628945).sum := by decide
  have hdescent : baseEnd_5628945 < baseStart_5628945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5628945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629002 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_5629002 : Nat := 118140960795 + 5629002 * 2 ^ 59
def prefixEnd_5629002 : Nat := 4983230072969 + 3 ^ 40 * 5629002 * 2
def baseEnd_5629002 : Nat := 963461210373296912495899

theorem tailTrace_5629002 : CollatzResearch.WordTrace tailWord_5629002 prefixEnd_5629002 963461210373296912495899 := by
  unfold tailWord_5629002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51326642388273646462292315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136871046368729723899446173 51326642388273646462292315)
  ·
    refine ⟨76989963582410469693438473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51326642388273646462292315 76989963582410469693438473)
    ·
      refine ⟨57742472686807852270078855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76989963582410469693438473 57742472686807852270078855)
      ·
        refine ⟨86613709030211778405118283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57742472686807852270078855 86613709030211778405118283)
        ·
          refine ⟨129920563545317667607677425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86613709030211778405118283 129920563545317667607677425)
          ·
            refine ⟨97440422658988250705758069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129920563545317667607677425 97440422658988250705758069)
            ·
              refine ⟨9135039624280148503664819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97440422658988250705758069 9135039624280148503664819)
              ·
                refine ⟨13702559436420222755497229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135039624280148503664819 13702559436420222755497229)
                ·
                  refine ⟨5138459788657583533311461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13702559436420222755497229 5138459788657583533311461)
                  ·
                    refine ⟨963461210373296912495899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138459788657583533311461 963461210373296912495899)
                    ·
                      rfl

theorem cell23_5629002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_5629002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629002 prefixEnd_5629002 := by exact prefixLift 5629002
  have htrace : WordTrace (prefixWord ++ tailWord_5629002) baseStart_5629002 baseEnd_5629002 := by
    simpa [prefixWord, tailWord_5629002, baseEnd_5629002] using wordTrace_append hprefix tailTrace_5629002
  have hstable : (prefixWord ++ tailWord_5629002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629002).length < 2 ^ (prefixWord ++ tailWord_5629002).sum := by decide
  have hdescent : baseEnd_5629002 < baseStart_5629002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629025 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 3]
def baseStart_5629025 : Nat := 118140960795 + 5629025 * 2 ^ 59
def prefixEnd_5629025 : Nat := 4983230072969 + 3 ^ 40 * 5629025 * 2
def baseEnd_5629025 : Nat := 2890395441174944147500091

theorem tailTrace_5629025 : CollatzResearch.WordTrace tailWord_5629025 prefixEnd_5629025 2890395441174944147500091 := by
  unfold tailWord_5629025
  simp only [CollatzResearch.WordTrace]
  refine ⟨205307408432011260777256529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136871605621340840518171019 205307408432011260777256529)
  ·
    refine ⟨153980556324008445582942397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205307408432011260777256529 153980556324008445582942397)
    ·
      refine ⟨57742708621503167093603399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153980556324008445582942397 57742708621503167093603399)
      ·
        refine ⟨86614062932254750640405099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57742708621503167093603399 86614062932254750640405099)
        ·
          refine ⟨129921094398382125960607649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86614062932254750640405099 129921094398382125960607649)
          ·
            refine ⟨97440820798786594470455737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129921094398382125960607649 97440820798786594470455737)
            ·
              refine ⟨73080615599089945852841803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97440820798786594470455737 73080615599089945852841803)
              ·
                refine ⟨109620923398634918779262705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73080615599089945852841803 109620923398634918779262705)
                ·
                  refine ⟨82215692548976189084447029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109620923398634918779262705 82215692548976189084447029)
                  ·
                    refine ⟨7707721176466517726666909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82215692548976189084447029 7707721176466517726666909)
                    ·
                      refine ⟨2890395441174944147500091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707721176466517726666909 2890395441174944147500091)
                      ·
                        rfl

theorem cell23_5629025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_5629025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629025 prefixEnd_5629025 := by exact prefixLift 5629025
  have htrace : WordTrace (prefixWord ++ tailWord_5629025) baseStart_5629025 baseEnd_5629025 := by
    simpa [prefixWord, tailWord_5629025, baseEnd_5629025] using wordTrace_append hprefix tailTrace_5629025
  have hstable : (prefixWord ++ tailWord_5629025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629025).length < 2 ^ (prefixWord ++ tailWord_5629025).sum := by decide
  have hdescent : baseEnd_5629025 < baseStart_5629025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629075 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 6]
def baseStart_5629075 : Nat := 118140960795 + 5629075 * 2 ^ 59
def prefixEnd_5629075 : Nat := 4983230072969 + 3 ^ 40 * 5629075 * 2
def baseEnd_5629075 : Nat := 963473705069222983958287

theorem tailTrace_5629075 : CollatzResearch.WordTrace tailWord_5629075 prefixEnd_5629075 963473705069222983958287 := by
  unfold tailWord_5629075
  simp only [CollatzResearch.WordTrace]
  refine ⟨205309232081830119316576679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136872821387886746211051119 205309232081830119316576679)
  ·
    refine ⟨307963848122745178974865019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205309232081830119316576679 307963848122745178974865019)
    ·
      refine ⟨461945772184117768462297529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307963848122745178974865019 461945772184117768462297529)
      ·
        refine ⟨346459329138088326346723147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461945772184117768462297529 346459329138088326346723147)
        ·
          refine ⟨519688993707132489520084721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346459329138088326346723147 519688993707132489520084721)
          ·
            refine ⟨389766745280349367140063541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519688993707132489520084721 389766745280349367140063541)
            ·
              refine ⟨36540632370032753169380957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 389766745280349367140063541 36540632370032753169380957)
              ·
                refine ⟨13702737138762282438517859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36540632370032753169380957 13702737138762282438517859)
                ·
                  refine ⟨20554105708143423657776789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13702737138762282438517859 20554105708143423657776789)
                  ·
                    refine ⟨963473705069222983958287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20554105708143423657776789 963473705069222983958287)
                    ·
                      rfl

theorem cell23_5629075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 6].length) (baseStart_5629075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629075 prefixEnd_5629075 := by exact prefixLift 5629075
  have htrace : WordTrace (prefixWord ++ tailWord_5629075) baseStart_5629075 baseEnd_5629075 := by
    simpa [prefixWord, tailWord_5629075, baseEnd_5629075] using wordTrace_append hprefix tailTrace_5629075
  have hstable : (prefixWord ++ tailWord_5629075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629075).length < 2 ^ (prefixWord ++ tailWord_5629075).sum := by decide
  have hdescent : baseEnd_5629075 < baseStart_5629075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629086 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5629086 : Nat := 118140960795 + 5629086 * 2 ^ 59
def prefixEnd_5629086 : Nat := 4983230072969 + 3 ^ 40 * 5629086 * 2
def baseEnd_5629086 : Nat := 2890426763494868408837311

theorem tailTrace_5629086 : CollatzResearch.WordTrace tailWord_5629086 prefixEnd_5629086 2890426763494868408837311 := by
  unfold tailWord_5629086
  simp only [CollatzResearch.WordTrace]
  refine ⟨25663704160598783524403389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136873088856526845463484741 25663704160598783524403389)
  ·
    refine ⟨9623889060224543821651271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25663704160598783524403389 9623889060224543821651271)
    ·
      refine ⟨14435833590336815732476907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9623889060224543821651271 14435833590336815732476907)
      ·
        refine ⟨21653750385505223598715361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14435833590336815732476907 21653750385505223598715361)
        ·
          refine ⟨16240312789128917699036521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21653750385505223598715361 16240312789128917699036521)
          ·
            refine ⟨12180234591846688274277391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16240312789128917699036521 12180234591846688274277391)
            ·
              refine ⟨18270351887770032411416087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12180234591846688274277391 18270351887770032411416087)
              ·
                refine ⟨27405527831655048617124131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18270351887770032411416087 27405527831655048617124131)
                ·
                  refine ⟨41108291747482572925686197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27405527831655048617124131 41108291747482572925686197)
                  ·
                    refine ⟨3853902351326491211783081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41108291747482572925686197 3853902351326491211783081)
                    ·
                      refine ⟨2890426763494868408837311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853902351326491211783081 2890426763494868408837311)
                      ·
                        rfl

theorem cell23_5629086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5629086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629086 prefixEnd_5629086 := by exact prefixLift 5629086
  have htrace : WordTrace (prefixWord ++ tailWord_5629086) baseStart_5629086 baseEnd_5629086 := by
    simpa [prefixWord, tailWord_5629086, baseEnd_5629086] using wordTrace_append hprefix tailTrace_5629086
  have hstable : (prefixWord ++ tailWord_5629086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629086).length < 2 ^ (prefixWord ++ tailWord_5629086).sum := by decide
  have hdescent : baseEnd_5629086 < baseStart_5629086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629092 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_5629092 : Nat := 118140960795 + 5629092 * 2 ^ 59
def prefixEnd_5629092 : Nat := 4983230072969 + 3 ^ 40 * 5629092 * 2
def baseEnd_5629092 : Nat := 963476614792931795120761

theorem tailTrace_5629092 : CollatzResearch.WordTrace tailWord_5629092 prefixEnd_5629092 963476614792931795120761 := by
  unfold tailWord_5629092
  simp only [CollatzResearch.WordTrace]
  refine ⟨102654926061384265609972765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136873234748512354146630353 102654926061384265609972765)
  ·
    refine ⟨38495597273019099603739787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102654926061384265609972765 38495597273019099603739787)
    ·
      refine ⟨57743395909528649405609681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38495597273019099603739787 57743395909528649405609681)
      ·
        refine ⟨43307546932146487054207261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57743395909528649405609681 43307546932146487054207261)
        ·
          refine ⟨16240330099554932645327723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43307546932146487054207261 16240330099554932645327723)
          ·
            refine ⟨24360495149332398967991585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16240330099554932645327723 24360495149332398967991585)
            ·
              refine ⟨18270371361999299225993689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24360495149332398967991585 18270371361999299225993689)
              ·
                refine ⟨13702778521499474419495267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18270371361999299225993689 13702778521499474419495267)
                ·
                  refine ⟨20554167782249211629242901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13702778521499474419495267 20554167782249211629242901)
                  ·
                    refine ⟨963476614792931795120761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20554167782249211629242901 963476614792931795120761)
                    ·
                      rfl

theorem cell23_5629092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_5629092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629092 prefixEnd_5629092 := by exact prefixLift 5629092
  have htrace : WordTrace (prefixWord ++ tailWord_5629092) baseStart_5629092 baseEnd_5629092 := by
    simpa [prefixWord, tailWord_5629092, baseEnd_5629092] using wordTrace_append hprefix tailTrace_5629092
  have hstable : (prefixWord ++ tailWord_5629092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629092).length < 2 ^ (prefixWord ++ tailWord_5629092).sum := by decide
  have hdescent : baseEnd_5629092 < baseStart_5629092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629110 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_5629110 : Nat := 118140960795 + 5629110 * 2 ^ 59
def prefixEnd_5629110 : Nat := 4983230072969 + 3 ^ 40 * 5629110 * 2
def baseEnd_5629110 : Nat := 2890439087030576314937201

theorem tailTrace_5629110 : CollatzResearch.WordTrace tailWord_5629110 prefixEnd_5629110 2890439087030576314937201 := by
  unfold tailWord_5629110
  simp only [CollatzResearch.WordTrace]
  refine ⟨12831906789793957518381299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136873672424468880196067189 12831906789793957518381299)
  ·
    refine ⟨19247860184690936277571949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12831906789793957518381299 19247860184690936277571949)
    ·
      refine ⟨7217947569259101104089481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19247860184690936277571949 7217947569259101104089481)
      ·
        refine ⟨5413460676944325828067111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7217947569259101104089481 5413460676944325828067111)
        ·
          refine ⟨8120191015416488742100667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413460676944325828067111 8120191015416488742100667)
          ·
            refine ⟨12180286523124733113151001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120191015416488742100667 12180286523124733113151001)
            ·
              refine ⟨9135214892343549834863251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12180286523124733113151001 9135214892343549834863251)
              ·
                refine ⟨13702822338515324752294877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135214892343549834863251 13702822338515324752294877)
                ·
                  refine ⟨5138558376943246782110579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13702822338515324752294877 5138558376943246782110579)
                  ·
                    refine ⟨7707837565414870173165869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138558376943246782110579 7707837565414870173165869)
                    ·
                      refine ⟨2890439087030576314937201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707837565414870173165869 2890439087030576314937201)
                      ·
                        rfl

theorem cell23_5629110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_5629110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629110 prefixEnd_5629110 := by exact prefixLift 5629110
  have htrace : WordTrace (prefixWord ++ tailWord_5629110) baseStart_5629110 baseEnd_5629110 := by
    simpa [prefixWord, tailWord_5629110, baseEnd_5629110] using wordTrace_append hprefix tailTrace_5629110
  have hstable : (prefixWord ++ tailWord_5629110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629110).length < 2 ^ (prefixWord ++ tailWord_5629110).sum := by decide
  have hdescent : baseEnd_5629110 < baseStart_5629110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629116 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5629116 : Nat := 118140960795 + 5629116 * 2 ^ 59
def prefixEnd_5629116 : Nat := 4983230072969 + 3 ^ 40 * 5629116 * 2
def baseEnd_5629116 : Nat := 2890442167914503291462173

theorem tailTrace_5629116 : CollatzResearch.WordTrace tailWord_5629116 prefixEnd_5629116 2890442167914503291462173 := by
  unfold tailWord_5629116
  simp only [CollatzResearch.WordTrace]
  refine ⟨102655363737340791659409601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136873818316454388879212801 102655363737340791659409601)
  ·
    refine ⟨76991522803005593744557201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102655363737340791659409601 76991522803005593744557201)
    ·
      refine ⟨57743642102254195308417901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76991522803005593744557201 57743642102254195308417901)
      ·
        refine ⟨21653865788345323240656713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57743642102254195308417901 21653865788345323240656713)
        ·
          refine ⟨16240399341258992430492535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21653865788345323240656713 16240399341258992430492535)
          ·
            refine ⟨24360599011888488645738803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16240399341258992430492535 24360599011888488645738803)
            ·
              refine ⟨36540898517832732968608205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24360599011888488645738803 36540898517832732968608205)
              ·
                refine ⟨13702836944187274863228077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36540898517832732968608205 13702836944187274863228077)
                ·
                  refine ⟨5138563854070228073710529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13702836944187274863228077 5138563854070228073710529)
                  ·
                    refine ⟨3853922890552671055282897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5138563854070228073710529 3853922890552671055282897)
                    ·
                      refine ⟨2890442167914503291462173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853922890552671055282897 2890442167914503291462173)
                      ·
                        rfl

theorem cell23_5629116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5629116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629116 prefixEnd_5629116 := by exact prefixLift 5629116
  have htrace : WordTrace (prefixWord ++ tailWord_5629116) baseStart_5629116 baseEnd_5629116 := by
    simpa [prefixWord, tailWord_5629116, baseEnd_5629116] using wordTrace_append hprefix tailTrace_5629116
  have hstable : (prefixWord ++ tailWord_5629116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629116).length < 2 ^ (prefixWord ++ tailWord_5629116).sum := by decide
  have hdescent : baseEnd_5629116 < baseStart_5629116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629183 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 2, 1, 3]
def baseStart_5629183 : Nat := 118140960795 + 5629183 * 2 ^ 59
def prefixEnd_5629183 : Nat := 4983230072969 + 3 ^ 40 * 5629183 * 2
def baseEnd_5629183 : Nat := 2890476571118354529324365

theorem tailTrace_5629183 : CollatzResearch.WordTrace tailWord_5629183 prefixEnd_5629183 2890476571118354529324365 := by
  unfold tailWord_5629183
  simp only [CollatzResearch.WordTrace]
  refine ⟨205313171165438853761508203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136875447443625902507672135 205313171165438853761508203)
  ·
    refine ⟨307969756748158280642262305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205313171165438853761508203 307969756748158280642262305)
    ·
      refine ⟨230977317561118710481696729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307969756748158280642262305 230977317561118710481696729)
      ·
        refine ⟨173232988170839032861272547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230977317561118710481696729 173232988170839032861272547)
        ·
          refine ⟨259849482256258549291908821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173232988170839032861272547 259849482256258549291908821)
          ·
            refine ⟨6090222240381059749029113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 259849482256258549291908821 6090222240381059749029113)
            ·
              refine ⟨4567666680285794811771835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6090222240381059749029113 4567666680285794811771835)
              ·
                refine ⟨6851500020428692217657753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567666680285794811771835 6851500020428692217657753)
                ·
                  refine ⟨5138625015321519163243315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851500020428692217657753 5138625015321519163243315)
                  ·
                    refine ⟨7707937522982278744864973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5138625015321519163243315 7707937522982278744864973)
                    ·
                      refine ⟨2890476571118354529324365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7707937522982278744864973 2890476571118354529324365)
                      ·
                        rfl

theorem cell23_5629183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 2, 1, 3].length) (baseStart_5629183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629183 prefixEnd_5629183 := by exact prefixLift 5629183
  have htrace : WordTrace (prefixWord ++ tailWord_5629183) baseStart_5629183 baseEnd_5629183 := by
    simpa [prefixWord, tailWord_5629183, baseEnd_5629183] using wordTrace_append hprefix tailTrace_5629183
  have hstable : (prefixWord ++ tailWord_5629183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629183).length < 2 ^ (prefixWord ++ tailWord_5629183).sum := by decide
  have hdescent : baseEnd_5629183 < baseStart_5629183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629189 : List Nat := [1, 3, 1, 1, 2, 1, 4, 3, 1, 4, 2]
def baseStart_5629189 : Nat := 118140960795 + 5629189 * 2 ^ 59
def prefixEnd_5629189 : Nat := 4983230072969 + 3 ^ 40 * 5629189 * 2
def baseEnd_5629189 : Nat := 2890479652002281505849337

theorem tailTrace_5629189 : CollatzResearch.WordTrace tailWord_5629189 prefixEnd_5629189 2890479652002281505849337 := by
  unfold tailWord_5629189
  simp only [CollatzResearch.WordTrace]
  refine ⟨205313390003417116786226621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136875593335611411190817747 205313390003417116786226621)
  ·
    refine ⟨76992521251281418794834983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205313390003417116786226621 76992521251281418794834983)
    ·
      refine ⟨115488781876922128192252475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76992521251281418794834983 115488781876922128192252475)
      ·
        refine ⟨173233172815383192288378713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115488781876922128192252475 173233172815383192288378713)
        ·
          refine ⟨129924879611537394216284035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173233172815383192288378713 129924879611537394216284035)
          ·
            refine ⟨194887319417306091324426053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129924879611537394216284035 194887319417306091324426053)
            ·
              refine ⟨36541372390744892123329885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194887319417306091324426053 36541372390744892123329885)
              ·
                refine ⟨13703014646529334546248707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36541372390744892123329885 13703014646529334546248707)
                ·
                  refine ⟨20554521969794001819373061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13703014646529334546248707 20554521969794001819373061)
                  ·
                    refine ⟨3853972869336375341132449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20554521969794001819373061 3853972869336375341132449)
                    ·
                      refine ⟨2890479652002281505849337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3853972869336375341132449 2890479652002281505849337)
                      ·
                        rfl

theorem cell23_5629189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_5629189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629189 prefixEnd_5629189 := by exact prefixLift 5629189
  have htrace : WordTrace (prefixWord ++ tailWord_5629189) baseStart_5629189 baseEnd_5629189 := by
    simpa [prefixWord, tailWord_5629189, baseEnd_5629189] using wordTrace_append hprefix tailTrace_5629189
  have hstable : (prefixWord ++ tailWord_5629189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629189).length < 2 ^ (prefixWord ++ tailWord_5629189).sum := by decide
  have hdescent : baseEnd_5629189 < baseStart_5629189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629242 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_5629242 : Nat := 118140960795 + 5629242 * 2 ^ 59
def prefixEnd_5629242 : Nat := 4983230072969 + 3 ^ 40 * 5629242 * 2
def baseEnd_5629242 : Nat := 963502288825656599495531

theorem tailTrace_5629242 : CollatzResearch.WordTrace tailWord_5629242 prefixEnd_5629242 963502288825656599495531 := by
  unfold tailWord_5629242
  simp only [CollatzResearch.WordTrace]
  refine ⟨51328830768056276709476495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136876882048150071225270653 51328830768056276709476495)
  ·
    refine ⟨76993246152084415064214743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51328830768056276709476495 76993246152084415064214743)
    ·
      refine ⟨115489869228126622596322115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76993246152084415064214743 115489869228126622596322115)
      ·
        refine ⟨173234803842189933894483173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115489869228126622596322115 173234803842189933894483173)
        ·
          refine ⟨32481525720410612605215595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173234803842189933894483173 32481525720410612605215595)
          ·
            refine ⟨48722288580615918907823393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32481525720410612605215595 48722288580615918907823393)
            ·
              refine ⟨36541716435461939180867545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48722288580615918907823393 36541716435461939180867545)
              ·
                refine ⟨27406287326596454385650659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36541716435461939180867545 27406287326596454385650659)
                ·
                  refine ⟨41109430989894681578475989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27406287326596454385650659 41109430989894681578475989)
                  ·
                    refine ⟨963502288825656599495531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41109430989894681578475989 963502288825656599495531)
                    ·
                      rfl

theorem cell23_5629242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_5629242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629242 prefixEnd_5629242 := by exact prefixLift 5629242
  have htrace : WordTrace (prefixWord ++ tailWord_5629242) baseStart_5629242 baseEnd_5629242 := by
    simpa [prefixWord, tailWord_5629242, baseEnd_5629242] using wordTrace_append hprefix tailTrace_5629242
  have hstable : (prefixWord ++ tailWord_5629242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629242).length < 2 ^ (prefixWord ++ tailWord_5629242).sum := by decide
  have hdescent : baseEnd_5629242 < baseStart_5629242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629340 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_5629340 : Nat := 118140960795 + 5629340 * 2 ^ 59
def prefixEnd_5629340 : Nat := 4983230072969 + 3 ^ 40 * 5629340 * 2
def baseEnd_5629340 : Nat := 963519062527036805020381

theorem tailTrace_5629340 : CollatzResearch.WordTrace tailWord_5629340 prefixEnd_5629340 963519062527036805020381 := by
  unfold tailWord_5629340
  simp only [CollatzResearch.WordTrace]
  refine ⟨102659448712935034787486737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136879264950580046383315649 102659448712935034787486737)
  ·
    refine ⟨76994586534701276090615053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102659448712935034787486737 76994586534701276090615053)
    ·
      refine ⟨28872969950512978533980645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76994586534701276090615053 28872969950512978533980645)
      ·
        refine ⟨5413681865721183475121371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28872969950512978533980645 5413681865721183475121371)
        ·
          refine ⟨8120522798581775212682057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413681865721183475121371 8120522798581775212682057)
          ·
            refine ⟨6090392098936331409511543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8120522798581775212682057 6090392098936331409511543)
            ·
              refine ⟨9135588148404497114267315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090392098936331409511543 9135588148404497114267315)
              ·
                refine ⟨13703382222606745671400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135588148404497114267315 13703382222606745671400973)
                ·
                  refine ⟨5138768333477529626775365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13703382222606745671400973 5138768333477529626775365)
                  ·
                    refine ⟨963519062527036805020381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138768333477529626775365 963519062527036805020381)
                    ·
                      rfl

theorem cell23_5629340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_5629340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629340 prefixEnd_5629340 := by exact prefixLift 5629340
  have htrace : WordTrace (prefixWord ++ tailWord_5629340) baseStart_5629340 baseEnd_5629340 := by
    simpa [prefixWord, tailWord_5629340, baseEnd_5629340] using wordTrace_append hprefix tailTrace_5629340
  have hstable : (prefixWord ++ tailWord_5629340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629340).length < 2 ^ (prefixWord ++ tailWord_5629340).sum := by decide
  have hdescent : baseEnd_5629340 < baseStart_5629340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629373 : List Nat := [1, 4, 1, 2, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5629373 : Nat := 118140960795 + 5629373 * 2 ^ 59
def prefixEnd_5629373 : Nat := 4983230072969 + 3 ^ 40 * 5629373 * 2
def baseEnd_5629373 : Nat := 2890574132442708785948491

theorem tailTrace_5629373 : CollatzResearch.WordTrace tailWord_5629373 prefixEnd_5629373 2890574132442708785948491 := by
  unfold tailWord_5629373
  simp only [CollatzResearch.WordTrace]
  refine ⟨205320101034750516210924773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136880067356500344140616515 205320101034750516210924773)
  ·
    refine ⟨38497518944015721789548395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205320101034750516210924773 38497518944015721789548395)
    ·
      refine ⟨57746278416023582684322593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38497518944015721789548395 57746278416023582684322593)
      ·
        refine ⟨43309708812017687013241945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57746278416023582684322593 43309708812017687013241945)
        ·
          refine ⟨32482281609013265259931459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43309708812017687013241945 32482281609013265259931459)
          ·
            refine ⟨48723422413519897889897189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32482281609013265259931459 48723422413519897889897189)
            ·
              refine ⟨9135641702534980854355723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48723422413519897889897189 9135641702534980854355723)
              ·
                refine ⟨13703462553802471281533585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135641702534980854355723 13703462553802471281533585)
                ·
                  refine ⟨10277596915351853461150189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13703462553802471281533585 10277596915351853461150189)
                  ·
                    refine ⟨3854098843256945047931321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10277596915351853461150189 3854098843256945047931321)
                    ·
                      refine ⟨2890574132442708785948491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854098843256945047931321 2890574132442708785948491)
                      ·
                        rfl

theorem cell23_5629373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5629373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629373 prefixEnd_5629373 := by exact prefixLift 5629373
  have htrace : WordTrace (prefixWord ++ tailWord_5629373) baseStart_5629373 baseEnd_5629373 := by
    simpa [prefixWord, tailWord_5629373, baseEnd_5629373] using wordTrace_append hprefix tailTrace_5629373
  have hstable : (prefixWord ++ tailWord_5629373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629373).length < 2 ^ (prefixWord ++ tailWord_5629373).sum := by decide
  have hdescent : baseEnd_5629373 < baseStart_5629373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629379 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 6, 4]
def baseStart_5629379 : Nat := 118140960795 + 5629379 * 2 ^ 59
def prefixEnd_5629379 : Nat := 4983230072969 + 3 ^ 40 * 5629379 * 2
def baseEnd_5629379 : Nat := 963525737775545254157821

theorem tailTrace_5629379 : CollatzResearch.WordTrace tailWord_5629379 prefixEnd_5629379 963525737775545254157821 := by
  unfold tailWord_5629379
  simp only [CollatzResearch.WordTrace]
  refine ⟨205320319872728779235643191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136880213248485852823762127 205320319872728779235643191)
  ·
    refine ⟨307980479809093168853464787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205320319872728779235643191 307980479809093168853464787)
    ·
      refine ⟨461970719713639753280197181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307980479809093168853464787 461970719713639753280197181)
      ·
        refine ⟨173239019892614907480073943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461970719713639753280197181 173239019892614907480073943)
        ·
          refine ⟨259858529838922361220110915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173239019892614907480073943 259858529838922361220110915)
          ·
            refine ⟨389787794758383541830166373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259858529838922361220110915 389787794758383541830166373)
            ·
              refine ⟨73085211517196914093156195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 389787794758383541830166373 73085211517196914093156195)
              ·
                refine ⟨109627817275795371139734293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73085211517196914093156195 109627817275795371139734293)
                ·
                  refine ⟨5138803934802908022175045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109627817275795371139734293 5138803934802908022175045)
                  ·
                    refine ⟨963525737775545254157821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138803934802908022175045 963525737775545254157821)
                    ·
                      rfl

theorem cell23_5629379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 4].length) (baseStart_5629379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629379 prefixEnd_5629379 := by exact prefixLift 5629379
  have htrace : WordTrace (prefixWord ++ tailWord_5629379) baseStart_5629379 baseEnd_5629379 := by
    simpa [prefixWord, tailWord_5629379, baseEnd_5629379] using wordTrace_append hprefix tailTrace_5629379
  have hstable : (prefixWord ++ tailWord_5629379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629379).length < 2 ^ (prefixWord ++ tailWord_5629379).sum := by decide
  have hdescent : baseEnd_5629379 < baseStart_5629379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629409 : List Nat := [1, 2, 3, 1, 2, 3, 3, 8]
def baseStart_5629409 : Nat := 118140960795 + 5629409 * 2 ^ 59
def prefixEnd_5629409 : Nat := 4983230072969 + 3 ^ 40 * 5629409 * 2
def baseEnd_5629409 : Nat := 107058985842454468336975

theorem tailTrace_5629409 : CollatzResearch.WordTrace tailWord_5629409 prefixEnd_5629409 107058985842454468336975 := by
  unfold tailWord_5629409
  simp only [CollatzResearch.WordTrace]
  refine ⟨205321414062620094359235281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136880942708413396239490187 205321414062620094359235281)
  ·
    refine ⟨153991060546965070769426461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205321414062620094359235281 153991060546965070769426461)
    ·
      refine ⟨57746647705111901538534923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153991060546965070769426461 57746647705111901538534923)
      ·
        refine ⟨86619971557667852307802385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57746647705111901538534923 86619971557667852307802385)
        ·
          refine ⟨64964978668250889230851789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86619971557667852307802385 64964978668250889230851789)
          ·
            refine ⟨24361867000594083461569421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64964978668250889230851789 24361867000594083461569421)
            ·
              refine ⟨9135700125222781298088533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24361867000594083461569421 9135700125222781298088533)
              ·
                refine ⟨107058985842454468336975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9135700125222781298088533 107058985842454468336975)
                ·
                  rfl

theorem cell23_5629409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 8].length) (baseStart_5629409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629409 prefixEnd_5629409 := by exact prefixLift 5629409
  have htrace : WordTrace (prefixWord ++ tailWord_5629409) baseStart_5629409 baseEnd_5629409 := by
    simpa [prefixWord, tailWord_5629409, baseEnd_5629409] using wordTrace_append hprefix tailTrace_5629409
  have hstable : (prefixWord ++ tailWord_5629409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629409).length < 2 ^ (prefixWord ++ tailWord_5629409).sum := by decide
  have hdescent : baseEnd_5629409 < baseStart_5629409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629413 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 2, 4]
def baseStart_5629413 : Nat := 118140960795 + 5629413 * 2 ^ 59
def prefixEnd_5629413 : Nat := 4983230072969 + 3 ^ 40 * 5629413 * 2
def baseEnd_5629413 : Nat := 963531557222962876482769

theorem tailTrace_5629413 : CollatzResearch.WordTrace tailWord_5629413 prefixEnd_5629413 963531557222962876482769 := by
  unfold tailWord_5629413
  simp only [CollatzResearch.WordTrace]
  refine ⟨205321559954605603042380893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136881039969737068694920595 205321559954605603042380893)
  ·
    refine ⟨76995584982977101140892835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205321559954605603042380893 76995584982977101140892835)
    ·
      refine ⟨115493377474465651711339253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76995584982977101140892835 115493377474465651711339253)
      ·
        refine ⟨10827504138231154847938055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115493377474465651711339253 10827504138231154847938055)
        ·
          refine ⟨16241256207346732271907083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10827504138231154847938055 16241256207346732271907083)
          ·
            refine ⟨24361884311020098407860625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16241256207346732271907083 24361884311020098407860625)
            ·
              refine ⟨18271413233265073805895469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24361884311020098407860625 18271413233265073805895469)
              ·
                refine ⟨6851779962474402677210801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18271413233265073805895469 6851779962474402677210801)
                ·
                  refine ⟨5138834971855802007908101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851779962474402677210801 5138834971855802007908101)
                  ·
                    refine ⟨963531557222962876482769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5138834971855802007908101 963531557222962876482769)
                    ·
                      rfl

theorem cell23_5629413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 4].length) (baseStart_5629413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629413 prefixEnd_5629413 := by exact prefixLift 5629413
  have htrace : WordTrace (prefixWord ++ tailWord_5629413) baseStart_5629413 baseEnd_5629413 := by
    simpa [prefixWord, tailWord_5629413, baseEnd_5629413] using wordTrace_append hprefix tailTrace_5629413
  have hstable : (prefixWord ++ tailWord_5629413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629413).length < 2 ^ (prefixWord ++ tailWord_5629413).sum := by decide
  have hdescent : baseEnd_5629413 < baseStart_5629413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629416 : List Nat := [2, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_5629416 : Nat := 118140960795 + 5629416 * 2 ^ 59
def prefixEnd_5629416 : Nat := 4983230072969 + 3 ^ 40 * 5629416 * 2
def baseEnd_5629416 : Nat := 2890596212110852117710793

theorem tailTrace_5629416 : CollatzResearch.WordTrace tailWord_5629416 prefixEnd_5629416 2890596212110852117710793 := by
  unfold tailWord_5629416
  simp only [CollatzResearch.WordTrace]
  refine ⟨102660834686797367277370051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136881112915729823036493401 102660834686797367277370051)
  ·
    refine ⟨153991252030196050916055077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102660834686797367277370051 153991252030196050916055077)
    ·
      refine ⟨28873359755661759546760327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153991252030196050916055077 28873359755661759546760327)
      ·
        refine ⟨43310039633492639320140491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28873359755661759546760327 43310039633492639320140491)
        ·
          refine ⟨64965059450238958980210737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43310039633492639320140491 64965059450238958980210737)
          ·
            refine ⟨48723794587679219235158053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64965059450238958980210737 48723794587679219235158053)
            ·
              refine ⟨9135711485189853606592135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48723794587679219235158053 9135711485189853606592135)
              ·
                refine ⟨13703567227784780409888203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135711485189853606592135 13703567227784780409888203)
                ·
                  refine ⟨20555350841677170614832305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13703567227784780409888203 20555350841677170614832305)
                  ·
                    refine ⟨15416513131257877961124229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20555350841677170614832305 15416513131257877961124229)
                    ·
                      refine ⟨2890596212110852117710793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15416513131257877961124229 2890596212110852117710793)
                      ·
                        rfl

theorem cell23_5629416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_5629416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629416 prefixEnd_5629416 := by exact prefixLift 5629416
  have htrace : WordTrace (prefixWord ++ tailWord_5629416) baseStart_5629416 baseEnd_5629416 := by
    simpa [prefixWord, tailWord_5629416, baseEnd_5629416] using wordTrace_append hprefix tailTrace_5629416
  have hstable : (prefixWord ++ tailWord_5629416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629416).length < 2 ^ (prefixWord ++ tailWord_5629416).sum := by decide
  have hdescent : baseEnd_5629416 < baseStart_5629416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629436 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_5629436 : Nat := 118140960795 + 5629436 * 2 ^ 59
def prefixEnd_5629436 : Nat := 4983230072969 + 3 ^ 40 * 5629436 * 2
def baseEnd_5629436 : Nat := 2890606481723942039460701

theorem tailTrace_5629436 : CollatzResearch.WordTrace tailWord_5629436 prefixEnd_5629436 2890606481723942039460701 := by
  unfold tailWord_5629436
  simp only [CollatzResearch.WordTrace]
  refine ⟨102661199416761138985234081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136881599222348185313645441 102661199416761138985234081)
  ·
    refine ⟨76995899562570854238925561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102661199416761138985234081 76995899562570854238925561)
    ·
      refine ⟨57746924671928140679194171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76995899562570854238925561 57746924671928140679194171)
      ·
        refine ⟨86620387007892211018791257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57746924671928140679194171 86620387007892211018791257)
        ·
          refine ⟨64965290255919158264093443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86620387007892211018791257 64965290255919158264093443)
          ·
            refine ⟨97447935383878737396140165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64965290255919158264093443 97447935383878737396140165)
            ·
              refine ⟨18271487884477263261776281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97447935383878737396140165 18271487884477263261776281)
              ·
                refine ⟨13703615913357947446332211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18271487884477263261776281 13703615913357947446332211)
                ·
                  refine ⟨20555423870036921169498317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13703615913357947446332211 20555423870036921169498317)
                  ·
                    refine ⟨7708283951263845438561869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20555423870036921169498317 7708283951263845438561869)
                    ·
                      refine ⟨2890606481723942039460701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7708283951263845438561869 2890606481723942039460701)
                      ·
                        rfl

theorem cell23_5629436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_5629436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629436 prefixEnd_5629436 := by exact prefixLift 5629436
  have htrace : WordTrace (prefixWord ++ tailWord_5629436) baseStart_5629436 baseEnd_5629436 := by
    simpa [prefixWord, tailWord_5629436, baseEnd_5629436] using wordTrace_append hprefix tailTrace_5629436
  have hstable : (prefixWord ++ tailWord_5629436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629436).length < 2 ^ (prefixWord ++ tailWord_5629436).sum := by decide
  have hdescent : baseEnd_5629436 < baseStart_5629436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629437 : List Nat := [1, 4, 1, 1, 1, 5, 2, 3, 1, 2, 2]
def baseStart_5629437 : Nat := 118140960795 + 5629437 * 2 ^ 59
def prefixEnd_5629437 : Nat := 4983230072969 + 3 ^ 40 * 5629437 * 2
def baseEnd_5629437 : Nat := 2890606995204596535548197

theorem tailTrace_5629437 : CollatzResearch.WordTrace tailWord_5629437 prefixEnd_5629437 2890606995204596535548197 := by
  unfold tailWord_5629437
  simp only [CollatzResearch.WordTrace]
  refine ⟨205322435306518655141254565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136881623537679103427503043 205322435306518655141254565)
  ·
    refine ⟨38497956619972247838985231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205322435306518655141254565 38497956619972247838985231)
    ·
      refine ⟨57746934929958371758477847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38497956619972247838985231 57746934929958371758477847)
      ·
        refine ⟨86620402394937557637716771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57746934929958371758477847 86620402394937557637716771)
        ·
          refine ⟨129930603592406336456575157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86620402394937557637716771 129930603592406336456575157)
          ·
            refine ⟨12180994086788094042803921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129930603592406336456575157 12180994086788094042803921)
            ·
              refine ⟨9135745565091070532102941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12180994086788094042803921 9135745565091070532102941)
              ·
                refine ⟨3425904586909151449538603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9135745565091070532102941 3425904586909151449538603)
                ·
                  refine ⟨5138856880363727174307905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3425904586909151449538603 5138856880363727174307905)
                  ·
                    refine ⟨3854142660272795380730929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5138856880363727174307905 3854142660272795380730929)
                    ·
                      refine ⟨2890606995204596535548197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854142660272795380730929 2890606995204596535548197)
                      ·
                        rfl

theorem cell23_5629437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_5629437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629437 prefixEnd_5629437 := by exact prefixLift 5629437
  have htrace : WordTrace (prefixWord ++ tailWord_5629437) baseStart_5629437 baseEnd_5629437 := by
    simpa [prefixWord, tailWord_5629437, baseEnd_5629437] using wordTrace_append hprefix tailTrace_5629437
  have hstable : (prefixWord ++ tailWord_5629437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629437).length < 2 ^ (prefixWord ++ tailWord_5629437).sum := by decide
  have hdescent : baseEnd_5629437 < baseStart_5629437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629496 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_5629496 : Nat := 118140960795 + 5629496 * 2 ^ 59
def prefixEnd_5629496 : Nat := 4983230072969 + 3 ^ 40 * 5629496 * 2
def baseEnd_5629496 : Nat := 2890637290563211804710425

theorem tailTrace_5629496 : CollatzResearch.WordTrace tailWord_5629496 prefixEnd_5629496 2890637290563211804710425 := by
  unfold tailWord_5629496
  simp only [CollatzResearch.WordTrace]
  refine ⟨102662293606652454108826171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136883058142203272145101561 102662293606652454108826171)
  ·
    refine ⟨153993440409978681163239257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102662293606652454108826171 153993440409978681163239257)
    ·
      refine ⟨115495080307484010872429443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153993440409978681163239257 115495080307484010872429443)
      ·
        refine ⟨173242620461226016308644165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115495080307484010872429443 173242620461226016308644165)
        ·
          refine ⟨32482991336479878057870781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 173242620461226016308644165 32482991336479878057870781)
          ·
            refine ⟨12181121751179954271701543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32482991336479878057870781 12181121751179954271701543)
            ·
              refine ⟨18271682626769931407552315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12181121751179954271701543 18271682626769931407552315)
              ·
                refine ⟨27407523940154897111328473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18271682626769931407552315 27407523940154897111328473)
                ·
                  refine ⟨20555642955116172833496355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27407523940154897111328473 20555642955116172833496355)
                  ·
                    refine ⟨30833464432674259250244533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20555642955116172833496355 30833464432674259250244533)
                    ·
                      refine ⟨2890637290563211804710425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30833464432674259250244533 2890637290563211804710425)
                      ·
                        rfl

theorem cell23_5629496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_5629496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629496 prefixEnd_5629496 := by exact prefixLift 5629496
  have htrace : WordTrace (prefixWord ++ tailWord_5629496) baseStart_5629496 baseEnd_5629496 := by
    simpa [prefixWord, tailWord_5629496, baseEnd_5629496] using wordTrace_append hprefix tailTrace_5629496
  have hstable : (prefixWord ++ tailWord_5629496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629496).length < 2 ^ (prefixWord ++ tailWord_5629496).sum := by decide
  have hdescent : baseEnd_5629496 < baseStart_5629496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629509 : List Nat := [1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_5629509 : Nat := 118140960795 + 5629509 * 2 ^ 59
def prefixEnd_5629509 : Nat := 4983230072969 + 3 ^ 40 * 5629509 * 2
def baseEnd_5629509 : Nat := 2890643965811720253847865

theorem tailTrace_5629509 : CollatzResearch.WordTrace tailWord_5629509 prefixEnd_5629509 2890643965811720253847865 := by
  unfold tailWord_5629509
  simp only [CollatzResearch.WordTrace]
  refine ⟨205325061362257811437875581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136883374241505207625250387 205325061362257811437875581)
  ·
    refine ⟨76996898010846679289203343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205325061362257811437875581 76996898010846679289203343)
    ·
      refine ⟨115495347016270018933805015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76996898010846679289203343 115495347016270018933805015)
      ·
        refine ⟨173243020524405028400707523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115495347016270018933805015 173243020524405028400707523)
        ·
          refine ⟨259864530786607542601061285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173243020524405028400707523 259864530786607542601061285)
          ·
            refine ⟨48724599522488914237698991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259864530786607542601061285 48724599522488914237698991)
            ·
              refine ⟨73086899283733371356548487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48724599522488914237698991 73086899283733371356548487)
              ·
                refine ⟨109630348925600057034822731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73086899283733371356548487 109630348925600057034822731)
                ·
                  refine ⟨164445523388400085552234097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109630348925600057034822731 164445523388400085552234097)
                  ·
                    refine ⟨123334142541300064164175573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164445523388400085552234097 123334142541300064164175573)
                    ·
                      refine ⟨2890643965811720253847865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123334142541300064164175573 2890643965811720253847865)
                      ·
                        rfl

theorem cell23_5629509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_5629509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629509 prefixEnd_5629509 := by exact prefixLift 5629509
  have htrace : WordTrace (prefixWord ++ tailWord_5629509) baseStart_5629509 baseEnd_5629509 := by
    simpa [prefixWord, tailWord_5629509, baseEnd_5629509] using wordTrace_append hprefix tailTrace_5629509
  have hstable : (prefixWord ++ tailWord_5629509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629509).length < 2 ^ (prefixWord ++ tailWord_5629509).sum := by decide
  have hdescent : baseEnd_5629509 < baseStart_5629509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629516 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 7]
def baseStart_5629516 : Nat := 118140960795 + 5629516 * 2 ^ 59
def prefixEnd_5629516 : Nat := 4983230072969 + 3 ^ 40 * 5629516 * 2
def baseEnd_5629516 : Nat := 321183062241811302940037

theorem tailTrace_5629516 : CollatzResearch.WordTrace tailWord_5629516 prefixEnd_5629516 321183062241811302940037 := by
  unfold tailWord_5629516
  simp only [CollatzResearch.WordTrace]
  refine ⟨102662658336616225816690201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136883544448821634422253601 102662658336616225816690201)
  ·
    refine ⟨76996993752462169362517651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102662658336616225816690201 76996993752462169362517651)
    ·
      refine ⟨115495490628693254043776477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76996993752462169362517651 115495490628693254043776477)
      ·
        refine ⟨43310808985759970266416179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115495490628693254043776477 43310808985759970266416179)
        ·
          refine ⟨64966213478639955399624269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43310808985759970266416179 64966213478639955399624269)
          ·
            refine ⟨24362330054489983274859101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64966213478639955399624269 24362330054489983274859101)
            ·
              refine ⟨9135873770433743728072163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24362330054489983274859101 9135873770433743728072163)
              ·
                refine ⟨13703810655650615592108245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9135873770433743728072163 13703810655650615592108245)
                ·
                  refine ⟨321183062241811302940037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13703810655650615592108245 321183062241811302940037)
                  ·
                    rfl

theorem cell23_5629516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_5629516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629516 prefixEnd_5629516 := by exact prefixLift 5629516
  have htrace : WordTrace (prefixWord ++ tailWord_5629516) baseStart_5629516 baseEnd_5629516 := by
    simpa [prefixWord, tailWord_5629516, baseEnd_5629516] using wordTrace_append hprefix tailTrace_5629516
  have hstable : (prefixWord ++ tailWord_5629516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629516).length < 2 ^ (prefixWord ++ tailWord_5629516).sum := by decide
  have hdescent : baseEnd_5629516 < baseStart_5629516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629527 : List Nat := [1, 1, 3, 2, 2, 3, 4, 1, 2, 2, 2]
def baseStart_5629527 : Nat := 118140960795 + 5629527 * 2 ^ 59
def prefixEnd_5629527 : Nat := 4983230072969 + 3 ^ 40 * 5629527 * 2
def baseEnd_5629527 : Nat := 2890653208463501183422783

theorem tailTrace_5629527 : CollatzResearch.WordTrace tailWord_5629527 prefixEnd_5629527 2890653208463501183422783 := by
  unfold tailWord_5629527
  simp only [CollatzResearch.WordTrace]
  refine ⟨205325717876192600512030835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136883811917461733674687223 205325717876192600512030835)
  ·
    refine ⟨307988576814288900768046253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205325717876192600512030835 307988576814288900768046253)
    ·
      refine ⟨115495716305358337788017345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307988576814288900768046253 115495716305358337788017345)
      ·
        refine ⟨86621787229018753341013009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115495716305358337788017345 86621787229018753341013009)
        ·
          refine ⟨64966340421764065005759757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86621787229018753341013009 64966340421764065005759757)
          ·
            refine ⟨24362377658161524377159909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64966340421764065005759757 24362377658161524377159909)
            ·
              refine ⟨4567945810905285820717483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24362377658161524377159909 4567945810905285820717483)
              ·
                refine ⟨6851918716357928731076225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4567945810905285820717483 6851918716357928731076225)
                ·
                  refine ⟨5138939037268446548307169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6851918716357928731076225 5138939037268446548307169)
                  ·
                    refine ⟨3854204277951334911230377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5138939037268446548307169 3854204277951334911230377)
                    ·
                      refine ⟨2890653208463501183422783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854204277951334911230377 2890653208463501183422783)
                      ·
                        rfl

theorem cell23_5629527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_5629527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629527 prefixEnd_5629527 := by exact prefixLift 5629527
  have htrace : WordTrace (prefixWord ++ tailWord_5629527) baseStart_5629527 baseEnd_5629527 := by
    simpa [prefixWord, tailWord_5629527, baseEnd_5629527] using wordTrace_append hprefix tailTrace_5629527
  have hstable : (prefixWord ++ tailWord_5629527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629527).length < 2 ^ (prefixWord ++ tailWord_5629527).sum := by decide
  have hdescent : baseEnd_5629527 < baseStart_5629527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629529 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 7]
def baseStart_5629529 : Nat := 118140960795 + 5629529 * 2 ^ 59
def prefixEnd_5629529 : Nat := 4983230072969 + 3 ^ 40 * 5629529 * 2
def baseEnd_5629529 : Nat := 963551411808270058532591

theorem tailTrace_5629529 : CollatzResearch.WordTrace tailWord_5629529 prefixEnd_5629529 963551411808270058532591 := by
  unfold tailWord_5629529
  simp only [CollatzResearch.WordTrace]
  refine ⟨205325790822185354853603641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136883860548123569902402427 205325790822185354853603641)
  ·
    refine ⟨153994343116639016140202731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205325790822185354853603641 153994343116639016140202731)
    ·
      refine ⟨230991514674958524210304097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153994343116639016140202731 230991514674958524210304097)
      ·
        refine ⟨173243636006218893157728073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230991514674958524210304097 173243636006218893157728073)
        ·
          refine ⟨129932727004664169868296055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173243636006218893157728073 129932727004664169868296055)
          ·
            refine ⟨194899090506996254802444083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129932727004664169868296055 194899090506996254802444083)
            ·
              refine ⟨292348635760494382203666125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194899090506996254802444083 292348635760494382203666125)
              ·
                refine ⟨109630738410185393326374797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 292348635760494382203666125 109630738410185393326374797)
                ·
                  refine ⟨41111526903819522497390549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109630738410185393326374797 41111526903819522497390549)
                  ·
                    refine ⟨963551411808270058532591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41111526903819522497390549 963551411808270058532591)
                    ·
                      rfl

theorem cell23_5629529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 7].length) (baseStart_5629529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629529 prefixEnd_5629529 := by exact prefixLift 5629529
  have htrace : WordTrace (prefixWord ++ tailWord_5629529) baseStart_5629529 baseEnd_5629529 := by
    simpa [prefixWord, tailWord_5629529, baseEnd_5629529] using wordTrace_append hprefix tailTrace_5629529
  have hstable : (prefixWord ++ tailWord_5629529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629529).length < 2 ^ (prefixWord ++ tailWord_5629529).sum := by decide
  have hdescent : baseEnd_5629529 < baseStart_5629529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629600 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_5629600 : Nat := 118140960795 + 5629600 * 2 ^ 59
def prefixEnd_5629600 : Nat := 4983230072969 + 3 ^ 40 * 5629600 * 2
def baseEnd_5629600 : Nat := 2890690692551279397809947

theorem tailTrace_5629600 : CollatzResearch.WordTrace tailWord_5629600 prefixEnd_5629600 2890690692551279397809947 := by
  unfold tailWord_5629600
  simp only [CollatzResearch.WordTrace]
  refine ⟨102664190202464066989719127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136885586936618755986292169 102664190202464066989719127)
  ·
    refine ⟨153996285303696100484578691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102664190202464066989719127 153996285303696100484578691)
    ·
      refine ⟨230994427955544150726868037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153996285303696100484578691 230994427955544150726868037)
      ·
        refine ⟨43311455241664528261287757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230994427955544150726868037 43311455241664528261287757)
        ·
          refine ⟨16241795715624198097982909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43311455241664528261287757 16241795715624198097982909)
          ·
            refine ⟨6090673393359074286743591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16241795715624198097982909 6090673393359074286743591)
            ·
              refine ⟨9136010090038611430115387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090673393359074286743591 9136010090038611430115387)
              ·
                refine ⟨13704015135057917145173081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136010090038611430115387 13704015135057917145173081)
                ·
                  refine ⟨10278011351293437858879811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13704015135057917145173081 10278011351293437858879811)
                  ·
                    refine ⟨15417017026940156788319717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10278011351293437858879811 15417017026940156788319717)
                    ·
                      refine ⟨2890690692551279397809947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15417017026940156788319717 2890690692551279397809947)
                      ·
                        rfl

theorem cell23_5629600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_5629600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629600 prefixEnd_5629600 := by exact prefixLift 5629600
  have htrace : WordTrace (prefixWord ++ tailWord_5629600) baseStart_5629600 baseEnd_5629600 := by
    simpa [prefixWord, tailWord_5629600, baseEnd_5629600] using wordTrace_append hprefix tailTrace_5629600
  have hstable : (prefixWord ++ tailWord_5629600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629600).length < 2 ^ (prefixWord ++ tailWord_5629600).sum := by decide
  have hdescent : baseEnd_5629600 < baseStart_5629600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629623 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 6]
def baseStart_5629623 : Nat := 118140960795 + 5629623 * 2 ^ 59
def prefixEnd_5629623 : Nat := 4983230072969 + 3 ^ 40 * 5629623 * 2
def baseEnd_5629623 : Nat := 321189166956259200869149

theorem tailTrace_5629623 : CollatzResearch.WordTrace tailWord_5629623 prefixEnd_5629623 321189166956259200869149 := by
  unfold tailWord_5629623
  simp only [CollatzResearch.WordTrace]
  refine ⟨205329219283844808907525523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136886146189229872605017015 205329219283844808907525523)
  ·
    refine ⟨307993828925767213361288285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205329219283844808907525523 307993828925767213361288285)
    ·
      refine ⟨115497685847162705010483107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307993828925767213361288285 115497685847162705010483107)
      ·
        refine ⟨173246528770744057515724661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115497685847162705010483107 173246528770744057515724661)
        ·
          refine ⟨16241862072257255392099187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 173246528770744057515724661 16241862072257255392099187)
          ·
            refine ⟨24362793108385883088148781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16241862072257255392099187 24362793108385883088148781)
            ·
              refine ⟨9136047415644706158055793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24362793108385883088148781 9136047415644706158055793)
              ·
                refine ⟨6852035561733529618541845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9136047415644706158055793 6852035561733529618541845)
                ·
                  refine ⟨321189166956259200869149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6852035561733529618541845 321189166956259200869149)
                  ·
                    rfl

theorem cell23_5629623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 6].length) (baseStart_5629623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629623 prefixEnd_5629623 := by exact prefixLift 5629623
  have htrace : WordTrace (prefixWord ++ tailWord_5629623) baseStart_5629623 baseEnd_5629623 := by
    simpa [prefixWord, tailWord_5629623, baseEnd_5629623] using wordTrace_append hprefix tailTrace_5629623
  have hstable : (prefixWord ++ tailWord_5629623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629623).length < 2 ^ (prefixWord ++ tailWord_5629623).sum := by decide
  have hdescent : baseEnd_5629623 < baseStart_5629623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629626 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_5629626 : Nat := 118140960795 + 5629626 * 2 ^ 59
def prefixEnd_5629626 : Nat := 4983230072969 + 3 ^ 40 * 5629626 * 2
def baseEnd_5629626 : Nat := 2890704043048296296084827

theorem tailTrace_5629626 : CollatzResearch.WordTrace tailWord_5629626 prefixEnd_5629626 2890704043048296296084827 := by
  unfold tailWord_5629626
  simp only [CollatzResearch.WordTrace]
  refine ⟨51332332175708485104971183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136886219135222626946589821 51332332175708485104971183)
  ·
    refine ⟨76998498263562727657456775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51332332175708485104971183 76998498263562727657456775)
    ·
      refine ⟨115497747395344091486185163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76998498263562727657456775 115497747395344091486185163)
      ·
        refine ⟨173246621093016137229277745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115497747395344091486185163 173246621093016137229277745)
        ·
          refine ⟨129934965819762102921958309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173246621093016137229277745 129934965819762102921958309)
          ·
            refine ⟨24362806091205394297867183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129934965819762102921958309 24362806091205394297867183)
            ·
              refine ⟨36544209136808091446800775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24362806091205394297867183 36544209136808091446800775)
              ·
                refine ⟨54816313705212137170201163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36544209136808091446800775 54816313705212137170201163)
                ·
                  refine ⟨82224470557818205755301745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54816313705212137170201163 82224470557818205755301745)
                  ·
                    refine ⟨61668352918363654316476309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82224470557818205755301745 61668352918363654316476309)
                    ·
                      refine ⟨2890704043048296296084827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61668352918363654316476309 2890704043048296296084827)
                      ·
                        rfl

theorem cell23_5629626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_5629626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629626 prefixEnd_5629626 := by exact prefixLift 5629626
  have htrace : WordTrace (prefixWord ++ tailWord_5629626) baseStart_5629626 baseEnd_5629626 := by
    simpa [prefixWord, tailWord_5629626, baseEnd_5629626] using wordTrace_append hprefix tailTrace_5629626
  have hstable : (prefixWord ++ tailWord_5629626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629626).length < 2 ^ (prefixWord ++ tailWord_5629626).sum := by decide
  have hdescent : baseEnd_5629626 < baseStart_5629626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629661 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 1, 4]
def baseStart_5629661 : Nat := 118140960795 + 5629661 * 2 ^ 59
def prefixEnd_5629661 : Nat := 4983230072969 + 3 ^ 40 * 5629661 * 2
def baseEnd_5629661 : Nat := 963574004957067886382389

theorem tailTrace_5629661 : CollatzResearch.WordTrace tailWord_5629661 prefixEnd_5629661 963574004957067886382389 := by
  unfold tailWord_5629661
  simp only [CollatzResearch.WordTrace]
  refine ⟨205330605257707141397408837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136887070171804760931605891 205330605257707141397408837)
  ·
    refine ⟨38499488485820089012014157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205330605257707141397408837 38499488485820089012014157)
    ·
      refine ⟨14437308182182533379505309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38499488485820089012014157 14437308182182533379505309)
      ·
        refine ⟨5413990568318450017314491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14437308182182533379505309 5413990568318450017314491)
        ·
          refine ⟨8120985852477675025971737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5413990568318450017314491 8120985852477675025971737)
          ·
            refine ⟨6090739389358256269478803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8120985852477675025971737 6090739389358256269478803)
            ·
              refine ⟨9136109084037384404218205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6090739389358256269478803 9136109084037384404218205)
              ·
                refine ⟨3426040906514019151581827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9136109084037384404218205 3426040906514019151581827)
                ·
                  refine ⟨5139061359771028727372741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426040906514019151581827 5139061359771028727372741)
                  ·
                    refine ⟨963574004957067886382389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139061359771028727372741 963574004957067886382389)
                    ·
                      rfl

theorem cell23_5629661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_5629661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629661 prefixEnd_5629661 := by exact prefixLift 5629661
  have htrace : WordTrace (prefixWord ++ tailWord_5629661) baseStart_5629661 baseEnd_5629661 := by
    simpa [prefixWord, tailWord_5629661, baseEnd_5629661] using wordTrace_append hprefix tailTrace_5629661
  have hstable : (prefixWord ++ tailWord_5629661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629661).length < 2 ^ (prefixWord ++ tailWord_5629661).sum := by decide
  have hdescent : baseEnd_5629661 < baseStart_5629661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629677 : List Nat := [1, 5, 1, 2, 1, 3, 1, 2, 2, 3, 2]
def baseStart_5629677 : Nat := 118140960795 + 5629677 * 2 ^ 59
def prefixEnd_5629677 : Nat := 4983230072969 + 3 ^ 40 * 5629677 * 2
def baseEnd_5629677 : Nat := 2890730230561675596547093

theorem tailTrace_5629677 : CollatzResearch.WordTrace tailWord_5629677 prefixEnd_5629677 2890730230561675596547093 := by
  unfold tailWord_5629677
  simp only [CollatzResearch.WordTrace]
  refine ⟨205331188825649176129991285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136887459217099450753327523 205331188825649176129991285)
  ·
    refine ⟨19249798952404610262186683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 205331188825649176129991285 19249798952404610262186683)
    ·
      refine ⟨28874698428606915393280025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19249798952404610262186683 28874698428606915393280025)
      ·
        refine ⟨21656023821455186544960019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28874698428606915393280025 21656023821455186544960019)
        ·
          refine ⟨32484035732182779817440029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21656023821455186544960019 32484035732182779817440029)
          ·
            refine ⟨12181513399568542431540011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32484035732182779817440029 12181513399568542431540011)
            ·
              refine ⟨18272270099352813647310017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12181513399568542431540011 18272270099352813647310017)
              ·
                refine ⟨13704202574514610235482513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18272270099352813647310017 13704202574514610235482513)
                ·
                  refine ⟨10278151930885957676611885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13704202574514610235482513 10278151930885957676611885)
                  ·
                    refine ⟨3854306974082234128729457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10278151930885957676611885 3854306974082234128729457)
                    ·
                      refine ⟨2890730230561675596547093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854306974082234128729457 2890730230561675596547093)
                      ·
                        rfl

theorem cell23_5629677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_5629677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629677 prefixEnd_5629677 := by exact prefixLift 5629677
  have htrace : WordTrace (prefixWord ++ tailWord_5629677) baseStart_5629677 baseEnd_5629677 := by
    simpa [prefixWord, tailWord_5629677, baseEnd_5629677] using wordTrace_append hprefix tailTrace_5629677
  have hstable : (prefixWord ++ tailWord_5629677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629677).length < 2 ^ (prefixWord ++ tailWord_5629677).sum := by decide
  have hdescent : baseEnd_5629677 < baseStart_5629677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629683 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 4, 4]
def baseStart_5629683 : Nat := 118140960795 + 5629683 * 2 ^ 59
def prefixEnd_5629683 : Nat := 4983230072969 + 3 ^ 40 * 5629683 * 2
def baseEnd_5629683 : Nat := 963577770481867524357355

theorem tailTrace_5629683 : CollatzResearch.WordTrace tailWord_5629683 prefixEnd_5629683 963577770481867524357355 := by
  unfold tailWord_5629683
  simp only [CollatzResearch.WordTrace]
  refine ⟨205331407663627439154709703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136887605109084959436473135 205331407663627439154709703)
  ·
    refine ⟨307997111495441158732064555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205331407663627439154709703 307997111495441158732064555)
    ·
      refine ⟨461995667243161738098096833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307997111495441158732064555 461995667243161738098096833)
      ·
        refine ⟨346496750432371303573572625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461995667243161738098096833 346496750432371303573572625)
        ·
          refine ⟨259872562824278477680179469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346496750432371303573572625 259872562824278477680179469)
          ·
            refine ⟨97452211059104429130067301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259872562824278477680179469 97452211059104429130067301)
            ·
              refine ⟨18272289573582080461887619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97452211059104429130067301 18272289573582080461887619)
              ·
                refine ⟨27408434360373120692831429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18272289573582080461887619 27408434360373120692831429)
                ·
                  refine ⟨5139081442569960129905893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27408434360373120692831429 5139081442569960129905893)
                  ·
                    refine ⟨963577770481867524357355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139081442569960129905893 963577770481867524357355)
                    ·
                      rfl

theorem cell23_5629683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 4].length) (baseStart_5629683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629683 prefixEnd_5629683 := by exact prefixLift 5629683
  have htrace : WordTrace (prefixWord ++ tailWord_5629683) baseStart_5629683 baseEnd_5629683 := by
    simpa [prefixWord, tailWord_5629683, baseEnd_5629683] using wordTrace_append hprefix tailTrace_5629683
  have hstable : (prefixWord ++ tailWord_5629683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629683).length < 2 ^ (prefixWord ++ tailWord_5629683).sum := by decide
  have hdescent : baseEnd_5629683 < baseStart_5629683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629723 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3]
def baseStart_5629723 : Nat := 118140960795 + 5629723 * 2 ^ 59
def prefixEnd_5629723 : Nat := 4983230072969 + 3 ^ 40 * 5629723 * 2
def baseEnd_5629723 : Nat := 2890753850671782416571881

theorem tailTrace_5629723 : CollatzResearch.WordTrace tailWord_5629723 prefixEnd_5629723 2890753850671782416571881 := by
  unfold tailWord_5629723
  simp only [CollatzResearch.WordTrace]
  refine ⟨205332866583482525986165823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136888577722321683990777215 205332866583482525986165823)
  ·
    refine ⟨307999299875223788979248735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205332866583482525986165823 307999299875223788979248735)
    ·
      refine ⟨461998949812835683468873103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307999299875223788979248735 461998949812835683468873103)
      ·
        refine ⟨692998424719253525203309655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461998949812835683468873103 692998424719253525203309655)
        ·
          refine ⟨1039497637078880287804964483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692998424719253525203309655 1039497637078880287804964483)
          ·
            refine ⟨1559246455618320431707446725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039497637078880287804964483 1559246455618320431707446725)
            ·
              refine ⟨292358710428435080945146261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1559246455618320431707446725 292358710428435080945146261)
              ·
                refine ⟨13704314551332894419303731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292358710428435080945146261 13704314551332894419303731)
                ·
                  refine ⟨20556471826999341628955597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13704314551332894419303731 20556471826999341628955597)
                  ·
                    refine ⟨7708676935124753110858349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20556471826999341628955597 7708676935124753110858349)
                    ·
                      refine ⟨2890753850671782416571881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7708676935124753110858349 2890753850671782416571881)
                      ·
                        rfl

theorem cell23_5629723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 3, 3].length) (baseStart_5629723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629723 prefixEnd_5629723 := by exact prefixLift 5629723
  have htrace : WordTrace (prefixWord ++ tailWord_5629723) baseStart_5629723 baseEnd_5629723 := by
    simpa [prefixWord, tailWord_5629723, baseEnd_5629723] using wordTrace_append hprefix tailTrace_5629723
  have hstable : (prefixWord ++ tailWord_5629723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629723).length < 2 ^ (prefixWord ++ tailWord_5629723).sum := by decide
  have hdescent : baseEnd_5629723 < baseStart_5629723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629724 : List Nat := [2, 2, 3, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5629724 : Nat := 118140960795 + 5629724 * 2 ^ 59
def prefixEnd_5629724 : Nat := 4983230072969 + 3 ^ 40 * 5629724 * 2
def baseEnd_5629724 : Nat := 2890754364152436912659377

theorem tailTrace_5629724 : CollatzResearch.WordTrace tailWord_5629724 prefixEnd_5629724 2890754364152436912659377 := by
  unfold tailWord_5629724
  simp only [CollatzResearch.WordTrace]
  refine ⟨102666451528239451578476113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136888602037652602104634817 102666451528239451578476113)
  ·
    refine ⟨76999838646179588683857085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102666451528239451578476113 76999838646179588683857085)
    ·
      refine ⟨28874939492317345756446407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76999838646179588683857085 28874939492317345756446407)
      ·
        refine ⟨43312409238476018634669611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28874939492317345756446407 43312409238476018634669611)
        ·
          refine ⟨64968613857714027952004417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43312409238476018634669611 64968613857714027952004417)
          ·
            refine ⟨48726460393285520964003313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64968613857714027952004417 48726460393285520964003313)
            ·
              refine ⟨36544845294964140723002485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48726460393285520964003313 36544845294964140723002485)
              ·
                refine ⟨3426079246402888192781483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36544845294964140723002485 3426079246402888192781483)
                ·
                  refine ⟨5139118869604332289172225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3426079246402888192781483 5139118869604332289172225)
                  ·
                    refine ⟨3854339152203249216879169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5139118869604332289172225 3854339152203249216879169)
                    ·
                      refine ⟨2890754364152436912659377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854339152203249216879169 2890754364152436912659377)
                      ·
                        rfl

theorem cell23_5629724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5629724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629724 prefixEnd_5629724 := by exact prefixLift 5629724
  have htrace : WordTrace (prefixWord ++ tailWord_5629724) baseStart_5629724 baseEnd_5629724 := by
    simpa [prefixWord, tailWord_5629724, baseEnd_5629724] using wordTrace_append hprefix tailTrace_5629724
  have hstable : (prefixWord ++ tailWord_5629724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629724).length < 2 ^ (prefixWord ++ tailWord_5629724).sum := by decide
  have hdescent : baseEnd_5629724 < baseStart_5629724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629727 : List Nat := [1, 1, 2, 4, 2, 1, 5, 1, 1, 2, 3]
def baseStart_5629727 : Nat := 118140960795 + 5629727 * 2 ^ 59
def prefixEnd_5629727 : Nat := 4983230072969 + 3 ^ 40 * 5629727 * 2
def baseEnd_5629727 : Nat := 2890755904594400400921863

theorem tailTrace_5629727 : CollatzResearch.WordTrace tailWord_5629727 prefixEnd_5629727 2890755904594400400921863 := by
  unfold tailWord_5629727
  simp only [CollatzResearch.WordTrace]
  refine ⟨205333012475468034669311435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136888674983645356446207623 205333012475468034669311435)
  ·
    refine ⟨307999518713202052003967153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205333012475468034669311435 307999518713202052003967153)
    ·
      refine ⟨230999639034901539002975365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307999518713202052003967153 230999639034901539002975365)
      ·
        refine ⟨43312432319044038563057881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230999639034901539002975365 43312432319044038563057881)
        ·
          refine ⟨32484324239283028922293411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43312432319044038563057881 32484324239283028922293411)
          ·
            refine ⟨48726486358924543383440117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32484324239283028922293411 48726486358924543383440117)
            ·
              refine ⟨4568108096149175942197511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48726486358924543383440117 4568108096149175942197511)
              ·
                refine ⟨6852162144223763913296267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4568108096149175942197511 6852162144223763913296267)
                ·
                  refine ⟨10278243216335645869944401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852162144223763913296267 10278243216335645869944401)
                  ·
                    refine ⟨7708682412251734402458301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10278243216335645869944401 7708682412251734402458301)
                    ·
                      refine ⟨2890755904594400400921863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7708682412251734402458301 2890755904594400400921863)
                      ·
                        rfl

theorem cell23_5629727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_5629727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629727 prefixEnd_5629727 := by exact prefixLift 5629727
  have htrace : WordTrace (prefixWord ++ tailWord_5629727) baseStart_5629727 baseEnd_5629727 := by
    simpa [prefixWord, tailWord_5629727, baseEnd_5629727] using wordTrace_append hprefix tailTrace_5629727
  have hstable : (prefixWord ++ tailWord_5629727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629727).length < 2 ^ (prefixWord ++ tailWord_5629727).sum := by decide
  have hdescent : baseEnd_5629727 < baseStart_5629727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629757 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5629757 : Nat := 118140960795 + 5629757 * 2 ^ 59
def prefixEnd_5629757 : Nat := 4983230072969 + 3 ^ 40 * 5629757 * 2
def baseEnd_5629757 : Nat := 2890771309014035283546725

theorem tailTrace_5629757 : CollatzResearch.WordTrace tailWord_5629757 prefixEnd_5629757 2890771309014035283546725 := by
  unfold tailWord_5629757
  simp only [CollatzResearch.WordTrace]
  refine ⟨205334106665359349792903525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136889404443572899861935683 205334106665359349792903525)
  ·
    refine ⟨38500144999754878086169411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 205334106665359349792903525 38500144999754878086169411)
    ·
      refine ⟨57750217499632317129254117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38500144999754878086169411 57750217499632317129254117)
      ·
        refine ⟨10828165781181059461735147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57750217499632317129254117 10828165781181059461735147)
        ·
          refine ⟨16242248671771589192602721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10828165781181059461735147 16242248671771589192602721)
          ·
            refine ⟨12181686503828691894452041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16242248671771589192602721 12181686503828691894452041)
            ·
              refine ⟨9136264877871518920839031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12181686503828691894452041 9136264877871518920839031)
              ·
                refine ⟨13704397316807278381258547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136264877871518920839031 13704397316807278381258547)
                ·
                  refine ⟨20556595975210917571887821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13704397316807278381258547 20556595975210917571887821)
                  ·
                    refine ⟨7708723490704094089457933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20556595975210917571887821 7708723490704094089457933)
                    ·
                      refine ⟨2890771309014035283546725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7708723490704094089457933 2890771309014035283546725)
                      ·
                        rfl

theorem cell23_5629757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5629757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629757 prefixEnd_5629757 := by exact prefixLift 5629757
  have htrace : WordTrace (prefixWord ++ tailWord_5629757) baseStart_5629757 baseEnd_5629757 := by
    simpa [prefixWord, tailWord_5629757, baseEnd_5629757] using wordTrace_append hprefix tailTrace_5629757
  have hstable : (prefixWord ++ tailWord_5629757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629757).length < 2 ^ (prefixWord ++ tailWord_5629757).sum := by decide
  have hdescent : baseEnd_5629757 < baseStart_5629757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629793 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5629793 : Nat := 118140960795 + 5629793 * 2 ^ 59
def prefixEnd_5629793 : Nat := 4983230072969 + 3 ^ 40 * 5629793 * 2
def baseEnd_5629793 : Nat := 2890789794317597142696559

theorem tailTrace_5629793 : CollatzResearch.WordTrace tailWord_5629793 prefixEnd_5629793 2890789794317597142696559 := by
  unfold tailWord_5629793
  simp only [CollatzResearch.WordTrace]
  refine ⟨205335419693228927941214033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136890279795485951960809355 205335419693228927941214033)
  ·
    refine ⟨154001564769921695955910525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205335419693228927941214033 154001564769921695955910525)
    ·
      refine ⟨57750586788720635983466447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 154001564769921695955910525 57750586788720635983466447)
      ·
        refine ⟨86625880183080953975199671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57750586788720635983466447 86625880183080953975199671)
        ·
          refine ⟨129938820274621430962799507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86625880183080953975199671 129938820274621430962799507)
          ·
            refine ⟨194908230411932146444199261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129938820274621430962799507 194908230411932146444199261)
            ·
              refine ⟨73090586404474554916574723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194908230411932146444199261 73090586404474554916574723)
              ·
                refine ⟨109635879606711832374862085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73090586404474554916574723 109635879606711832374862085)
                ·
                  refine ⟨20556727426258468570286641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109635879606711832374862085 20556727426258468570286641)
                  ·
                    refine ⟨15417545569693851427714981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20556727426258468570286641 15417545569693851427714981)
                    ·
                      refine ⟨2890789794317597142696559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15417545569693851427714981 2890789794317597142696559)
                      ·
                        rfl

theorem cell23_5629793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5629793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629793 prefixEnd_5629793 := by exact prefixLift 5629793
  have htrace : WordTrace (prefixWord ++ tailWord_5629793) baseStart_5629793 baseEnd_5629793 := by
    simpa [prefixWord, tailWord_5629793, baseEnd_5629793] using wordTrace_append hprefix tailTrace_5629793
  have hstable : (prefixWord ++ tailWord_5629793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629793).length < 2 ^ (prefixWord ++ tailWord_5629793).sum := by decide
  have hdescent : baseEnd_5629793 < baseStart_5629793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629833 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 7]
def baseStart_5629833 : Nat := 118140960795 + 5629833 * 2 ^ 59
def prefixEnd_5629833 : Nat := 4983230072969 + 3 ^ 40 * 5629833 * 2
def baseEnd_5629833 : Nat := 963603444514592328732125

theorem tailTrace_5629833 : CollatzResearch.WordTrace tailWord_5629833 prefixEnd_5629833 963603444514592328732125 := by
  unfold tailWord_5629833
  simp only [CollatzResearch.WordTrace]
  refine ⟨205336878613084014772670153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136891252408722676515113435 205336878613084014772670153)
  ·
    refine ⟨154002658959813011079502615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205336878613084014772670153 154002658959813011079502615)
    ·
      refine ⟨231003988439719516619253923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154002658959813011079502615 231003988439719516619253923)
      ·
        refine ⟨346505982659579274928880885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231003988439719516619253923 346505982659579274928880885)
        ·
          refine ⟨32484935874335557024582583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 346505982659579274928880885 32484935874335557024582583)
          ·
            refine ⟨48727403811503335536873875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32484935874335557024582583 48727403811503335536873875)
            ·
              refine ⟨73091105717255003305310813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48727403811503335536873875 73091105717255003305310813)
              ·
                refine ⟨27409164643970626239491555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73091105717255003305310813 27409164643970626239491555)
                ·
                  refine ⟨41113746965955939359237333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27409164643970626239491555 41113746965955939359237333)
                  ·
                    refine ⟨963603444514592328732125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41113746965955939359237333 963603444514592328732125)
                    ·
                      rfl

theorem cell23_5629833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 7].length) (baseStart_5629833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629833 prefixEnd_5629833 := by exact prefixLift 5629833
  have htrace : WordTrace (prefixWord ++ tailWord_5629833) baseStart_5629833 baseEnd_5629833 := by
    simpa [prefixWord, tailWord_5629833, baseEnd_5629833] using wordTrace_append hprefix tailTrace_5629833
  have hstable : (prefixWord ++ tailWord_5629833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629833).length < 2 ^ (prefixWord ++ tailWord_5629833).sum := by decide
  have hdescent : baseEnd_5629833 < baseStart_5629833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629850 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_5629850 : Nat := 118140960795 + 5629850 * 2 ^ 59
def prefixEnd_5629850 : Nat := 4983230072969 + 3 ^ 40 * 5629850 * 2
def baseEnd_5629850 : Nat := 963606354238301139894599

theorem tailTrace_5629850 : CollatzResearch.WordTrace tailWord_5629850 prefixEnd_5629850 963606354238301139894599 := by
  unfold tailWord_5629850
  simp only [CollatzResearch.WordTrace]
  refine ⟨51334374663505606669009751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136891665769348284450692669 51334374663505606669009751)
  ·
    refine ⟨77001561995258410003514627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51334374663505606669009751 77001561995258410003514627)
    ·
      refine ⟨115502342992887615005271941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77001561995258410003514627 115502342992887615005271941)
      ·
        refine ⟨21656689311166427813488489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 115502342992887615005271941 21656689311166427813488489)
        ·
          refine ⟨16242516983374820860116367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21656689311166427813488489 16242516983374820860116367)
          ·
            refine ⟨24363775475062231290174551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16242516983374820860116367 24363775475062231290174551)
            ·
              refine ⟨36545663212593346935261827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24363775475062231290174551 36545663212593346935261827)
              ·
                refine ⟨54818494818890020402892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36545663212593346935261827 54818494818890020402892741)
                ·
                  refine ⟨10278467778541878825542389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54818494818890020402892741 10278467778541878825542389)
                  ·
                    refine ⟨963606354238301139894599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278467778541878825542389 963606354238301139894599)
                    ·
                      rfl

theorem cell23_5629850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_5629850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629850 prefixEnd_5629850 := by exact prefixLift 5629850
  have htrace : WordTrace (prefixWord ++ tailWord_5629850) baseStart_5629850 baseEnd_5629850 := by
    simpa [prefixWord, tailWord_5629850, baseEnd_5629850] using wordTrace_append hprefix tailTrace_5629850
  have hstable : (prefixWord ++ tailWord_5629850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629850).length < 2 ^ (prefixWord ++ tailWord_5629850).sum := by decide
  have hdescent : baseEnd_5629850 < baseStart_5629850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629860 : List Nat := [2, 3, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_5629860 : Nat := 118140960795 + 5629860 * 2 ^ 59
def prefixEnd_5629860 : Nat := 4983230072969 + 3 ^ 40 * 5629860 * 2
def baseEnd_5629860 : Nat := 2890824197521448380558751

theorem tailTrace_5629860 : CollatzResearch.WordTrace tailWord_5629860 prefixEnd_5629860 2890824197521448380558751 := by
  unfold tailWord_5629860
  simp only [CollatzResearch.WordTrace]
  refine ⟨102668931691993099191951517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136891908922657465589268689 102668931691993099191951517)
  ·
    refine ⟨38500849384497412196981819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102668931691993099191951517 38500849384497412196981819)
    ·
      refine ⟨57751274076746118295472729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38500849384497412196981819 57751274076746118295472729)
      ·
        refine ⟨43313455557559588721604547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57751274076746118295472729 43313455557559588721604547)
        ·
          refine ⟨64970183336339383082406821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43313455557559588721604547 64970183336339383082406821)
          ·
            refine ⟨12181909375563634327951279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64970183336339383082406821 12181909375563634327951279)
            ·
              refine ⟨18272864063345451491926919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12181909375563634327951279 18272864063345451491926919)
              ·
                refine ⟨27409296095018177237890379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18272864063345451491926919 27409296095018177237890379)
                ·
                  refine ⟨41113944142527265856835569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27409296095018177237890379 41113944142527265856835569)
                  ·
                    refine ⟨30835458106895449392626677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41113944142527265856835569 30835458106895449392626677)
                    ·
                      refine ⟨2890824197521448380558751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30835458106895449392626677 2890824197521448380558751)
                      ·
                        rfl

theorem cell23_5629860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_5629860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629860 prefixEnd_5629860 := by exact prefixLift 5629860
  have htrace : WordTrace (prefixWord ++ tailWord_5629860) baseStart_5629860 baseEnd_5629860 := by
    simpa [prefixWord, tailWord_5629860, baseEnd_5629860] using wordTrace_append hprefix tailTrace_5629860
  have hstable : (prefixWord ++ tailWord_5629860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629860).length < 2 ^ (prefixWord ++ tailWord_5629860).sum := by decide
  have hdescent : baseEnd_5629860 < baseStart_5629860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629880 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_5629880 : Nat := 118140960795 + 5629880 * 2 ^ 59
def prefixEnd_5629880 : Nat := 4983230072969 + 3 ^ 40 * 5629880 * 2
def baseEnd_5629880 : Nat := 963611489044846100769553

theorem tailTrace_5629880 : CollatzResearch.WordTrace tailWord_5629880 prefixEnd_5629880 963611489044846100769553 := by
  unfold tailWord_5629880
  simp only [CollatzResearch.WordTrace]
  refine ⟨102669296421956870899815547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136892395229275827866420729 102669296421956870899815547)
  ·
    refine ⟨154003944632935306349723321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102669296421956870899815547 154003944632935306349723321)
    ·
      refine ⟨115502958474701479762292491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 154003944632935306349723321 115502958474701479762292491)
      ·
        refine ⟨173254437712052219643438737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115502958474701479762292491 173254437712052219643438737)
        ·
          refine ⟨129940828284039164732579053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173254437712052219643438737 129940828284039164732579053)
          ·
            refine ⟨48727810606514686774717145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129940828284039164732579053 48727810606514686774717145)
            ·
              refine ⟨36545857954886015081037859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48727810606514686774717145 36545857954886015081037859)
              ·
                refine ⟨54818786932329022621556789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36545857954886015081037859 54818786932329022621556789)
                ·
                  refine ⟨5139261274905845870770949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54818786932329022621556789 5139261274905845870770949)
                  ·
                    refine ⟨963611489044846100769553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139261274905845870770949 963611489044846100769553)
                    ·
                      rfl

theorem cell23_5629880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_5629880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629880 prefixEnd_5629880 := by exact prefixLift 5629880
  have htrace : WordTrace (prefixWord ++ tailWord_5629880) baseStart_5629880 baseEnd_5629880 := by
    simpa [prefixWord, tailWord_5629880, baseEnd_5629880] using wordTrace_append hprefix tailTrace_5629880
  have hstable : (prefixWord ++ tailWord_5629880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629880).length < 2 ^ (prefixWord ++ tailWord_5629880).sum := by decide
  have hdescent : baseEnd_5629880 < baseStart_5629880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629883 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4]
def baseStart_5629883 : Nat := 118140960795 + 5629883 * 2 ^ 59
def prefixEnd_5629883 : Nat := 4983230072969 + 3 ^ 40 * 5629883 * 2
def baseEnd_5629883 : Nat := 2890836007576501790571145

theorem tailTrace_5629883 : CollatzResearch.WordTrace tailWord_5629883 prefixEnd_5629883 2890836007576501790571145 := by
  unfold tailWord_5629883
  simp only [CollatzResearch.WordTrace]
  refine ⟨205338702262902873311990303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136892468175268582207993535 205338702262902873311990303)
  ·
    refine ⟨308008053394354309967985455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205338702262902873311990303 308008053394354309967985455)
    ·
      refine ⟨462012080091531464951978183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308008053394354309967985455 462012080091531464951978183)
      ·
        refine ⟨693018120137297197427967275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462012080091531464951978183 693018120137297197427967275)
        ·
          refine ⟨1039527180205945796141950913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693018120137297197427967275 1039527180205945796141950913)
          ·
            refine ⟨779645385154459347106463185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039527180205945796141950913 779645385154459347106463185)
            ·
              refine ⟨584734038865844510329847389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779645385154459347106463185 584734038865844510329847389)
              ·
                refine ⟨219275264574691691373692771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584734038865844510329847389 219275264574691691373692771)
                ·
                  refine ⟨328912896862037537060539157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219275264574691691373692771 328912896862037537060539157)
                  ·
                    refine ⟨15417792040408009549712773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 328912896862037537060539157 15417792040408009549712773)
                    ·
                      refine ⟨2890836007576501790571145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15417792040408009549712773 2890836007576501790571145)
                      ·
                        rfl

theorem cell23_5629883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 6, 4].length) (baseStart_5629883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629883 prefixEnd_5629883 := by exact prefixLift 5629883
  have htrace : WordTrace (prefixWord ++ tailWord_5629883) baseStart_5629883 baseEnd_5629883 := by
    simpa [prefixWord, tailWord_5629883, baseEnd_5629883] using wordTrace_append hprefix tailTrace_5629883
  have hstable : (prefixWord ++ tailWord_5629883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629883).length < 2 ^ (prefixWord ++ tailWord_5629883).sum := by decide
  have hdescent : baseEnd_5629883 < baseStart_5629883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629884 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_5629884 : Nat := 118140960795 + 5629884 * 2 ^ 59
def prefixEnd_5629884 : Nat := 4983230072969 + 3 ^ 40 * 5629884 * 2
def baseEnd_5629884 : Nat := 963612173685718762219547

theorem tailTrace_5629884 : CollatzResearch.WordTrace tailWord_5629884 prefixEnd_5629884 963612173685718762219547 := by
  unfold tailWord_5629884
  simp only [CollatzResearch.WordTrace]
  refine ⟨102669369367949625241388353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136892492490599500321851137 102669369367949625241388353)
  ·
    refine ⟨77002027025962218931041265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102669369367949625241388353 77002027025962218931041265)
    ·
      refine ⟨57751520269471664198280949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77002027025962218931041265 57751520269471664198280949)
      ·
        refine ⟨5414205025262968518588839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57751520269471664198280949 5414205025262968518588839)
        ·
          refine ⟨8121307537894452777883259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5414205025262968518588839 8121307537894452777883259)
          ·
            refine ⟨12181961306841679166824889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121307537894452777883259 12181961306841679166824889)
            ·
              refine ⟨9136470980131259375118667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12181961306841679166824889 9136470980131259375118667)
              ·
                refine ⟨13704706470196889062678001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9136470980131259375118667 13704706470196889062678001)
                ·
                  refine ⟨10278529852647666797008501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13704706470196889062678001 10278529852647666797008501)
                  ·
                    refine ⟨963612173685718762219547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278529852647666797008501 963612173685718762219547)
                    ·
                      rfl

theorem cell23_5629884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_5629884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629884 prefixEnd_5629884 := by exact prefixLift 5629884
  have htrace : WordTrace (prefixWord ++ tailWord_5629884) baseStart_5629884 baseEnd_5629884 := by
    simpa [prefixWord, tailWord_5629884, baseEnd_5629884] using wordTrace_append hprefix tailTrace_5629884
  have hstable : (prefixWord ++ tailWord_5629884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629884).length < 2 ^ (prefixWord ++ tailWord_5629884).sum := by decide
  have hdescent : baseEnd_5629884 < baseStart_5629884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629893 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 8]
def baseStart_5629893 : Nat := 118140960795 + 5629893 * 2 ^ 59
def prefixEnd_5629893 : Nat := 4983230072969 + 3 ^ 40 * 5629893 * 2
def baseEnd_5629893 : Nat := 321204571375894083494011

theorem tailTrace_5629893 : CollatzResearch.WordTrace tailWord_5629893 prefixEnd_5629893 321204571375894083494011 := by
  unfold tailWord_5629893
  simp only [CollatzResearch.WordTrace]
  refine ⟨205339066992866645019854333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136892711328577763346569555 205339066992866645019854333)
  ·
    refine ⟨77002150122324991882445375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205339066992866645019854333 77002150122324991882445375)
    ·
      refine ⟨115503225183487487823668063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77002150122324991882445375 115503225183487487823668063)
      ·
        refine ⟨173254837775231231735502095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115503225183487487823668063 173254837775231231735502095)
        ·
          refine ⟨259882256662846847603253143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173254837775231231735502095 259882256662846847603253143)
          ·
            refine ⟨389823384994270271404879715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259882256662846847603253143 389823384994270271404879715)
            ·
              refine ⟨584735077491405407107319573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389823384994270271404879715 584735077491405407107319573)
              ·
                refine ⟨27409456757409628458155605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 584735077491405407107319573 27409456757409628458155605)
                ·
                  refine ⟨321204571375894083494011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27409456757409628458155605 321204571375894083494011)
                  ·
                    rfl

theorem cell23_5629893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 8].length) (baseStart_5629893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629893 prefixEnd_5629893 := by exact prefixLift 5629893
  have htrace : WordTrace (prefixWord ++ tailWord_5629893) baseStart_5629893 baseEnd_5629893 := by
    simpa [prefixWord, tailWord_5629893, baseEnd_5629893] using wordTrace_append hprefix tailTrace_5629893
  have hstable : (prefixWord ++ tailWord_5629893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629893).length < 2 ^ (prefixWord ++ tailWord_5629893).sum := by decide
  have hdescent : baseEnd_5629893 < baseStart_5629893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629957 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 1, 5]
def baseStart_5629957 : Nat := 118140960795 + 5629957 * 2 ^ 59
def prefixEnd_5629957 : Nat := 4983230072969 + 3 ^ 40 * 5629957 * 2
def baseEnd_5629957 : Nat := 963624668381644833681935

theorem tailTrace_5629957 : CollatzResearch.WordTrace tailWord_5629957 prefixEnd_5629957 963624668381644833681935 := by
  unfold tailWord_5629957
  simp only [CollatzResearch.WordTrace]
  refine ⟨205341401264634783950184125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136894267509756522633456083 205341401264634783950184125)
  ·
    refine ⟨77003025474238043981319047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 205341401264634783950184125 77003025474238043981319047)
    ·
      refine ⟨115504538211357065971978571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77003025474238043981319047 115504538211357065971978571)
      ·
        refine ⟨173256807317035598957967857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115504538211357065971978571 173256807317035598957967857)
        ·
          refine ⟨129942605487776699218475893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 173256807317035598957967857 129942605487776699218475893)
          ·
            refine ⟨12182119264479065551732115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 129942605487776699218475893 12182119264479065551732115)
            ·
              refine ⟨18273178896718598327598173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182119264479065551732115 18273178896718598327598173)
              ·
                refine ⟨6852442086269474372849315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18273178896718598327598173 6852442086269474372849315)
                ·
                  refine ⟨10278663129404211559273973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852442086269474372849315 10278663129404211559273973)
                  ·
                    refine ⟨963624668381644833681935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278663129404211559273973 963624668381644833681935)
                    ·
                      rfl

theorem cell23_5629957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 5].length) (baseStart_5629957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629957 prefixEnd_5629957 := by exact prefixLift 5629957
  have htrace : WordTrace (prefixWord ++ tailWord_5629957) baseStart_5629957 baseEnd_5629957 := by
    simpa [prefixWord, tailWord_5629957, baseEnd_5629957] using wordTrace_append hprefix tailTrace_5629957
  have hstable : (prefixWord ++ tailWord_5629957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629957).length < 2 ^ (prefixWord ++ tailWord_5629957).sum := by decide
  have hdescent : baseEnd_5629957 < baseStart_5629957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629991 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 1, 5]
def baseStart_5629991 : Nat := 118140960795 + 5629991 * 2 ^ 59
def prefixEnd_5629991 : Nat := 4983230072969 + 3 ^ 40 * 5629991 * 2
def baseEnd_5629991 : Nat := 963630487829062456006883

theorem tailTrace_5629991 : CollatzResearch.WordTrace tailWord_5629991 prefixEnd_5629991 963630487829062456006883 := by
  unfold tailWord_5629991
  simp only [CollatzResearch.WordTrace]
  refine ⟨205342641346511607756921827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136895094231007738504614551 205342641346511607756921827)
  ·
    refine ⟨308013962019767411635382741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205342641346511607756921827 308013962019767411635382741)
    ·
      refine ⟨7219077234838298710204283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 308013962019767411635382741 7219077234838298710204283)
      ·
        refine ⟨10828615852257448065306425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219077234838298710204283 10828615852257448065306425)
        ·
          refine ⟨8121461889193086048979819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10828615852257448065306425 8121461889193086048979819)
          ·
            refine ⟨12182192833789629073469729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121461889193086048979819 12182192833789629073469729)
            ·
              refine ⟨9136644625342221805102297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12182192833789629073469729 9136644625342221805102297)
              ·
                refine ⟨6852483469006666353826723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9136644625342221805102297 6852483469006666353826723)
                ·
                  refine ⟨10278725203509999530740085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852483469006666353826723 10278725203509999530740085)
                  ·
                    refine ⟨963630487829062456006883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10278725203509999530740085 963630487829062456006883)
                    ·
                      rfl

theorem cell23_5629991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_5629991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629991 prefixEnd_5629991 := by exact prefixLift 5629991
  have htrace : WordTrace (prefixWord ++ tailWord_5629991) baseStart_5629991 baseEnd_5629991 := by
    simpa [prefixWord, tailWord_5629991, baseEnd_5629991] using wordTrace_append hprefix tailTrace_5629991
  have hstable : (prefixWord ++ tailWord_5629991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629991).length < 2 ^ (prefixWord ++ tailWord_5629991).sum := by decide
  have hdescent : baseEnd_5629991 < baseStart_5629991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5629994 : List Nat := [3, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_5629994 : Nat := 118140960795 + 5629994 * 2 ^ 59
def prefixEnd_5629994 : Nat := 4983230072969 + 3 ^ 40 * 5629994 * 2
def baseEnd_5629994 : Nat := 2890893003929150856283135

theorem tailTrace_5629994 : CollatzResearch.WordTrace tailWord_5629994 prefixEnd_5629994 2890893003929150856283135 := by
  unfold tailWord_5629994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51335687691375184817320259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136895167177000492846187357 51335687691375184817320259)
  ·
    refine ⟨77003531537062777225980389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51335687691375184817320259 77003531537062777225980389)
    ·
      refine ⟨14438162163199270729871323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77003531537062777225980389 14438162163199270729871323)
      ·
        refine ⟨21657243244798906094806985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438162163199270729871323 21657243244798906094806985)
        ·
          refine ⟨16242932433599179571105239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21657243244798906094806985 16242932433599179571105239)
          ·
            refine ⟨24364398650398769356657859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16242932433599179571105239 24364398650398769356657859)
            ·
              refine ⟨36546597975598154034986789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24364398650398769356657859 36546597975598154034986789)
              ·
                refine ⟨6852487120424653881560023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36546597975598154034986789 6852487120424653881560023)
                ·
                  refine ⟨10278730680636980822340035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6852487120424653881560023 10278730680636980822340035)
                  ·
                    refine ⟨15418096020955471233510053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10278730680636980822340035 15418096020955471233510053)
                    ·
                      refine ⟨2890893003929150856283135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15418096020955471233510053 2890893003929150856283135)
                      ·
                        rfl

theorem cell23_5629994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_5629994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5629994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5629994 prefixEnd_5629994 := by exact prefixLift 5629994
  have htrace : WordTrace (prefixWord ++ tailWord_5629994) baseStart_5629994 baseEnd_5629994 := by
    simpa [prefixWord, tailWord_5629994, baseEnd_5629994] using wordTrace_append hprefix tailTrace_5629994
  have hstable : (prefixWord ++ tailWord_5629994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5629994).length < 2 ^ (prefixWord ++ tailWord_5629994).sum := by decide
  have hdescent : baseEnd_5629994 < baseStart_5629994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5629994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630000 : List Nat := [2, 1, 1, 1, 2, 6, 1, 9]
def baseStart_5630000 : Nat := 118140960795 + 5630000 * 2 ^ 59
def prefixEnd_5630000 : Nat := 4983230072969 + 3 ^ 40 * 5630000 * 2
def baseEnd_5630000 : Nat := 107070225363447327141041

theorem tailTrace_5630000 : CollatzResearch.WordTrace tailWord_5630000 prefixEnd_5630000 107070225363447327141041 := by
  unfold tailWord_5630000
  simp only [CollatzResearch.WordTrace]
  refine ⟨102671484801739501146999727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136895313068986001529332969 102671484801739501146999727)
  ·
    refine ⟨154007227202609251720499591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102671484801739501146999727 154007227202609251720499591)
    ·
      refine ⟨231010840803913877580749387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154007227202609251720499591 231010840803913877580749387)
      ·
        refine ⟨346516261205870816371124081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 231010840803913877580749387 346516261205870816371124081)
        ·
          refine ⟨259887195904403112278343061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346516261205870816371124081 259887195904403112278343061)
          ·
            refine ⟨12182212308018895888047331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 259887195904403112278343061 12182212308018895888047331)
            ·
              refine ⟨18273318462028343832070997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182212308018895888047331 18273318462028343832070997)
              ·
                refine ⟨107070225363447327141041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18273318462028343832070997 107070225363447327141041)
                ·
                  rfl

theorem cell23_5630000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_5630000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630000 prefixEnd_5630000 := by exact prefixLift 5630000
  have htrace : WordTrace (prefixWord ++ tailWord_5630000) baseStart_5630000 baseEnd_5630000 := by
    simpa [prefixWord, tailWord_5630000, baseEnd_5630000] using wordTrace_append hprefix tailTrace_5630000
  have hstable : (prefixWord ++ tailWord_5630000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630000).length < 2 ^ (prefixWord ++ tailWord_5630000).sum := by decide
  have hdescent : baseEnd_5630000 < baseStart_5630000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630017 : List Nat := [1, 2, 5, 1, 2, 3, 9]
def baseStart_5630017 : Nat := 118140960795 + 5630017 * 2 ^ 59
def prefixEnd_5630017 : Nat := 4983230072969 + 3 ^ 40 * 5630017 * 2
def baseEnd_5630017 : Nat := 35690182888693879830809

theorem tailTrace_5630017 : CollatzResearch.WordTrace tailWord_5630017 prefixEnd_5630017 35690182888693879830809 := by
  unfold tailWord_5630017
  simp only [CollatzResearch.WordTrace]
  refine ⟨205343589644417414197368305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136895726429611609464912203 205343589644417414197368305)
  ·
    refine ⟨154007692233313060648026229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 205343589644417414197368305 154007692233313060648026229)
    ·
      refine ⟨14438221146873099435752459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 154007692233313060648026229 14438221146873099435752459)
      ·
        refine ⟨21657331720309649153628689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14438221146873099435752459 21657331720309649153628689)
        ·
          refine ⟨16242998790232236865221517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21657331720309649153628689 16242998790232236865221517)
          ·
            refine ⟨6091124546337088824458069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16242998790232236865221517 6091124546337088824458069)
            ·
              refine ⟨35690182888693879830809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6091124546337088824458069 35690182888693879830809)
              ·
                rfl

theorem cell23_5630017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 9].length) (baseStart_5630017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630017 prefixEnd_5630017 := by exact prefixLift 5630017
  have htrace : WordTrace (prefixWord ++ tailWord_5630017) baseStart_5630017 baseEnd_5630017 := by
    simpa [prefixWord, tailWord_5630017, baseEnd_5630017] using wordTrace_append hprefix tailTrace_5630017
  have hstable : (prefixWord ++ tailWord_5630017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630017).length < 2 ^ (prefixWord ++ tailWord_5630017).sum := by decide
  have hdescent : baseEnd_5630017 < baseStart_5630017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630038 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_5630038 : Nat := 118140960795 + 5630038 * 2 ^ 59
def prefixEnd_5630038 : Nat := 4983230072969 + 3 ^ 40 * 5630038 * 2
def baseEnd_5630038 : Nat := 963638532359316228044311

theorem tailTrace_5630038 : CollatzResearch.WordTrace tailWord_5630038 prefixEnd_5630038 963638532359316228044311 := by
  unfold tailWord_5630038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834022223583833423992673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136896237051560889855921845 12834022223583833423992673)
  ·
    refine ⟨9625516667687875067994505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12834022223583833423992673 9625516667687875067994505)
    ·
      refine ⟨7219137500765906300995879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9625516667687875067994505 7219137500765906300995879)
      ·
        refine ⟨10828706251148859451493819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7219137500765906300995879 10828706251148859451493819)
        ·
          refine ⟨16243059376723289177240729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10828706251148859451493819 16243059376723289177240729)
          ·
            refine ⟨12182294532542466882930547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16243059376723289177240729 12182294532542466882930547)
            ·
              refine ⟨18273441798813700324395821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182294532542466882930547 18273441798813700324395821)
              ·
                refine ⟨6852540674555137621648433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18273441798813700324395821 6852540674555137621648433)
                ·
                  refine ⟨5139405505916353216236325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6852540674555137621648433 5139405505916353216236325)
                  ·
                    refine ⟨963638532359316228044311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5139405505916353216236325 963638532359316228044311)
                    ·
                      rfl

theorem cell23_5630038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_5630038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630038 prefixEnd_5630038 := by exact prefixLift 5630038
  have htrace : WordTrace (prefixWord ++ tailWord_5630038) baseStart_5630038 baseEnd_5630038 := by
    simpa [prefixWord, tailWord_5630038, baseEnd_5630038] using wordTrace_append hprefix tailTrace_5630038
  have hstable : (prefixWord ++ tailWord_5630038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630038).length < 2 ^ (prefixWord ++ tailWord_5630038).sum := by decide
  have hdescent : baseEnd_5630038 < baseStart_5630038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630080 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_5630080 : Nat := 118140960795 + 5630080 * 2 ^ 59
def prefixEnd_5630080 : Nat := 4983230072969 + 3 ^ 40 * 5630080 * 2
def baseEnd_5630080 : Nat := 2890937163265437519807739

theorem tailTrace_5630080 : CollatzResearch.WordTrace tailWord_5630080 prefixEnd_5630080 2890937163265437519807739 := by
  unfold tailWord_5630080
  simp only [CollatzResearch.WordTrace]
  refine ⟨102672943721594587978455847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136897258295459450637941129 102672943721594587978455847)
  ·
    refine ⟨154009415582391881967683771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102672943721594587978455847 154009415582391881967683771)
    ·
      refine ⟨231014123373587822951525657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154009415582391881967683771 231014123373587822951525657)
      ·
        refine ⟨173260592530190867213644243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231014123373587822951525657 173260592530190867213644243)
        ·
          refine ⟨259890888795286300820466365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173260592530190867213644243 259890888795286300820466365)
          ·
            refine ⟨97459083298232362807674887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259890888795286300820466365 97459083298232362807674887)
            ·
              refine ⟨146188624947348544211512331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97459083298232362807674887 146188624947348544211512331)
              ·
                refine ⟨219282937421022816317268497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146188624947348544211512331 219282937421022816317268497)
                ·
                  refine ⟨164462203065767112237951373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 219282937421022816317268497 164462203065767112237951373)
                  ·
                    refine ⟨61673326149662667089231765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 164462203065767112237951373 61673326149662667089231765)
                    ·
                      refine ⟨2890937163265437519807739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61673326149662667089231765 2890937163265437519807739)
                      ·
                        rfl

theorem cell23_5630080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_5630080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630080 prefixEnd_5630080 := by exact prefixLift 5630080
  have htrace : WordTrace (prefixWord ++ tailWord_5630080) baseStart_5630080 baseEnd_5630080 := by
    simpa [prefixWord, tailWord_5630080, baseEnd_5630080] using wordTrace_append hprefix tailTrace_5630080
  have hstable : (prefixWord ++ tailWord_5630080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630080).length < 2 ^ (prefixWord ++ tailWord_5630080).sum := by decide
  have hdescent : baseEnd_5630080 < baseStart_5630080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630084 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_5630084 : Nat := 118140960795 + 5630084 * 2 ^ 59
def prefixEnd_5630084 : Nat := 4983230072969 + 3 ^ 40 * 5630084 * 2
def baseEnd_5630084 : Nat := 2890939217188055504157721

theorem tailTrace_5630084 : CollatzResearch.WordTrace tailWord_5630084 prefixEnd_5630084 2890939217188055504157721 := by
  unfold tailWord_5630084
  simp only [CollatzResearch.WordTrace]
  refine ⟨102673016667587342320028653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136897355556783123093371537 102673016667587342320028653)
  ·
    refine ⟨38502381250345253370010745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102673016667587342320028653 38502381250345253370010745)
    ·
      refine ⟨28876785937758940027508059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38502381250345253370010745 28876785937758940027508059)
      ·
        refine ⟨43315178906638410041262089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28876785937758940027508059 43315178906638410041262089)
        ·
          refine ⟨32486384179978807530946567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43315178906638410041262089 32486384179978807530946567)
          ·
            refine ⟨48729576269968211296419851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32486384179978807530946567 48729576269968211296419851)
            ·
              refine ⟨73094364404952316944629777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48729576269968211296419851 73094364404952316944629777)
              ·
                refine ⟨54820773303714237708472333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73094364404952316944629777 54820773303714237708472333)
                ·
                  refine ⟨20557789988892839140677125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54820773303714237708472333 20557789988892839140677125)
                  ·
                    refine ⟨3854585622917407338876961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20557789988892839140677125 3854585622917407338876961)
                    ·
                      refine ⟨2890939217188055504157721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3854585622917407338876961 2890939217188055504157721)
                      ·
                        rfl

theorem cell23_5630084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_5630084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630084 prefixEnd_5630084 := by exact prefixLift 5630084
  have htrace : WordTrace (prefixWord ++ tailWord_5630084) baseStart_5630084 baseEnd_5630084 := by
    simpa [prefixWord, tailWord_5630084, baseEnd_5630084] using wordTrace_append hprefix tailTrace_5630084
  have hstable : (prefixWord ++ tailWord_5630084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630084).length < 2 ^ (prefixWord ++ tailWord_5630084).sum := by decide
  have hdescent : baseEnd_5630084 < baseStart_5630084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630087 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3]
def baseStart_5630087 : Nat := 118140960795 + 5630087 * 2 ^ 59
def prefixEnd_5630087 : Nat := 4983230072969 + 3 ^ 40 * 5630087 * 2
def baseEnd_5630087 : Nat := 2890940757630018992420207

theorem tailTrace_5630087 : CollatzResearch.WordTrace tailWord_5630087 prefixEnd_5630087 2890940757630018992420207 := by
  unfold tailWord_5630087
  simp only [CollatzResearch.WordTrace]
  refine ⟨205346142754163816152416515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136897428502775877434944343 205346142754163816152416515)
  ·
    refine ⟨308019214131245724228624773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 205346142754163816152416515 308019214131245724228624773)
    ·
      refine ⟨57753602649608573292867145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 308019214131245724228624773 57753602649608573292867145)
      ·
        refine ⟨43315201987206429969650359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57753602649608573292867145 43315201987206429969650359)
        ·
          refine ⟨64972802980809644954475539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43315201987206429969650359 64972802980809644954475539)
          ·
            refine ⟨97459204471214467431713309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64972802980809644954475539 97459204471214467431713309)
            ·
              refine ⟨36547201676705425286892491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97459204471214467431713309 36547201676705425286892491)
              ·
                refine ⟨54820802515058137930338737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36547201676705425286892491 54820802515058137930338737)
                ·
                  refine ⟨41115601886293603447754053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54820802515058137930338737 41115601886293603447754053)
                  ·
                    refine ⟨7709175353680050646453885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41115601886293603447754053 7709175353680050646453885)
                    ·
                      refine ⟨2890940757630018992420207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7709175353680050646453885 2890940757630018992420207)
                      ·
                        rfl

theorem cell23_5630087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_5630087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630087 prefixEnd_5630087 := by exact prefixLift 5630087
  have htrace : WordTrace (prefixWord ++ tailWord_5630087) baseStart_5630087 baseEnd_5630087 := by
    simpa [prefixWord, tailWord_5630087, baseEnd_5630087] using wordTrace_append hprefix tailTrace_5630087
  have hstable : (prefixWord ++ tailWord_5630087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630087).length < 2 ^ (prefixWord ++ tailWord_5630087).sum := by decide
  have hdescent : baseEnd_5630087 < baseStart_5630087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5630094 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_5630094 : Nat := 118140960795 + 5630094 * 2 ^ 59
def prefixEnd_5630094 : Nat := 4983230072969 + 3 ^ 40 * 5630094 * 2
def baseEnd_5630094 : Nat := 963648117331533488344225

theorem tailTrace_5630094 : CollatzResearch.WordTrace tailWord_5630094 prefixEnd_5630094 963648117331533488344225 := by
  unfold tailWord_5630094
  simp only [CollatzResearch.WordTrace]
  refine ⟨25668299758142307043490167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136897598710092304231947557 25668299758142307043490167)
  ·
    refine ⟨38502449637213460565235251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25668299758142307043490167 38502449637213460565235251)
    ·
      refine ⟨57753674455820190847852877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38502449637213460565235251 57753674455820190847852877)
      ·
        refine ⟨21657627920932571567944829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57753674455820190847852877 21657627920932571567944829)
        ·
          refine ⟨8121610470349714337979311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21657627920932571567944829 8121610470349714337979311)
          ·
            refine ⟨12182415705524571506968967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121610470349714337979311 12182415705524571506968967)
            ·
              refine ⟨18273623558286857260453451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12182415705524571506968967 18273623558286857260453451)
              ·
                refine ⟨27410435337430285890680177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18273623558286857260453451 27410435337430285890680177)
                ·
                  refine ⟨20557826503072714418010133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27410435337430285890680177 20557826503072714418010133)
                  ·
                    refine ⟨963648117331533488344225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20557826503072714418010133 963648117331533488344225)
                    ·
                      rfl

theorem cell23_5630094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_5630094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5630094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5630094 prefixEnd_5630094 := by exact prefixLift 5630094
  have htrace : WordTrace (prefixWord ++ tailWord_5630094) baseStart_5630094 baseEnd_5630094 := by
    simpa [prefixWord, tailWord_5630094, baseEnd_5630094] using wordTrace_append hprefix tailTrace_5630094
  have hstable : (prefixWord ++ tailWord_5630094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5630094).length < 2 ^ (prefixWord ++ tailWord_5630094).sum := by decide
  have hdescent : baseEnd_5630094 < baseStart_5630094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5630094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
