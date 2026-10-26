import V185TrunkScan21Chunk101

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1238526 : List Nat := [4, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1238526 : Nat := 118140960795 + 1238526 * 2 ^ 59
def prefixEnd_1238526 : Nat := 4983230072969 + 3 ^ 40 * 1238526 * 2
def baseEnd_1238526 : Nat := 94216169050448369633945

theorem tailTrace_1238526 : CollatzResearch.WordTrace tailWord_1238526 prefixEnd_1238526 94216169050448369633945 := by
  unfold tailWord_1238526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646594288879912530708929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30115169540692866830447621 5646594288879912530708929)
  ·
    refine ⟨4234945716659934398031697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5646594288879912530708929 4234945716659934398031697)
    ·
      refine ⟨3176209287494950798523773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4234945716659934398031697 3176209287494950798523773)
      ·
        refine ⟨1191078482810606549446415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3176209287494950798523773 1191078482810606549446415)
        ·
          refine ⟨1786617724215909824169623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191078482810606549446415 1786617724215909824169623)
          ·
            refine ⟨2679926586323864736254435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786617724215909824169623 2679926586323864736254435)
            ·
              refine ⟨4019889879485797104381653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2679926586323864736254435 4019889879485797104381653)
              ·
                refine ⟨94216169050448369633945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4019889879485797104381653 94216169050448369633945)
                ·
                  rfl

theorem cell21_1238526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1238526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238526 prefixEnd_1238526 := by exact prefixLift 1238526
  have htrace : WordTrace (prefixWord ++ tailWord_1238526) baseStart_1238526 baseEnd_1238526 := by
    simpa [prefixWord, tailWord_1238526, baseEnd_1238526] using wordTrace_append hprefix tailTrace_1238526
  have hstable : (prefixWord ++ tailWord_1238526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238526).length < 2 ^ (prefixWord ++ tailWord_1238526).sum := by decide
  have hdescent : baseEnd_1238526 < baseStart_1238526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238557 : List Nat := [1, 4, 2, 2, 1, 1, 5, 2, 3]
def baseStart_1238557 : Nat := 118140960795 + 1238557 * 2 ^ 59
def prefixEnd_1238557 : Nat := 4983230072969 + 3 ^ 40 * 1238557 * 2
def baseEnd_1238557 : Nat := 282655581773695943885105

theorem tailTrace_1238557 : CollatzResearch.WordTrace tailWord_1238557 prefixEnd_1238557 282655581773695943885105 := by
  unfold tailWord_1238557
  simp only [CollatzResearch.WordTrace]
  refine ⟨45173884973926992540049925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30115923315951328360033283 45173884973926992540049925)
  ·
    refine ⟨8470103432611311101259361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45173884973926992540049925 8470103432611311101259361)
    ·
      refine ⟨6352577574458483325944521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8470103432611311101259361 6352577574458483325944521)
      ·
        refine ⟨4764433180843862494458391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6352577574458483325944521 4764433180843862494458391)
        ·
          refine ⟨7146649771265793741687587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764433180843862494458391 7146649771265793741687587)
          ·
            refine ⟨10719974656898690612531381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146649771265793741687587 10719974656898690612531381)
            ·
              refine ⟨1004997624084252244924817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10719974656898690612531381 1004997624084252244924817)
              ·
                refine ⟨753748218063189183693613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004997624084252244924817 753748218063189183693613)
                ·
                  refine ⟨282655581773695943885105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 753748218063189183693613 282655581773695943885105)
                  ·
                    rfl

theorem cell21_1238557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_1238557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238557 prefixEnd_1238557 := by exact prefixLift 1238557
  have htrace : WordTrace (prefixWord ++ tailWord_1238557) baseStart_1238557 baseEnd_1238557 := by
    simpa [prefixWord, tailWord_1238557, baseEnd_1238557] using wordTrace_append hprefix tailTrace_1238557
  have hstable : (prefixWord ++ tailWord_1238557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238557).length < 2 ^ (prefixWord ++ tailWord_1238557).sum := by decide
  have hdescent : baseEnd_1238557 < baseStart_1238557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238664 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 4]
def baseStart_1238664 : Nat := 118140960795 + 1238664 * 2 ^ 59
def prefixEnd_1238664 : Nat := 4983230072969 + 3 ^ 40 * 1238664 * 2
def baseEnd_1238664 : Nat := 282680000631487535601553

theorem tailTrace_1238664 : CollatzResearch.WordTrace tailWord_1238664 prefixEnd_1238664 282680000631487535601553 := by
  unfold tailWord_1238664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22588893792269674907097523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30118525056359566542796697 22588893792269674907097523)
  ·
    refine ⟨33883340688404512360646285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22588893792269674907097523 33883340688404512360646285)
    ·
      refine ⟨12706252758151692135242357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33883340688404512360646285 12706252758151692135242357)
      ·
        refine ⟨1191211196076721137678971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12706252758151692135242357 1191211196076721137678971)
        ·
          refine ⟨1786816794115081706518457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191211196076721137678971 1786816794115081706518457)
          ·
            refine ⟨1340112595586311279888843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1786816794115081706518457 1340112595586311279888843)
            ·
              refine ⟨2010168893379466919833265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340112595586311279888843 2010168893379466919833265)
              ·
                refine ⟨1507626670034600189874949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010168893379466919833265 1507626670034600189874949)
                ·
                  refine ⟨282680000631487535601553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507626670034600189874949 282680000631487535601553)
                  ·
                    rfl

theorem cell21_1238664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 4].length) (baseStart_1238664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238664 prefixEnd_1238664 := by exact prefixLift 1238664
  have htrace : WordTrace (prefixWord ++ tailWord_1238664) baseStart_1238664 baseEnd_1238664 := by
    simpa [prefixWord, tailWord_1238664, baseEnd_1238664] using wordTrace_append hprefix tailTrace_1238664
  have hstable : (prefixWord ++ tailWord_1238664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238664).length < 2 ^ (prefixWord ++ tailWord_1238664).sum := by decide
  have hdescent : baseEnd_1238664 < baseStart_1238664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238703 : List Nat := [1, 1, 2, 1, 2, 4, 3, 7]
def baseStart_1238703 : Nat := 118140960795 + 1238703 * 2 ^ 59
def prefixEnd_1238703 : Nat := 4983230072969 + 3 ^ 40 * 1238703 * 2
def baseEnd_1238703 : Nat := 94229633654277378150491

theorem tailTrace_1238703 : CollatzResearch.WordTrace tailWord_1238703 prefixEnd_1238703 94229633654277378150491 := by
  unfold tailWord_1238703
  simp only [CollatzResearch.WordTrace]
  refine ⟨45179210031398059474864763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30119473354265372983243175 45179210031398059474864763)
  ·
    refine ⟨67768815047097089212297145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45179210031398059474864763 67768815047097089212297145)
    ·
      refine ⟨50826611285322816909222859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67768815047097089212297145 50826611285322816909222859)
      ·
        refine ⟨76239916927984225363834289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50826611285322816909222859 76239916927984225363834289)
        ·
          refine ⟨57179937695988169022875717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76239916927984225363834289 57179937695988169022875717)
          ·
            refine ⟨10721238317997781691789197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57179937695988169022875717 10721238317997781691789197)
            ·
              refine ⟨4020464369249168134420949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10721238317997781691789197 4020464369249168134420949)
              ·
                refine ⟨94229633654277378150491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4020464369249168134420949 94229633654277378150491)
                ·
                  rfl

theorem cell21_1238703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 7].length) (baseStart_1238703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238703 prefixEnd_1238703 := by exact prefixLift 1238703
  have htrace : WordTrace (prefixWord ++ tailWord_1238703) baseStart_1238703 baseEnd_1238703 := by
    simpa [prefixWord, tailWord_1238703, baseEnd_1238703] using wordTrace_append hprefix tailTrace_1238703
  have hstable : (prefixWord ++ tailWord_1238703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238703).length < 2 ^ (prefixWord ++ tailWord_1238703).sum := by decide
  have hdescent : baseEnd_1238703 < baseStart_1238703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238726 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1238726 : Nat := 118140960795 + 1238726 * 2 ^ 59
def prefixEnd_1238726 : Nat := 4983230072969 + 3 ^ 40 * 1238726 * 2
def baseEnd_1238726 : Nat := 282694149876189205568093

theorem tailTrace_1238726 : CollatzResearch.WordTrace tailWord_1238726 prefixEnd_1238726 282694149876189205568093 := by
  unfold tailWord_1238726
  simp only [CollatzResearch.WordTrace]
  refine ⟨1411876528447335450092251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30120032606876489601968021 1411876528447335450092251)
  ·
    refine ⟨2117814792671003175138377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1411876528447335450092251 2117814792671003175138377)
    ·
      refine ⟨1588361094503252381353783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2117814792671003175138377 1588361094503252381353783)
      ·
        refine ⟨2382541641754878572030675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588361094503252381353783 2382541641754878572030675)
        ·
          refine ⟨3573812462632317858046013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382541641754878572030675 3573812462632317858046013)
          ·
            refine ⟨1340179673487119196767255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573812462632317858046013 1340179673487119196767255)
            ·
              refine ⟨2010269510230678795150883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340179673487119196767255 2010269510230678795150883)
              ·
                refine ⟨3015404265346018192726325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2010269510230678795150883 3015404265346018192726325)
                ·
                  refine ⟨282694149876189205568093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3015404265346018192726325 282694149876189205568093)
                  ·
                    rfl

theorem cell21_1238726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1238726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238726 prefixEnd_1238726 := by exact prefixLift 1238726
  have htrace : WordTrace (prefixWord ++ tailWord_1238726) baseStart_1238726 baseEnd_1238726 := by
    simpa [prefixWord, tailWord_1238726, baseEnd_1238726] using wordTrace_append hprefix tailTrace_1238726
  have hstable : (prefixWord ++ tailWord_1238726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238726).length < 2 ^ (prefixWord ++ tailWord_1238726).sum := by decide
  have hdescent : baseEnd_1238726 < baseStart_1238726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238740 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1238740 : Nat := 118140960795 + 1238740 * 2 ^ 59
def prefixEnd_1238740 : Nat := 4983230072969 + 3 ^ 40 * 1238740 * 2
def baseEnd_1238740 : Nat := 282697344866928292334731

theorem tailTrace_1238740 : CollatzResearch.WordTrace tailWord_1238740 prefixEnd_1238740 282697344866928292334731 := by
  unfold tailWord_1238740
  simp only [CollatzResearch.WordTrace]
  refine ⟨22590279766132007396980837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30120373021509343195974449 22590279766132007396980837)
  ·
    refine ⟨4235677456149751386933907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22590279766132007396980837 4235677456149751386933907)
    ·
      refine ⟨6353516184224627080400861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4235677456149751386933907 6353516184224627080400861)
      ·
        refine ⟨2382568569084235155150323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6353516184224627080400861 2382568569084235155150323)
        ·
          refine ⟨3573852853626352732725485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382568569084235155150323 3573852853626352732725485)
          ·
            refine ⟨1340194820109882274772057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573852853626352732725485 1340194820109882274772057)
            ·
              refine ⟨1005146115082411706079043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340194820109882274772057 1005146115082411706079043)
              ·
                refine ⟨1507719172623617559118565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005146115082411706079043 1507719172623617559118565)
                ·
                  refine ⟨282697344866928292334731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507719172623617559118565 282697344866928292334731)
                  ·
                    rfl

theorem cell21_1238740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1238740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238740 prefixEnd_1238740 := by exact prefixLift 1238740
  have htrace : WordTrace (prefixWord ++ tailWord_1238740) baseStart_1238740 baseEnd_1238740 := by
    simpa [prefixWord, tailWord_1238740, baseEnd_1238740] using wordTrace_append hprefix tailTrace_1238740
  have hstable : (prefixWord ++ tailWord_1238740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238740).length < 2 ^ (prefixWord ++ tailWord_1238740).sum := by decide
  have hdescent : baseEnd_1238740 < baseStart_1238740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238810 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_1238810 : Nat := 118140960795 + 1238810 * 2 ^ 59
def prefixEnd_1238810 : Nat := 4983230072969 + 3 ^ 40 * 1238810 * 2
def baseEnd_1238810 : Nat := 282713319820623726167921

theorem tailTrace_1238810 : CollatzResearch.WordTrace tailWord_1238810 prefixEnd_1238810 282713319820623726167921 := by
  unfold tailWord_1238810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11295778160502604187252471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30122075094673611166006589 11295778160502604187252471)
  ·
    refine ⟨16943667240753906280878707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11295778160502604187252471 16943667240753906280878707)
    ·
      refine ⟨25415500861130859421318061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16943667240753906280878707 25415500861130859421318061)
      ·
        refine ⟨9530812822924072282994273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25415500861130859421318061 9530812822924072282994273)
        ·
          refine ⟨7148109617193054212245705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9530812822924072282994273 7148109617193054212245705)
          ·
            refine ⟨5361082212894790659184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7148109617193054212245705 5361082212894790659184279)
            ·
              refine ⟨8041623319342185988776419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5361082212894790659184279 8041623319342185988776419)
              ·
                refine ⟨12062434979013278983164629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8041623319342185988776419 12062434979013278983164629)
                ·
                  refine ⟨282713319820623726167921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12062434979013278983164629 282713319820623726167921)
                  ·
                    rfl

theorem cell21_1238810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_1238810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238810 prefixEnd_1238810 := by exact prefixLift 1238810
  have htrace : WordTrace (prefixWord ++ tailWord_1238810) baseStart_1238810 baseEnd_1238810 := by
    simpa [prefixWord, tailWord_1238810, baseEnd_1238810] using wordTrace_append hprefix tailTrace_1238810
  have hstable : (prefixWord ++ tailWord_1238810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238810).length < 2 ^ (prefixWord ++ tailWord_1238810).sum := by decide
  have hdescent : baseEnd_1238810 < baseStart_1238810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238858 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_1238858 : Nat := 118140960795 + 1238858 * 2 ^ 59
def prefixEnd_1238858 : Nat := 4983230072969 + 3 ^ 40 * 1238858 * 2
def baseEnd_1238858 : Nat := 282724274074586309367823

theorem tailTrace_1238858 : CollatzResearch.WordTrace tailWord_1238858 prefixEnd_1238858 282724274074586309367823 := by
  unfold tailWord_1238858
  simp only [CollatzResearch.WordTrace]
  refine ⟨11296215836459130236689307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30123242230557680631171485 11296215836459130236689307)
  ·
    refine ⟨16944323754688695355033961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11296215836459130236689307 16944323754688695355033961)
    ·
      refine ⟨12708242816016521516275471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16944323754688695355033961 12708242816016521516275471)
      ·
        refine ⟨19062364224024782274413207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708242816016521516275471 19062364224024782274413207)
        ·
          refine ⟨28593546336037173411619811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19062364224024782274413207 28593546336037173411619811)
          ·
            refine ⟨42890319504055760117429717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28593546336037173411619811 42890319504055760117429717)
            ·
              refine ⟨1005241863376306877752259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 42890319504055760117429717 1005241863376306877752259)
              ·
                refine ⟨1507862795064460316628389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005241863376306877752259 1507862795064460316628389)
                ·
                  refine ⟨282724274074586309367823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507862795064460316628389 282724274074586309367823)
                  ·
                    rfl

theorem cell21_1238858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_1238858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238858 prefixEnd_1238858 := by exact prefixLift 1238858
  have htrace : WordTrace (prefixWord ++ tailWord_1238858) baseStart_1238858 baseEnd_1238858 := by
    simpa [prefixWord, tailWord_1238858, baseEnd_1238858] using wordTrace_append hprefix tailTrace_1238858
  have hstable : (prefixWord ++ tailWord_1238858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238858).length < 2 ^ (prefixWord ++ tailWord_1238858).sum := by decide
  have hdescent : baseEnd_1238858 < baseStart_1238858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238917 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 4]
def baseStart_1238917 : Nat := 118140960795 + 1238917 * 2 ^ 59
def prefixEnd_1238917 : Nat := 4983230072969 + 3 ^ 40 * 1238917 * 2
def baseEnd_1238917 : Nat := 282737738678415317884369

theorem tailTrace_1238917 : CollatzResearch.WordTrace tailWord_1238917 prefixEnd_1238917 282737738678415317884369 := by
  unfold tailWord_1238917
  simp only [CollatzResearch.WordTrace]
  refine ⟨45187015252622774023155005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30124676835081849348770003 45187015252622774023155005)
  ·
    refine ⟨16945130719733540258683127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45187015252622774023155005 16945130719733540258683127)
    ·
      refine ⟨25417696079600310388024691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16945130719733540258683127 25417696079600310388024691)
      ·
        refine ⟨38126544119400465582037037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25417696079600310388024691 38126544119400465582037037)
        ·
          refine ⟨14297454044775174593263889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38126544119400465582037037 14297454044775174593263889)
          ·
            refine ⟨10723090533581380944947917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14297454044775174593263889 10723090533581380944947917)
            ·
              refine ⟨4021158950093017854355469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10723090533581380944947917 4021158950093017854355469)
              ·
                refine ⟨1507934606284881695383301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021158950093017854355469 1507934606284881695383301)
                ·
                  refine ⟨282737738678415317884369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1507934606284881695383301 282737738678415317884369)
                  ·
                    rfl

theorem cell21_1238917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_1238917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238917 prefixEnd_1238917 := by exact prefixLift 1238917
  have htrace : WordTrace (prefixWord ++ tailWord_1238917) baseStart_1238917 baseEnd_1238917 := by
    simpa [prefixWord, tailWord_1238917, baseEnd_1238917] using wordTrace_append hprefix tailTrace_1238917
  have hstable : (prefixWord ++ tailWord_1238917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238917).length < 2 ^ (prefixWord ++ tailWord_1238917).sum := by decide
  have hdescent : baseEnd_1238917 < baseStart_1238917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1238996 : List Nat := [2, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_1238996 : Nat := 118140960795 + 1238996 * 2 ^ 59
def prefixEnd_1238996 : Nat := 4983230072969 + 3 ^ 40 * 1238996 * 2
def baseEnd_1238996 : Nat := 282755767554728736067541

theorem tailTrace_1238996 : CollatzResearch.WordTrace tailWord_1238996 prefixEnd_1238996 282755767554728736067541 := by
  unfold tailWord_1238996
  simp only [CollatzResearch.WordTrace]
  refine ⟨22594948309668285257640421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30126597746224380343520561 22594948309668285257640421)
  ·
    refine ⟨4236552808062803485807579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22594948309668285257640421 4236552808062803485807579)
    ·
      refine ⟨6354829212094205228711369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236552808062803485807579 6354829212094205228711369)
      ·
        refine ⟨4766121909070653921533527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6354829212094205228711369 4766121909070653921533527)
        ·
          refine ⟨7149182863605980882300291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766121909070653921533527 7149182863605980882300291)
          ·
            refine ⟨10723774295408971323450437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149182863605980882300291 10723774295408971323450437)
            ·
              refine ⟨2010707680389182123146957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10723774295408971323450437 2010707680389182123146957)
              ·
                refine ⟨754015380145943296180109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2010707680389182123146957 754015380145943296180109)
                ·
                  refine ⟨282755767554728736067541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754015380145943296180109 282755767554728736067541)
                  ·
                    rfl

theorem cell21_1238996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_1238996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1238996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1238996 prefixEnd_1238996 := by exact prefixLift 1238996
  have htrace : WordTrace (prefixWord ++ tailWord_1238996) baseStart_1238996 baseEnd_1238996 := by
    simpa [prefixWord, tailWord_1238996, baseEnd_1238996] using wordTrace_append hprefix tailTrace_1238996
  have hstable : (prefixWord ++ tailWord_1238996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1238996).length < 2 ^ (prefixWord ++ tailWord_1238996).sum := by decide
  have hdescent : baseEnd_1238996 < baseStart_1238996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1238996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239007 : List Nat := [1, 1, 2, 3, 4, 2, 8]
def baseStart_1239007 : Nat := 118140960795 + 1239007 * 2 ^ 59
def prefixEnd_1239007 : Nat := 4983230072969 + 3 ^ 40 * 1239007 * 2
def baseEnd_1239007 : Nat := 31417586433843906820465

theorem tailTrace_1239007 : CollatzResearch.WordTrace tailWord_1239007 prefixEnd_1239007 31417586433843906820465 := by
  unfold tailWord_1239007
  simp only [CollatzResearch.WordTrace]
  refine ⟨45190297822296719393931275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30126865214864479595954183 45190297822296719393931275)
  ·
    refine ⟨67785446733445079090896913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45190297822296719393931275 67785446733445079090896913)
    ·
      refine ⟨50839085050083809318172685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67785446733445079090896913 50839085050083809318172685)
      ·
        refine ⟨19064656893781428494314757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50839085050083809318172685 19064656893781428494314757)
        ·
          refine ⟨3574623167584017842684017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19064656893781428494314757 3574623167584017842684017)
          ·
            refine ⟨2680967375688013382013013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3574623167584017842684017 2680967375688013382013013)
            ·
              refine ⟨31417586433843906820465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2680967375688013382013013 31417586433843906820465)
              ·
                rfl

theorem cell21_1239007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 8].length) (baseStart_1239007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239007 prefixEnd_1239007 := by exact prefixLift 1239007
  have htrace : WordTrace (prefixWord ++ tailWord_1239007) baseStart_1239007 baseEnd_1239007 := by
    simpa [prefixWord, tailWord_1239007, baseEnd_1239007] using wordTrace_append hprefix tailTrace_1239007
  have hstable : (prefixWord ++ tailWord_1239007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239007).length < 2 ^ (prefixWord ++ tailWord_1239007).sum := by decide
  have hdescent : baseEnd_1239007 < baseStart_1239007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239052 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 8]
def baseStart_1239052 : Nat := 118140960795 + 1239052 * 2 ^ 59
def prefixEnd_1239052 : Nat := 4983230072969 + 3 ^ 40 * 1239052 * 2
def baseEnd_1239052 : Nat := 282768547517685083134093

theorem tailTrace_1239052 : CollatzResearch.WordTrace tailWord_1239052 prefixEnd_1239052 282768547517685083134093 := by
  unfold tailWord_1239052
  simp only [CollatzResearch.WordTrace]
  refine ⟨22595969553566846039659705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30127959404755794719546273 22595969553566846039659705)
  ·
    refine ⟨16946977165175134529744779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22595969553566846039659705 16946977165175134529744779)
    ·
      refine ⟨25420465747762701794617169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946977165175134529744779 25420465747762701794617169)
      ·
        refine ⟨19065349310822026345962877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25420465747762701794617169 19065349310822026345962877)
        ·
          refine ⟨7149505991558259879736079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19065349310822026345962877 7149505991558259879736079)
          ·
            refine ⟨10724258987337389819604119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7149505991558259879736079 10724258987337389819604119)
            ·
              refine ⟨16086388481006084729406179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10724258987337389819604119 16086388481006084729406179)
              ·
                refine ⟨24129582721509127094109269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16086388481006084729406179 24129582721509127094109269)
                ·
                  refine ⟨282768547517685083134093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24129582721509127094109269 282768547517685083134093)
                  ·
                    rfl

theorem cell21_1239052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 8].length) (baseStart_1239052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239052 prefixEnd_1239052 := by exact prefixLift 1239052
  have htrace : WordTrace (prefixWord ++ tailWord_1239052) baseStart_1239052 baseEnd_1239052 := by
    simpa [prefixWord, tailWord_1239052, baseEnd_1239052] using wordTrace_append hprefix tailTrace_1239052
  have hstable : (prefixWord ++ tailWord_1239052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239052).length < 2 ^ (prefixWord ++ tailWord_1239052).sum := by decide
  have hdescent : baseEnd_1239052 < baseStart_1239052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239069 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 6]
def baseStart_1239069 : Nat := 118140960795 + 1239069 * 2 ^ 59
def prefixEnd_1239069 : Nat := 4983230072969 + 3 ^ 40 * 1239069 * 2
def baseEnd_1239069 : Nat := 282772427149296831350725

theorem tailTrace_1239069 : CollatzResearch.WordTrace tailWord_1239069 prefixEnd_1239069 282772427149296831350725 := by
  unfold tailWord_1239069
  simp only [CollatzResearch.WordTrace]
  refine ⟨45192559148072103982688261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30128372765381402655125507 45192559148072103982688261)
  ·
    refine ⟨8473604840263519496754049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45192559148072103982688261 8473604840263519496754049)
    ·
      refine ⟨6355203630197639622565537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8473604840263519496754049 6355203630197639622565537)
      ·
        refine ⟨4766402722648229716924153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6355203630197639622565537 4766402722648229716924153)
        ·
          refine ⟨3574802041986172287693115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4766402722648229716924153 3574802041986172287693115)
          ·
            refine ⟨5362203062979258431539673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3574802041986172287693115 5362203062979258431539673)
            ·
              refine ⟨4021652297234443823654755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5362203062979258431539673 4021652297234443823654755)
              ·
                refine ⟨6032478445851665735482133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4021652297234443823654755 6032478445851665735482133)
                ·
                  refine ⟨282772427149296831350725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6032478445851665735482133 282772427149296831350725)
                  ·
                    rfl

theorem cell21_1239069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_1239069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239069 prefixEnd_1239069 := by exact prefixLift 1239069
  have htrace : WordTrace (prefixWord ++ tailWord_1239069) baseStart_1239069 baseEnd_1239069 := by
    simpa [prefixWord, tailWord_1239069, baseEnd_1239069] using wordTrace_append hprefix tailTrace_1239069
  have hstable : (prefixWord ++ tailWord_1239069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239069).length < 2 ^ (prefixWord ++ tailWord_1239069).sum := by decide
  have hdescent : baseEnd_1239069 < baseStart_1239069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239086 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_1239086 : Nat := 118140960795 + 1239086 * 2 ^ 59
def prefixEnd_1239086 : Nat := 4983230072969 + 3 ^ 40 * 1239086 * 2
def baseEnd_1239086 : Nat := 282776306780908579567357

theorem tailTrace_1239086 : CollatzResearch.WordTrace tailWord_1239086 prefixEnd_1239086 282776306780908579567357 := by
  unfold tailWord_1239086
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649147398626314485757139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30128786126007010590704741 5649147398626314485757139)
  ·
    refine ⟨8473721097939471728635709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5649147398626314485757139 8473721097939471728635709)
    ·
      refine ⟨3177645411727301898238391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8473721097939471728635709 3177645411727301898238391)
      ·
        refine ⟨4766468117590952847357587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177645411727301898238391 4766468117590952847357587)
        ·
          refine ⟨7149702176386429271036381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4766468117590952847357587 7149702176386429271036381)
          ·
            refine ⟨2681138316144910976638643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7149702176386429271036381 2681138316144910976638643)
            ·
              refine ⟨4021707474217366464957965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681138316144910976638643 4021707474217366464957965)
              ·
                refine ⟨1508140302831512424359237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4021707474217366464957965 1508140302831512424359237)
                ·
                  refine ⟨282776306780908579567357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508140302831512424359237 282776306780908579567357)
                  ·
                    rfl

theorem cell21_1239086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_1239086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239086 prefixEnd_1239086 := by exact prefixLift 1239086
  have htrace : WordTrace (prefixWord ++ tailWord_1239086) baseStart_1239086 baseEnd_1239086 := by
    simpa [prefixWord, tailWord_1239086, baseEnd_1239086] using wordTrace_append hprefix tailTrace_1239086
  have hstable : (prefixWord ++ tailWord_1239086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239086).length < 2 ^ (prefixWord ++ tailWord_1239086).sum := by decide
  have hdescent : baseEnd_1239086 < baseStart_1239086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239210 : List Nat := [3, 1, 5, 1, 2, 2, 2, 5]
def baseStart_1239210 : Nat := 118140960795 + 1239210 * 2 ^ 59
def prefixEnd_1239210 : Nat := 4983230072969 + 3 ^ 40 * 1239210 * 2
def baseEnd_1239210 : Nat := 94268201756770639833479

theorem tailTrace_1239210 : CollatzResearch.WordTrace tailWord_1239210 prefixEnd_1239210 94268201756770639833479 := by
  unfold tailWord_1239210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299425460140321265892771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30131801227040856709047389 11299425460140321265892771)
  ·
    refine ⟨16949138190210481898839157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11299425460140321265892771 16949138190210481898839157)
    ·
      refine ⟨1588981705332232678016171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16949138190210481898839157 1588981705332232678016171)
      ·
        refine ⟨2383472557998349017024257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588981705332232678016171 2383472557998349017024257)
        ·
          refine ⟨1787604418498761762768193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2383472557998349017024257 1787604418498761762768193)
          ·
            refine ⟨1340703313874071322076145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787604418498761762768193 1340703313874071322076145)
            ·
              refine ⟨1005527485405553491557109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1340703313874071322076145 1005527485405553491557109)
              ·
                refine ⟨94268201756770639833479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1005527485405553491557109 94268201756770639833479)
                ·
                  rfl

theorem cell21_1239210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 2, 5].length) (baseStart_1239210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239210 prefixEnd_1239210 := by exact prefixLift 1239210
  have htrace : WordTrace (prefixWord ++ tailWord_1239210) baseStart_1239210 baseEnd_1239210 := by
    simpa [prefixWord, tailWord_1239210, baseEnd_1239210] using wordTrace_append hprefix tailTrace_1239210
  have hstable : (prefixWord ++ tailWord_1239210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239210).length < 2 ^ (prefixWord ++ tailWord_1239210).sum := by decide
  have hdescent : baseEnd_1239210 < baseStart_1239210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239297 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 4]
def baseStart_1239297 : Nat := 118140960795 + 1239297 * 2 ^ 59
def prefixEnd_1239297 : Nat := 4983230072969 + 3 ^ 40 * 1239297 * 2
def baseEnd_1239297 : Nat := 282824459855619101550259

theorem tailTrace_1239297 : CollatzResearch.WordTrace tailWord_1239297 prefixEnd_1239297 282824459855619101550259 := by
  unfold tailWord_1239297
  simp only [CollatzResearch.WordTrace]
  refine ⟨45200874991246098921988145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30133916660830732614658763 45200874991246098921988145)
  ·
    refine ⟨33900656243434574191491109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45200874991246098921988145 33900656243434574191491109)
    ·
      refine ⟨6356373045643982660904583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33900656243434574191491109 6356373045643982660904583)
      ·
        refine ⟨9534559568465973991356875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6356373045643982660904583 9534559568465973991356875)
        ·
          refine ⟨14301839352698960987035313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9534559568465973991356875 14301839352698960987035313)
          ·
            refine ⟨10726379514524220740276485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14301839352698960987035313 10726379514524220740276485)
            ·
              refine ⟨2011196158973291388801841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10726379514524220740276485 2011196158973291388801841)
              ·
                refine ⟨1508397119229968541601381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011196158973291388801841 1508397119229968541601381)
                ·
                  refine ⟨282824459855619101550259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508397119229968541601381 282824459855619101550259)
                  ·
                    rfl

theorem cell21_1239297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 4].length) (baseStart_1239297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239297 prefixEnd_1239297 := by exact prefixLift 1239297
  have htrace : WordTrace (prefixWord ++ tailWord_1239297) baseStart_1239297 baseEnd_1239297 := by
    simpa [prefixWord, tailWord_1239297, baseEnd_1239297] using wordTrace_append hprefix tailTrace_1239297
  have hstable : (prefixWord ++ tailWord_1239297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239297).length < 2 ^ (prefixWord ++ tailWord_1239297).sum := by decide
  have hdescent : baseEnd_1239297 < baseStart_1239297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239300 : List Nat := [2, 3, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1239300 : Nat := 118140960795 + 1239300 * 2 ^ 59
def prefixEnd_1239300 : Nat := 4983230072969 + 3 ^ 40 * 1239300 * 2
def baseEnd_1239300 : Nat := 282825144496491763000253

theorem tailTrace_1239300 : CollatzResearch.WordTrace tailWord_1239300 prefixEnd_1239300 282825144496491763000253 := by
  unfold tailWord_1239300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22600492205117615217173677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30133989606823486956231569 22600492205117615217173677)
  ·
    refine ⟨8475184576919105706440129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22600492205117615217173677 8475184576919105706440129)
    ·
      refine ⟨6356388432689329279830097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8475184576919105706440129 6356388432689329279830097)
      ·
        refine ⟨4767291324516996959872573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6356388432689329279830097 4767291324516996959872573)
        ·
          refine ⟨1787734246693873859952215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4767291324516996959872573 1787734246693873859952215)
          ·
            refine ⟨2681601370040810789928323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787734246693873859952215 2681601370040810789928323)
            ·
              refine ⟨4022402055061216184892485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681601370040810789928323 4022402055061216184892485)
              ·
                refine ⟨754200385323978034667341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4022402055061216184892485 754200385323978034667341)
                ·
                  refine ⟨282825144496491763000253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754200385323978034667341 282825144496491763000253)
                  ·
                    rfl

theorem cell21_1239300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1239300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239300 prefixEnd_1239300 := by exact prefixLift 1239300
  have htrace : WordTrace (prefixWord ++ tailWord_1239300) baseStart_1239300 baseEnd_1239300 := by
    simpa [prefixWord, tailWord_1239300, baseEnd_1239300] using wordTrace_append hprefix tailTrace_1239300
  have hstable : (prefixWord ++ tailWord_1239300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239300).length < 2 ^ (prefixWord ++ tailWord_1239300).sum := by decide
  have hdescent : baseEnd_1239300 < baseStart_1239300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239328 : List Nat := [2, 1, 1, 5, 2, 2, 3, 5]
def baseStart_1239328 : Nat := 118140960795 + 1239328 * 2 ^ 59
def prefixEnd_1239328 : Nat := 4983230072969 + 3 ^ 40 * 1239328 * 2
def baseEnd_1239328 : Nat := 94277178159323312177843

theorem tailTrace_1239328 : CollatzResearch.WordTrace tailWord_1239328 prefixEnd_1239328 94277178159323312177843 := by
  unfold tailWord_1239328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601002827066895608183319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30134670436089194144244425 22601002827066895608183319)
  ·
    refine ⟨33901504240600343412274979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22601002827066895608183319 33901504240600343412274979)
    ·
      refine ⟨50852256360900515118412469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33901504240600343412274979 50852256360900515118412469)
      ·
        refine ⟨4767399033834423292351169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50852256360900515118412469 4767399033834423292351169)
        ·
          refine ⟨3575549275375817469263377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4767399033834423292351169 3575549275375817469263377)
          ·
            refine ⟨2681661956531863101947533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3575549275375817469263377 2681661956531863101947533)
            ·
              refine ⟨1005623233699448663230325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2681661956531863101947533 1005623233699448663230325)
              ·
                refine ⟨94277178159323312177843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1005623233699448663230325 94277178159323312177843)
                ·
                  rfl

theorem cell21_1239328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3, 5].length) (baseStart_1239328 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239328 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239328 prefixEnd_1239328 := by exact prefixLift 1239328
  have htrace : WordTrace (prefixWord ++ tailWord_1239328) baseStart_1239328 baseEnd_1239328 := by
    simpa [prefixWord, tailWord_1239328, baseEnd_1239328] using wordTrace_append hprefix tailTrace_1239328
  have hstable : (prefixWord ++ tailWord_1239328).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239328).length < 2 ^ (prefixWord ++ tailWord_1239328).sum := by decide
  have hdescent : baseEnd_1239328 < baseStart_1239328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239356 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_1239356 : Nat := 118140960795 + 1239356 * 2 ^ 59
def prefixEnd_1239356 : Nat := 4983230072969 + 3 ^ 40 * 1239356 * 2
def baseEnd_1239356 : Nat := 282837924459448110066805

theorem tailTrace_1239356 : CollatzResearch.WordTrace tailWord_1239356 prefixEnd_1239356 282837924459448110066805 := by
  unfold tailWord_1239356
  simp only [CollatzResearch.WordTrace]
  refine ⟨22601513449016175999192961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30135351265354901332257281 22601513449016175999192961)
  ·
    refine ⟨16951135086762131999394721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22601513449016175999192961 16951135086762131999394721)
    ·
      refine ⟨12713351315071598999546041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16951135086762131999394721 12713351315071598999546041)
      ·
        refine ⟨9535013486303699249659531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12713351315071598999546041 9535013486303699249659531)
        ·
          refine ⟨14302520229455548874489297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9535013486303699249659531 14302520229455548874489297)
          ·
            refine ⟨10726890172091661655866973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14302520229455548874489297 10726890172091661655866973)
            ·
              refine ⟨4022583814534373120950115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10726890172091661655866973 4022583814534373120950115)
              ·
                refine ⟨6033875721801559681425173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4022583814534373120950115 6033875721801559681425173)
                ·
                  refine ⟨282837924459448110066805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6033875721801559681425173 282837924459448110066805)
                  ·
                    rfl

theorem cell21_1239356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_1239356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239356 prefixEnd_1239356 := by exact prefixLift 1239356
  have htrace : WordTrace (prefixWord ++ tailWord_1239356) baseStart_1239356 baseEnd_1239356 := by
    simpa [prefixWord, tailWord_1239356, baseEnd_1239356] using wordTrace_append hprefix tailTrace_1239356
  have hstable : (prefixWord ++ tailWord_1239356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239356).length < 2 ^ (prefixWord ++ tailWord_1239356).sum := by decide
  have hdescent : baseEnd_1239356 < baseStart_1239356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239404 : List Nat := [2, 2, 1, 1, 7, 1, 7]
def baseStart_1239404 : Nat := 118140960795 + 1239404 * 2 ^ 59
def prefixEnd_1239404 : Nat := 4983230072969 + 3 ^ 40 * 1239404 * 2
def baseEnd_1239404 : Nat := 31427653190378965918523

theorem tailTrace_1239404 : CollatzResearch.WordTrace tailWord_1239404 prefixEnd_1239404 31427653190378965918523 := by
  unfold tailWord_1239404
  simp only [CollatzResearch.WordTrace]
  refine ⟨22602388800929228098066633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30136518401238970797422177 22602388800929228098066633)
  ·
    refine ⟨16951791600696921073549975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22602388800929228098066633 16951791600696921073549975)
    ·
      refine ⟨25427687401045381610324963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16951791600696921073549975 25427687401045381610324963)
      ·
        refine ⟨38141531101568072415487445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25427687401045381610324963 38141531101568072415487445)
        ·
          refine ⟨893942135193001697237987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38141531101568072415487445 893942135193001697237987)
          ·
            refine ⟨1340913202789502545856981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893942135193001697237987 1340913202789502545856981)
            ·
              refine ⟨31427653190378965918523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1340913202789502545856981 31427653190378965918523)
              ·
                rfl

theorem cell21_1239404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 7].length) (baseStart_1239404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239404 prefixEnd_1239404 := by exact prefixLift 1239404
  have htrace : WordTrace (prefixWord ++ tailWord_1239404) baseStart_1239404 baseEnd_1239404 := by
    simpa [prefixWord, tailWord_1239404, baseEnd_1239404] using wordTrace_append hprefix tailTrace_1239404
  have hstable : (prefixWord ++ tailWord_1239404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239404).length < 2 ^ (prefixWord ++ tailWord_1239404).sum := by decide
  have hdescent : baseEnd_1239404 < baseStart_1239404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239491 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_1239491 : Nat := 118140960795 + 1239491 * 2 ^ 59
def prefixEnd_1239491 : Nat := 4983230072969 + 3 ^ 40 * 1239491 * 2
def baseEnd_1239491 : Nat := 282868733298717875316529

theorem tailTrace_1239491 : CollatzResearch.WordTrace tailWord_1239491 prefixEnd_1239491 282868733298717875316529 := by
  unfold tailWord_1239491
  simp only [CollatzResearch.WordTrace]
  refine ⟨45207950752543270054550327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30138633835028846703033551 45207950752543270054550327)
  ·
    refine ⟨67811926128814905081825491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45207950752543270054550327 67811926128814905081825491)
    ·
      refine ⟨101717889193222357622738237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67811926128814905081825491 101717889193222357622738237)
      ·
        refine ⟨38144208447458384108526839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101717889193222357622738237 38144208447458384108526839)
        ·
          refine ⟨57216312671187576162790259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38144208447458384108526839 57216312671187576162790259)
          ·
            refine ⟨85824469006781364244185389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57216312671187576162790259 85824469006781364244185389)
            ·
              refine ⟨32184175877543011591569521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85824469006781364244185389 32184175877543011591569521)
              ·
                refine ⟨24138131908157258693677141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32184175877543011591569521 24138131908157258693677141)
                ·
                  refine ⟨282868733298717875316529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24138131908157258693677141 282868733298717875316529)
                  ·
                    rfl

theorem cell21_1239491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_1239491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239491 prefixEnd_1239491 := by exact prefixLift 1239491
  have htrace : WordTrace (prefixWord ++ tailWord_1239491) baseStart_1239491 baseEnd_1239491 := by
    simpa [prefixWord, tailWord_1239491, baseEnd_1239491] using wordTrace_append hprefix tailTrace_1239491
  have hstable : (prefixWord ++ tailWord_1239491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239491).length < 2 ^ (prefixWord ++ tailWord_1239491).sum := by decide
  have hdescent : baseEnd_1239491 < baseStart_1239491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239525 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 6]
def baseStart_1239525 : Nat := 118140960795 + 1239525 * 2 ^ 59
def prefixEnd_1239525 : Nat := 4983230072969 + 3 ^ 40 * 1239525 * 2
def baseEnd_1239525 : Nat := 282876492561941371749793

theorem tailTrace_1239525 : CollatzResearch.WordTrace tailWord_1239525 prefixEnd_1239525 282876492561941371749793 := by
  unfold tailWord_1239525
  simp only [CollatzResearch.WordTrace]
  refine ⟨45209190834420093861288029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30139460556280062574192019 45209190834420093861288029)
  ·
    refine ⟨16953446562907535197983011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45209190834420093861288029 16953446562907535197983011)
    ·
      refine ⟨25430169844361302796974517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16953446562907535197983011 25430169844361302796974517)
      ·
        refine ⟨2384078422908872137216361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25430169844361302796974517 2384078422908872137216361)
        ·
          refine ⟨1788058817181654102912271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384078422908872137216361 1788058817181654102912271)
          ·
            refine ⟨2682088225772481154368407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1788058817181654102912271 2682088225772481154368407)
            ·
              refine ⟨4023132338658721731552611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682088225772481154368407 4023132338658721731552611)
              ·
                refine ⟨6034698507988082597328917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4023132338658721731552611 6034698507988082597328917)
                ·
                  refine ⟨282876492561941371749793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6034698507988082597328917 282876492561941371749793)
                  ·
                    rfl

theorem cell21_1239525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_1239525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239525 prefixEnd_1239525 := by exact prefixLift 1239525
  have htrace : WordTrace (prefixWord ++ tailWord_1239525) baseStart_1239525 baseEnd_1239525 := by
    simpa [prefixWord, tailWord_1239525, baseEnd_1239525] using wordTrace_append hprefix tailTrace_1239525
  have hstable : (prefixWord ++ tailWord_1239525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239525).length < 2 ^ (prefixWord ++ tailWord_1239525).sum := by decide
  have hdescent : baseEnd_1239525 < baseStart_1239525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239542 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_1239542 : Nat := 118140960795 + 1239542 * 2 ^ 59
def prefixEnd_1239542 : Nat := 4983230072969 + 3 ^ 40 * 1239542 * 2
def baseEnd_1239542 : Nat := 282880372193553119966425

theorem tailTrace_1239542 : CollatzResearch.WordTrace tailWord_1239542 prefixEnd_1239542 282880372193553119966425 := by
  unfold tailWord_1239542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2825613179709906610291055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30139873916905670509771253 2825613179709906610291055)
  ·
    refine ⟨4238419769564859915436583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2825613179709906610291055 4238419769564859915436583)
    ·
      refine ⟨6357629654347289873154875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4238419769564859915436583 6357629654347289873154875)
      ·
        refine ⟨9536444481520934809732313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6357629654347289873154875 9536444481520934809732313)
        ·
          refine ⟨7152333361140701107299235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9536444481520934809732313 7152333361140701107299235)
          ·
            refine ⟨10728500041711051660948853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7152333361140701107299235 10728500041711051660948853)
            ·
              refine ⟨1005796878910411093213955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10728500041711051660948853 1005796878910411093213955)
              ·
                refine ⟨1508695318365616639820933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005796878910411093213955 1508695318365616639820933)
                ·
                  refine ⟨282880372193553119966425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508695318365616639820933 282880372193553119966425)
                  ·
                    rfl

theorem cell21_1239542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_1239542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239542 prefixEnd_1239542 := by exact prefixLift 1239542
  have htrace : WordTrace (prefixWord ++ tailWord_1239542) baseStart_1239542 baseEnd_1239542 := by
    simpa [prefixWord, tailWord_1239542, baseEnd_1239542] using wordTrace_append hprefix tailTrace_1239542
  have hstable : (prefixWord ++ tailWord_1239542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239542).length < 2 ^ (prefixWord ++ tailWord_1239542).sum := by decide
  have hdescent : baseEnd_1239542 < baseStart_1239542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239556 : List Nat := [2, 3, 2, 3, 1, 1, 4, 5]
def baseStart_1239556 : Nat := 118140960795 + 1239556 * 2 ^ 59
def prefixEnd_1239556 : Nat := 4983230072969 + 3 ^ 40 * 1239556 * 2
def baseEnd_1239556 : Nat := 94294522394764068911021

theorem tailTrace_1239556 : CollatzResearch.WordTrace tailWord_1239556 prefixEnd_1239556 94294522394764068911021 := by
  unfold tailWord_1239556
  simp only [CollatzResearch.WordTrace]
  refine ⟨22605160748653893077833261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30140214331538524103777681 22605160748653893077833261)
  ·
    refine ⟨8476935280745209904187473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22605160748653893077833261 8476935280745209904187473)
    ·
      refine ⟨6357701460558907428140605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8476935280745209904187473 6357701460558907428140605)
      ·
        refine ⟨2384138047709590285552727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6357701460558907428140605 2384138047709590285552727)
        ·
          refine ⟨3576207071564385428329091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384138047709590285552727 3576207071564385428329091)
          ·
            refine ⟨5364310607346578142493637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576207071564385428329091 5364310607346578142493637)
            ·
              refine ⟨1005808238877483401717557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5364310607346578142493637 1005808238877483401717557)
              ·
                refine ⟨94294522394764068911021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1005808238877483401717557 94294522394764068911021)
                ·
                  rfl

theorem cell21_1239556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 5].length) (baseStart_1239556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239556 prefixEnd_1239556 := by exact prefixLift 1239556
  have htrace : WordTrace (prefixWord ++ tailWord_1239556) baseStart_1239556 baseEnd_1239556 := by
    simpa [prefixWord, tailWord_1239556, baseEnd_1239556] using wordTrace_append hprefix tailTrace_1239556
  have hstable : (prefixWord ++ tailWord_1239556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239556).length < 2 ^ (prefixWord ++ tailWord_1239556).sum := by decide
  have hdescent : baseEnd_1239556 < baseStart_1239556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239567 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 6]
def baseStart_1239567 : Nat := 118140960795 + 1239567 * 2 ^ 59
def prefixEnd_1239567 : Nat := 4983230072969 + 3 ^ 40 * 1239567 * 2
def baseEnd_1239567 : Nat := 282886077534158632049707

theorem tailTrace_1239567 : CollatzResearch.WordTrace tailWord_1239567 prefixEnd_1239567 282886077534158632049707 := by
  unfold tailWord_1239567
  simp only [CollatzResearch.WordTrace]
  refine ⟨45210722700267935034316955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30140481800178623356211303 45210722700267935034316955)
  ·
    refine ⟨67816084050401902551475433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45210722700267935034316955 67816084050401902551475433)
    ·
      refine ⟨50862063037801426913606575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67816084050401902551475433 50862063037801426913606575)
      ·
        refine ⟨76293094556702140370409863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50862063037801426913606575 76293094556702140370409863)
        ·
          refine ⟨114439641835053210555614795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76293094556702140370409863 114439641835053210555614795)
          ·
            refine ⟨171659462752579815833422193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114439641835053210555614795 171659462752579815833422193)
            ·
              refine ⟨128744597064434861875066645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171659462752579815833422193 128744597064434861875066645)
              ·
                refine ⟨6034902987395384150393749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128744597064434861875066645 6034902987395384150393749)
                ·
                  refine ⟨282886077534158632049707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6034902987395384150393749 282886077534158632049707)
                  ·
                    rfl

theorem cell21_1239567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_1239567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239567 prefixEnd_1239567 := by exact prefixLift 1239567
  have htrace : WordTrace (prefixWord ++ tailWord_1239567) baseStart_1239567 baseEnd_1239567 := by
    simpa [prefixWord, tailWord_1239567, baseEnd_1239567] using wordTrace_append hprefix tailTrace_1239567
  have hstable : (prefixWord ++ tailWord_1239567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239567).length < 2 ^ (prefixWord ++ tailWord_1239567).sum := by decide
  have hdescent : baseEnd_1239567 < baseStart_1239567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239601 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 4]
def baseStart_1239601 : Nat := 118140960795 + 1239601 * 2 ^ 59
def prefixEnd_1239601 : Nat := 4983230072969 + 3 ^ 40 * 1239601 * 2
def baseEnd_1239601 : Nat := 282893836797382128482971

theorem tailTrace_1239601 : CollatzResearch.WordTrace tailWord_1239601 prefixEnd_1239601 282893836797382128482971 := by
  unfold tailWord_1239601
  simp only [CollatzResearch.WordTrace]
  refine ⟨45211962782144758841054657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30141308521429839227369771 45211962782144758841054657)
  ·
    refine ⟨33908972086608569130790993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45211962782144758841054657 33908972086608569130790993)
    ·
      refine ⟨25431729064956426848093245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33908972086608569130790993 25431729064956426848093245)
      ·
        refine ⟨9536898399358660068034967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25431729064956426848093245 9536898399358660068034967)
        ·
          refine ⟨14305347599037990102052451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9536898399358660068034967 14305347599037990102052451)
          ·
            refine ⟨21458021398556985153078677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14305347599037990102052451 21458021398556985153078677)
            ·
              refine ⟨1005844753057358679050563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21458021398556985153078677 1005844753057358679050563)
              ·
                refine ⟨1508767129586038018575845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1005844753057358679050563 1508767129586038018575845)
                ·
                  refine ⟨282893836797382128482971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508767129586038018575845 282893836797382128482971)
                  ·
                    rfl

theorem cell21_1239601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_1239601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239601 prefixEnd_1239601 := by exact prefixLift 1239601
  have htrace : WordTrace (prefixWord ++ tailWord_1239601) baseStart_1239601 baseEnd_1239601 := by
    simpa [prefixWord, tailWord_1239601, baseEnd_1239601] using wordTrace_append hprefix tailTrace_1239601
  have hstable : (prefixWord ++ tailWord_1239601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239601).length < 2 ^ (prefixWord ++ tailWord_1239601).sum := by decide
  have hdescent : baseEnd_1239601 < baseStart_1239601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239660 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 4]
def baseStart_1239660 : Nat := 118140960795 + 1239660 * 2 ^ 59
def prefixEnd_1239660 : Nat := 4983230072969 + 3 ^ 40 * 1239660 * 2
def baseEnd_1239660 : Nat := 282907301401211136999517

theorem tailTrace_1239660 : CollatzResearch.WordTrace tailWord_1239660 prefixEnd_1239660 282907301401211136999517 := by
  unfold tailWord_1239660
  simp only [CollatzResearch.WordTrace]
  refine ⟨22607057344465505958726217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30142743125954007944968289 22607057344465505958726217)
  ·
    refine ⟨16955293008349129469044663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22607057344465505958726217 16955293008349129469044663)
    ·
      refine ⟨25432939512523694203566995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16955293008349129469044663 25432939512523694203566995)
      ·
        refine ⟨38149409268785541305350493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25432939512523694203566995 38149409268785541305350493)
        ·
          refine ⟨14306028475794577989506435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38149409268785541305350493 14306028475794577989506435)
          ·
            refine ⟨21459042713691866984259653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14306028475794577989506435 21459042713691866984259653)
            ·
              refine ⟨4023570508817225059548685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21459042713691866984259653 4023570508817225059548685)
              ·
                refine ⟨1508838940806459397330757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4023570508817225059548685 1508838940806459397330757)
                ·
                  refine ⟨282907301401211136999517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1508838940806459397330757 282907301401211136999517)
                  ·
                    rfl

theorem cell21_1239660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_1239660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239660 prefixEnd_1239660 := by exact prefixLift 1239660
  have htrace : WordTrace (prefixWord ++ tailWord_1239660) baseStart_1239660 baseEnd_1239660 := by
    simpa [prefixWord, tailWord_1239660, baseEnd_1239660] using wordTrace_append hprefix tailTrace_1239660
  have hstable : (prefixWord ++ tailWord_1239660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239660).length < 2 ^ (prefixWord ++ tailWord_1239660).sum := by decide
  have hdescent : baseEnd_1239660 < baseStart_1239660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239705 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 5]
def baseStart_1239705 : Nat := 118140960795 + 1239705 * 2 ^ 59
def prefixEnd_1239705 : Nat := 4983230072969 + 3 ^ 40 * 1239705 * 2
def baseEnd_1239705 : Nat := 282917571014301058749425

theorem tailTrace_1239705 : CollatzResearch.WordTrace tailWord_1239705 prefixEnd_1239705 282917571014301058749425 := by
  unfold tailWord_1239705
  simp only [CollatzResearch.WordTrace]
  refine ⟨45215755973767984602840569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30143837315845323068560379 45215755973767984602840569)
  ·
    refine ⟨33911816980325988452130427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45215755973767984602840569 33911816980325988452130427)
    ·
      refine ⟨50867725470488982678195641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33911816980325988452130427 50867725470488982678195641)
      ·
        refine ⟨38150794102866737008646731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50867725470488982678195641 38150794102866737008646731)
        ·
          refine ⟨57226191154300105512970097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38150794102866737008646731 57226191154300105512970097)
          ·
            refine ⟨42919643365725079134727573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57226191154300105512970097 42919643365725079134727573)
            ·
              refine ⟨2011858282768363084440355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42919643365725079134727573 2011858282768363084440355)
              ·
                refine ⟨3017787424152544626660533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2011858282768363084440355 3017787424152544626660533)
                ·
                  refine ⟨282917571014301058749425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3017787424152544626660533 282917571014301058749425)
                  ·
                    rfl

theorem cell21_1239705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 5].length) (baseStart_1239705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239705 prefixEnd_1239705 := by exact prefixLift 1239705
  have htrace : WordTrace (prefixWord ++ tailWord_1239705) baseStart_1239705 baseEnd_1239705 := by
    simpa [prefixWord, tailWord_1239705, baseEnd_1239705] using wordTrace_append hprefix tailTrace_1239705
  have hstable : (prefixWord ++ tailWord_1239705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239705).length < 2 ^ (prefixWord ++ tailWord_1239705).sum := by decide
  have hdescent : baseEnd_1239705 < baseStart_1239705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239756 : List Nat := [2, 2, 1, 5, 1, 2, 3, 2, 3]
def baseStart_1239756 : Nat := 118140960795 + 1239756 * 2 ^ 59
def prefixEnd_1239756 : Nat := 4983230072969 + 3 ^ 40 * 1239756 * 2
def baseEnd_1239756 : Nat := 282929209909136303399321

theorem tailTrace_1239756 : CollatzResearch.WordTrace tailWord_1239756 prefixEnd_1239756 282929209909136303399321 := by
  unfold tailWord_1239756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22608808048291610156473561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30145077397722146875298081 22608808048291610156473561)
  ·
    refine ⟨16956606036218707617355171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22608808048291610156473561 16956606036218707617355171)
    ·
      refine ⟨25434909054328061426032757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16956606036218707617355171 25434909054328061426032757)
      ·
        refine ⟨2384522723843255758690571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25434909054328061426032757 2384522723843255758690571)
        ·
          refine ⟨3576784085764883638035857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384522723843255758690571 3576784085764883638035857)
          ·
            refine ⟨2682588064323662728526893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576784085764883638035857 2682588064323662728526893)
            ·
              refine ⟨1005970524121373523197585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2682588064323662728526893 1005970524121373523197585)
              ·
                refine ⟨754477893091030142398189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1005970524121373523197585 754477893091030142398189)
                ·
                  refine ⟨282929209909136303399321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754477893091030142398189 282929209909136303399321)
                  ·
                    rfl

theorem cell21_1239756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 3, 2, 3].length) (baseStart_1239756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239756 prefixEnd_1239756 := by exact prefixLift 1239756
  have htrace : WordTrace (prefixWord ++ tailWord_1239756) baseStart_1239756 baseEnd_1239756 := by
    simpa [prefixWord, tailWord_1239756, baseEnd_1239756] using wordTrace_append hprefix tailTrace_1239756
  have hstable : (prefixWord ++ tailWord_1239756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239756).length < 2 ^ (prefixWord ++ tailWord_1239756).sum := by decide
  have hdescent : baseEnd_1239756 < baseStart_1239756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239815 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 3]
def baseStart_1239815 : Nat := 118140960795 + 1239815 * 2 ^ 59
def prefixEnd_1239815 : Nat := 4983230072969 + 3 ^ 40 * 1239815 * 2
def baseEnd_1239815 : Nat := 282942674512965311915867

theorem tailTrace_1239815 : CollatzResearch.WordTrace tailWord_1239815 prefixEnd_1239815 282942674512965311915867 := by
  unfold tailWord_1239815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45219768003369473389344899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30146512002246315592896599 45219768003369473389344899)
  ·
    refine ⟨67829652005054210084017349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45219768003369473389344899 67829652005054210084017349)
    ·
      refine ⟨12718059750947664390753253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67829652005054210084017349 12718059750947664390753253)
      ·
        refine ⟨2384636203302687073266235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12718059750947664390753253 2384636203302687073266235)
        ·
          refine ⟨3576954304954030609899353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384636203302687073266235 3576954304954030609899353)
          ·
            refine ⟨2682715728715522957424515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3576954304954030609899353 2682715728715522957424515)
            ·
              refine ⟨4024073593073284436136773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2682715728715522957424515 4024073593073284436136773)
              ·
                refine ⟨754513798701240831775645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4024073593073284436136773 754513798701240831775645)
                ·
                  refine ⟨282942674512965311915867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754513798701240831775645 282942674512965311915867)
                  ·
                    rfl

theorem cell21_1239815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].length) (baseStart_1239815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239815 prefixEnd_1239815 := by exact prefixLift 1239815
  have htrace : WordTrace (prefixWord ++ tailWord_1239815) baseStart_1239815 baseEnd_1239815 := by
    simpa [prefixWord, tailWord_1239815, baseEnd_1239815] using wordTrace_append hprefix tailTrace_1239815
  have hstable : (prefixWord ++ tailWord_1239815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239815).length < 2 ^ (prefixWord ++ tailWord_1239815).sum := by decide
  have hdescent : baseEnd_1239815 < baseStart_1239815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1239933 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 5]
def baseStart_1239933 : Nat := 118140960795 + 1239933 * 2 ^ 59
def prefixEnd_1239933 : Nat := 4983230072969 + 3 ^ 40 * 1239933 * 2
def baseEnd_1239933 : Nat := 282969603720623328948959

theorem tailTrace_1239933 : CollatzResearch.WordTrace tailWord_1239933 prefixEnd_1239933 282969603720623328948959 := by
  unfold tailWord_1239933
  simp only [CollatzResearch.WordTrace]
  refine ⟨45224071816941979542140453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30149381211294653028093635 45224071816941979542140453)
  ·
    refine ⟨8479513465676621164151335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45224071816941979542140453 8479513465676621164151335)
    ·
      refine ⟨12719270198514931746227003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8479513465676621164151335 12719270198514931746227003)
      ·
        refine ⟨19078905297772397619340505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719270198514931746227003 19078905297772397619340505)
        ·
          refine ⟨14309178973329298214505379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19078905297772397619340505 14309178973329298214505379)
          ·
            refine ⟨21463768459993947321758069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14309178973329298214505379 21463768459993947321758069)
            ·
              refine ⟨2012228293124432561414819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21463768459993947321758069 2012228293124432561414819)
              ·
                refine ⟨3018342439686648842122229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2012228293124432561414819 3018342439686648842122229)
                ·
                  refine ⟨282969603720623328948959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3018342439686648842122229 282969603720623328948959)
                  ·
                    rfl

theorem cell21_1239933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_1239933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1239933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1239933 prefixEnd_1239933 := by exact prefixLift 1239933
  have htrace : WordTrace (prefixWord ++ tailWord_1239933) baseStart_1239933 baseEnd_1239933 := by
    simpa [prefixWord, tailWord_1239933, baseEnd_1239933] using wordTrace_append hprefix tailTrace_1239933
  have hstable : (prefixWord ++ tailWord_1239933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1239933).length < 2 ^ (prefixWord ++ tailWord_1239933).sum := by decide
  have hdescent : baseEnd_1239933 < baseStart_1239933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1239933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240026 : List Nat := [3, 1, 1, 2, 4, 1, 1, 5, 3]
def baseStart_1240026 : Nat := 118140960795 + 1240026 * 2 ^ 59
def prefixEnd_1240026 : Nat := 4983230072969 + 3 ^ 40 * 1240026 * 2
def baseEnd_1240026 : Nat := 282990827587675833898769

theorem tailTrace_1240026 : CollatzResearch.WordTrace tailWord_1240026 prefixEnd_1240026 282990827587675833898769 := by
  unfold tailWord_1240026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306865951401264106318983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30151642537070037616850621 11306865951401264106318983)
  ·
    refine ⟨16960298927101896159478475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11306865951401264106318983 16960298927101896159478475)
    ·
      refine ⟨25440448390652844239217713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16960298927101896159478475 25440448390652844239217713)
      ·
        refine ⟨19080336292989633179413285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25440448390652844239217713 19080336292989633179413285)
        ·
          refine ⟨3577563054935556221139991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19080336292989633179413285 3577563054935556221139991)
          ·
            refine ⟨5366344582403334331709987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3577563054935556221139991 5366344582403334331709987)
            ·
              refine ⟨8049516873605001497564981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5366344582403334331709987 8049516873605001497564981)
              ·
                refine ⟨754642206900468890396717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8049516873605001497564981 754642206900468890396717)
                ·
                  refine ⟨282990827587675833898769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754642206900468890396717 282990827587675833898769)
                  ·
                    rfl

theorem cell21_1240026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 5, 3].length) (baseStart_1240026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240026 prefixEnd_1240026 := by exact prefixLift 1240026
  have htrace : WordTrace (prefixWord ++ tailWord_1240026) baseStart_1240026 baseEnd_1240026 := by
    simpa [prefixWord, tailWord_1240026, baseEnd_1240026] using wordTrace_append hprefix tailTrace_1240026
  have hstable : (prefixWord ++ tailWord_1240026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240026).length < 2 ^ (prefixWord ++ tailWord_1240026).sum := by decide
  have hdescent : baseEnd_1240026 < baseStart_1240026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240040 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_1240040 : Nat := 118140960795 + 1240040 * 2 ^ 59
def prefixEnd_1240040 : Nat := 4983230072969 + 3 ^ 40 * 1240040 * 2
def baseEnd_1240040 : Nat := 282994022578414920665407

theorem tailTrace_1240040 : CollatzResearch.WordTrace tailWord_1240040 prefixEnd_1240040 282994022578414920665407 := by
  unfold tailWord_1240040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22613987213777168408142787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30151982951702891210857049 22613987213777168408142787)
  ·
    refine ⟨33920980820665752612214181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22613987213777168408142787 33920980820665752612214181)
    ·
      refine ⟨6360183903874828614790159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33920980820665752612214181 6360183903874828614790159)
      ·
        refine ⟨9540275855812242922185239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6360183903874828614790159 9540275855812242922185239)
        ·
          refine ⟨14310413783718364383277859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9540275855812242922185239 14310413783718364383277859)
          ·
            refine ⟨21465620675577546574916789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14310413783718364383277859 21465620675577546574916789)
            ·
              refine ⟨2012401938335394991398449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21465620675577546574916789 2012401938335394991398449)
              ·
                refine ⟨1509301453751546243548837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012401938335394991398449 1509301453751546243548837)
                ·
                  refine ⟨282994022578414920665407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509301453751546243548837 282994022578414920665407)
                  ·
                    rfl

theorem cell21_1240040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_1240040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240040 prefixEnd_1240040 := by exact prefixLift 1240040
  have htrace : WordTrace (prefixWord ++ tailWord_1240040) baseStart_1240040 baseEnd_1240040 := by
    simpa [prefixWord, tailWord_1240040, baseEnd_1240040] using wordTrace_append hprefix tailTrace_1240040
  have hstable : (prefixWord ++ tailWord_1240040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240040).length < 2 ^ (prefixWord ++ tailWord_1240040).sum := by decide
  have hdescent : baseEnd_1240040 < baseStart_1240040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240099 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 6]
def baseStart_1240099 : Nat := 118140960795 + 1240099 * 2 ^ 59
def prefixEnd_1240099 : Nat := 4983230072969 + 3 ^ 40 * 1240099 * 2
def baseEnd_1240099 : Nat := 283007487182243929181953

theorem tailTrace_1240099 : CollatzResearch.WordTrace tailWord_1240099 prefixEnd_1240099 283007487182243929181953 := by
  unfold tailWord_1240099
  simp only [CollatzResearch.WordTrace]
  refine ⟨45230126334340589892683351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30153417556227059928455567 45230126334340589892683351)
  ·
    refine ⟨67845189501510884839025027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45230126334340589892683351 67845189501510884839025027)
    ·
      refine ⟨101767784252266327258537541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67845189501510884839025027 101767784252266327258537541)
      ·
        refine ⟨19081459547299936360975789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101767784252266327258537541 19081459547299936360975789)
        ·
          refine ⟨7155547330237476135365921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19081459547299936360975789 7155547330237476135365921)
          ·
            refine ⟨5366660497678107101524441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7155547330237476135365921 5366660497678107101524441)
            ·
              refine ⟨4024995373258580326143331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5366660497678107101524441 4024995373258580326143331)
              ·
                refine ⟨6037493059887870489214997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4024995373258580326143331 6037493059887870489214997)
                ·
                  refine ⟨283007487182243929181953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6037493059887870489214997 283007487182243929181953)
                  ·
                    rfl

theorem cell21_1240099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_1240099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240099 prefixEnd_1240099 := by exact prefixLift 1240099
  have htrace : WordTrace (prefixWord ++ tailWord_1240099) baseStart_1240099 baseEnd_1240099 := by
    simpa [prefixWord, tailWord_1240099, baseEnd_1240099] using wordTrace_append hprefix tailTrace_1240099
  have hstable : (prefixWord ++ tailWord_1240099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240099).length < 2 ^ (prefixWord ++ tailWord_1240099).sum := by decide
  have hdescent : baseEnd_1240099 < baseStart_1240099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240175 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_1240175 : Nat := 118140960795 + 1240175 * 2 ^ 59
def prefixEnd_1240175 : Nat := 4983230072969 + 3 ^ 40 * 1240175 * 2
def baseEnd_1240175 : Nat := 283024831417684685915131

theorem tailTrace_1240175 : CollatzResearch.WordTrace tailWord_1240175 prefixEnd_1240175 283024831417684685915131 := by
  unfold tailWord_1240175
  simp only [CollatzResearch.WordTrace]
  refine ⟨45232898282065254872449979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30155265521376836581633319 45232898282065254872449979)
  ·
    refine ⟨67849347423097882308674969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45232898282065254872449979 67849347423097882308674969)
    ·
      refine ⟨50887010567323411731506227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67849347423097882308674969 50887010567323411731506227)
      ·
        refine ⟨76330515850985117597259341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50887010567323411731506227 76330515850985117597259341)
        ·
          refine ⟨28623943444119419098972253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76330515850985117597259341 28623943444119419098972253)
          ·
            refine ⟨10733978791544782162114595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28623943444119419098972253 10733978791544782162114595)
            ·
              refine ⟨16100968187317173243171893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10733978791544782162114595 16100968187317173243171893)
              ·
                refine ⟨1509465767560984991547365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16100968187317173243171893 1509465767560984991547365)
                ·
                  refine ⟨283024831417684685915131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509465767560984991547365 283024831417684685915131)
                  ·
                    rfl

theorem cell21_1240175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_1240175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240175 prefixEnd_1240175 := by exact prefixLift 1240175
  have htrace : WordTrace (prefixWord ++ tailWord_1240175) baseStart_1240175 baseEnd_1240175 := by
    simpa [prefixWord, tailWord_1240175, baseEnd_1240175] using wordTrace_append hprefix tailTrace_1240175
  have hstable : (prefixWord ++ tailWord_1240175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240175).length < 2 ^ (prefixWord ++ tailWord_1240175).sum := by decide
  have hdescent : baseEnd_1240175 < baseStart_1240175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240206 : List Nat := [4, 1, 1, 3, 2, 2, 8]
def baseStart_1240206 : Nat := 118140960795 + 1240206 * 2 ^ 59
def prefixEnd_1240206 : Nat := 4983230072969 + 3 ^ 40 * 1240206 * 2
def baseEnd_1240206 : Nat := 31447989560003946766489

theorem tailTrace_1240206 : CollatzResearch.WordTrace tailWord_1240206 prefixEnd_1240206 31447989560003946766489 := by
  unfold tailWord_1240206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654253618119118395853559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30156019296635298111218981 5654253618119118395853559)
  ·
    refine ⟨8481380427178677593780339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5654253618119118395853559 8481380427178677593780339)
    ·
      refine ⟨12722070640768016390670509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8481380427178677593780339 12722070640768016390670509)
      ·
        refine ⟨4770776490288006146501441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12722070640768016390670509 4770776490288006146501441)
        ·
          refine ⟨3578082367716004609876081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4770776490288006146501441 3578082367716004609876081)
          ·
            refine ⟨2683561775787003457407061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578082367716004609876081 2683561775787003457407061)
            ·
              refine ⟨31447989560003946766489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2683561775787003457407061 31447989560003946766489)
              ·
                rfl

theorem cell21_1240206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 8].length) (baseStart_1240206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240206 prefixEnd_1240206 := by exact prefixLift 1240206
  have htrace : WordTrace (prefixWord ++ tailWord_1240206) baseStart_1240206 baseEnd_1240206 := by
    simpa [prefixWord, tailWord_1240206, baseEnd_1240206] using wordTrace_append hprefix tailTrace_1240206
  have hstable : (prefixWord ++ tailWord_1240206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240206).length < 2 ^ (prefixWord ++ tailWord_1240206).sum := by decide
  have hdescent : baseEnd_1240206 < baseStart_1240206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240226 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_1240226 : Nat := 118140960795 + 1240226 * 2 ^ 59
def prefixEnd_1240226 : Nat := 4983230072969 + 3 ^ 40 * 1240226 * 2
def baseEnd_1240226 : Nat := 283036470312519930565027

theorem tailTrace_1240226 : CollatzResearch.WordTrace tailWord_1240226 prefixEnd_1240226 283036470312519930565027 := by
  unfold tailWord_1240226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11308689601220122645639133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30156505603253660388371021 11308689601220122645639133)
  ·
    refine ⟨4240758600457545992114675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11308689601220122645639133 4240758600457545992114675)
    ·
      refine ⟨6361137900686318988172013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4240758600457545992114675 6361137900686318988172013)
      ·
        refine ⟨2385426712757369620564505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6361137900686318988172013 2385426712757369620564505)
        ·
          refine ⟨1789070034568027215423379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385426712757369620564505 1789070034568027215423379)
          ·
            refine ⟨2683605051852040823135069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789070034568027215423379 2683605051852040823135069)
            ·
              refine ⟨1006351894444515308675651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2683605051852040823135069 1006351894444515308675651)
              ·
                refine ⟨1509527841666772963013477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006351894444515308675651 1509527841666772963013477)
                ·
                  refine ⟨283036470312519930565027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509527841666772963013477 283036470312519930565027)
                  ·
                    rfl

theorem cell21_1240226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_1240226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240226 prefixEnd_1240226 := by exact prefixLift 1240226
  have htrace : WordTrace (prefixWord ++ tailWord_1240226) baseStart_1240226 baseEnd_1240226 := by
    simpa [prefixWord, tailWord_1240226, baseEnd_1240226] using wordTrace_append hprefix tailTrace_1240226
  have hstable : (prefixWord ++ tailWord_1240226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240226).length < 2 ^ (prefixWord ++ tailWord_1240226).sum := by decide
  have hdescent : baseEnd_1240226 < baseStart_1240226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240246 : List Nat := [5, 1, 3, 2, 2, 1, 1, 3, 3]
def baseStart_1240246 : Nat := 118140960795 + 1240246 * 2 ^ 59
def prefixEnd_1240246 : Nat := 4983230072969 + 3 ^ 40 * 1240246 * 2
def baseEnd_1240246 : Nat := 283041034585004340231653

theorem tailTrace_1240246 : CollatzResearch.WordTrace tailWord_1240246 prefixEnd_1240246 283041034585004340231653 := by
  unfold tailWord_1240246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827217991550502124892787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30156991909872022665523061 2827217991550502124892787)
  ·
    refine ⟨4240826987325753187339181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827217991550502124892787 4240826987325753187339181)
    ·
      refine ⟨1590310120247157445252193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4240826987325753187339181 1590310120247157445252193)
      ·
        refine ⟨1192732590185368083939145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1590310120247157445252193 1192732590185368083939145)
        ·
          refine ⟨894549442639026062954359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1192732590185368083939145 894549442639026062954359)
          ·
            refine ⟨1341824163958539094431539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894549442639026062954359 1341824163958539094431539)
            ·
              refine ⟨2012736245937808641647309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341824163958539094431539 2012736245937808641647309)
              ·
                refine ⟨754776092226678240617741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2012736245937808641647309 754776092226678240617741)
                ·
                  refine ⟨283041034585004340231653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754776092226678240617741 283041034585004340231653)
                  ·
                    rfl

theorem cell21_1240246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_1240246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240246 prefixEnd_1240246 := by exact prefixLift 1240246
  have htrace : WordTrace (prefixWord ++ tailWord_1240246) baseStart_1240246 baseEnd_1240246 := by
    simpa [prefixWord, tailWord_1240246, baseEnd_1240246] using wordTrace_append hprefix tailTrace_1240246
  have hstable : (prefixWord ++ tailWord_1240246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240246).length < 2 ^ (prefixWord ++ tailWord_1240246).sum := by decide
  have hdescent : baseEnd_1240246 < baseStart_1240246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240285 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 4]
def baseStart_1240285 : Nat := 118140960795 + 1240285 * 2 ^ 59
def prefixEnd_1240285 : Nat := 4983230072969 + 3 ^ 40 * 1240285 * 2
def baseEnd_1240285 : Nat := 283049934916348939081573

theorem tailTrace_1240285 : CollatzResearch.WordTrace tailWord_1240285 prefixEnd_1240285 283049934916348939081573 := by
  unfold tailWord_1240285
  simp only [CollatzResearch.WordTrace]
  refine ⟨45236910311666743658954309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30157940207777829105969539 45236910311666743658954309)
  ·
    refine ⟨8481920683437514436053933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45236910311666743658954309 8481920683437514436053933)
    ·
      refine ⟨3180720256289067913520225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8481920683437514436053933 3180720256289067913520225)
      ·
        refine ⟨2385540192216800935140169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3180720256289067913520225 2385540192216800935140169)
        ·
          refine ⟨1789155144162600701355127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385540192216800935140169 1789155144162600701355127)
          ·
            refine ⟨2683732716243901052032691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789155144162600701355127 2683732716243901052032691)
            ·
              refine ⟨4025599074365851578049037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2683732716243901052032691 4025599074365851578049037)
              ·
                refine ⟨1509599652887194341768389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4025599074365851578049037 1509599652887194341768389)
                ·
                  refine ⟨283049934916348939081573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1509599652887194341768389 283049934916348939081573)
                  ·
                    rfl

theorem cell21_1240285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_1240285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240285 prefixEnd_1240285 := by exact prefixLift 1240285
  have htrace : WordTrace (prefixWord ++ tailWord_1240285) baseStart_1240285 baseEnd_1240285 := by
    simpa [prefixWord, tailWord_1240285, baseEnd_1240285] using wordTrace_append hprefix tailTrace_1240285
  have hstable : (prefixWord ++ tailWord_1240285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240285).length < 2 ^ (prefixWord ++ tailWord_1240285).sum := by decide
  have hdescent : baseEnd_1240285 < baseStart_1240285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240296 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 7]
def baseStart_1240296 : Nat := 118140960795 + 1240296 * 2 ^ 59
def prefixEnd_1240296 : Nat := 4983230072969 + 3 ^ 40 * 1240296 * 2
def baseEnd_1240296 : Nat := 283052445266215364398217

theorem tailTrace_1240296 : CollatzResearch.WordTrace tailWord_1240296 prefixEnd_1240296 283052445266215364398217 := by
  unfold tailWord_1240296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22618655757313446268802371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30158207676417928358403161 22618655757313446268802371)
  ·
    refine ⟨33927983635970169403203557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22618655757313446268802371 33927983635970169403203557)
    ·
      refine ⟨6361496931744406763100667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33927983635970169403203557 6361496931744406763100667)
      ·
        refine ⟨9542245397616610144651001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6361496931744406763100667 9542245397616610144651001)
        ·
          refine ⟨7156684048212457608488251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9542245397616610144651001 7156684048212457608488251)
          ·
            refine ⟨10735026072318686412732377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7156684048212457608488251 10735026072318686412732377)
            ·
              refine ⟨8051269554239014809549283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10735026072318686412732377 8051269554239014809549283)
              ·
                refine ⟨12076904331358522214323925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8051269554239014809549283 12076904331358522214323925)
                ·
                  refine ⟨283052445266215364398217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12076904331358522214323925 283052445266215364398217)
                  ·
                    rfl

theorem cell21_1240296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 7].length) (baseStart_1240296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240296 prefixEnd_1240296 := by exact prefixLift 1240296
  have htrace : WordTrace (prefixWord ++ tailWord_1240296) baseStart_1240296 baseEnd_1240296 := by
    simpa [prefixWord, tailWord_1240296, baseEnd_1240296] using wordTrace_append hprefix tailTrace_1240296
  have hstable : (prefixWord ++ tailWord_1240296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240296).length < 2 ^ (prefixWord ++ tailWord_1240296).sum := by decide
  have hdescent : baseEnd_1240296 < baseStart_1240296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240313 : List Nat := [1, 2, 1, 3, 1, 1, 4, 5, 3]
def baseStart_1240313 : Nat := 118140960795 + 1240313 * 2 ^ 59
def prefixEnd_1240313 : Nat := 4983230072969 + 3 ^ 40 * 1240313 * 2
def baseEnd_1240313 : Nat := 283056324897827112614849

theorem tailTrace_1240313 : CollatzResearch.WordTrace tailWord_1240313 prefixEnd_1240313 283056324897827112614849 := by
  unfold tailWord_1240313
  simp only [CollatzResearch.WordTrace]
  refine ⟨45237931555565304440973593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30158621037043536293982395 45237931555565304440973593)
  ·
    refine ⟨33928448666673978330730195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45237931555565304440973593 33928448666673978330730195)
    ·
      refine ⟨50892673000010967496095293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33928448666673978330730195 50892673000010967496095293)
      ·
        refine ⟨19084752375004112811035735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50892673000010967496095293 19084752375004112811035735)
        ·
          refine ⟨28627128562506169216553603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19084752375004112811035735 28627128562506169216553603)
          ·
            refine ⟨42940692843759253824830405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28627128562506169216553603 42940692843759253824830405)
            ·
              refine ⟨8051379908204860092155701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42940692843759253824830405 8051379908204860092155701)
              ·
                refine ⟨754816866394205633639597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8051379908204860092155701 754816866394205633639597)
                ·
                  refine ⟨283056324897827112614849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754816866394205633639597 283056324897827112614849)
                  ·
                    rfl

theorem cell21_1240313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_1240313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240313 prefixEnd_1240313 := by exact prefixLift 1240313
  have htrace : WordTrace (prefixWord ++ tailWord_1240313) baseStart_1240313 baseEnd_1240313 := by
    simpa [prefixWord, tailWord_1240313, baseEnd_1240313] using wordTrace_append hprefix tailTrace_1240313
  have hstable : (prefixWord ++ tailWord_1240313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240313).length < 2 ^ (prefixWord ++ tailWord_1240313).sum := by decide
  have hdescent : baseEnd_1240313 < baseStart_1240313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240423 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 3]
def baseStart_1240423 : Nat := 118140960795 + 1240423 * 2 ^ 59
def prefixEnd_1240423 : Nat := 4983230072969 + 3 ^ 40 * 1240423 * 2
def baseEnd_1240423 : Nat := 283081428396491365781291

theorem tailTrace_1240423 : CollatzResearch.WordTrace tailWord_1240423 prefixEnd_1240423 283081428396491365781291 := by
  unfold tailWord_1240423
  simp only [CollatzResearch.WordTrace]
  refine ⟨45241943585166793227477923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30161295723444528818318615 45241943585166793227477923)
  ·
    refine ⟨67862915377750189841216885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45241943585166793227477923 67862915377750189841216885)
    ·
      refine ⟨6362148316664080297614083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67862915377750189841216885 6362148316664080297614083)
      ·
        refine ⟨9543222474996120446421125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6362148316664080297614083 9543222474996120446421125)
        ·
          refine ⟨1789354214061772583703961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9543222474996120446421125 1789354214061772583703961)
          ·
            refine ⟨1342015660546329437777971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1789354214061772583703961 1342015660546329437777971)
            ·
              refine ⟨2013023490819494156666957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342015660546329437777971 2013023490819494156666957)
              ·
                refine ⟨754883809057310308750109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2013023490819494156666957 754883809057310308750109)
                ·
                  refine ⟨283081428396491365781291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754883809057310308750109 283081428396491365781291)
                  ·
                    rfl

theorem cell21_1240423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 3].length) (baseStart_1240423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240423 prefixEnd_1240423 := by exact prefixLift 1240423
  have htrace : WordTrace (prefixWord ++ tailWord_1240423) baseStart_1240423 baseEnd_1240423 := by
    simpa [prefixWord, tailWord_1240423, baseEnd_1240423] using wordTrace_append hprefix tailTrace_1240423
  have hstable : (prefixWord ++ tailWord_1240423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240423).length < 2 ^ (prefixWord ++ tailWord_1240423).sum := by decide
  have hdescent : baseEnd_1240423 < baseStart_1240423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240524 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 7]
def baseStart_1240524 : Nat := 118140960795 + 1240524 * 2 ^ 59
def prefixEnd_1240524 : Nat := 4983230072969 + 3 ^ 40 * 1240524 * 2
def baseEnd_1240524 : Nat := 283104477972537634597751

theorem tailTrace_1240524 : CollatzResearch.WordTrace tailWord_1240524 prefixEnd_1240524 283104477972537634597751 := by
  unfold tailWord_1240524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22622813678900443738452313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30163751571867258317936417 22622813678900443738452313)
  ·
    refine ⟨16967110259175332803839235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22622813678900443738452313 16967110259175332803839235)
    ·
      refine ⟨25450665388762999205758853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16967110259175332803839235 25450665388762999205758853)
      ·
        refine ⟨4771999760393062351079785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25450665388762999205758853 4771999760393062351079785)
        ·
          refine ⟨3578999820294796763309839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4771999760393062351079785 3578999820294796763309839)
          ·
            refine ⟨5368499730442195144964759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3578999820294796763309839 5368499730442195144964759)
            ·
              refine ⟨8052749595663292717447139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5368499730442195144964759 8052749595663292717447139)
              ·
                refine ⟨12079124393494939076170709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8052749595663292717447139 12079124393494939076170709)
                ·
                  refine ⟨283104477972537634597751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12079124393494939076170709 283104477972537634597751)
                  ·
                    rfl

theorem cell21_1240524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_1240524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240524 prefixEnd_1240524 := by exact prefixLift 1240524
  have htrace : WordTrace (prefixWord ++ tailWord_1240524) baseStart_1240524 baseEnd_1240524 := by
    simpa [prefixWord, tailWord_1240524, baseEnd_1240524] using wordTrace_append hprefix tailTrace_1240524
  have hstable : (prefixWord ++ tailWord_1240524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240524).length < 2 ^ (prefixWord ++ tailWord_1240524).sum := by decide
  have hdescent : baseEnd_1240524 < baseStart_1240524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240586 : List Nat := [3, 1, 2, 2, 2, 2, 4, 5]
def baseStart_1240586 : Nat := 118140960795 + 1240586 * 2 ^ 59
def prefixEnd_1240586 : Nat := 4983230072969 + 3 ^ 40 * 1240586 * 2
def baseEnd_1240586 : Nat := 94372875739079768188097

theorem tailTrace_1240586 : CollatzResearch.WordTrace tailWord_1240586 prefixEnd_1240586 94372875739079768188097 := by
  unfold tailWord_1240586
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311972170894068016415403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30165259122384181377107741 11311972170894068016415403)
  ·
    refine ⟨16967958256341102024623105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11311972170894068016415403 16967958256341102024623105)
    ·
      refine ⟨12725968692255826518467329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16967958256341102024623105 12725968692255826518467329)
      ·
        refine ⟨9544476519191869888850497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12725968692255826518467329 9544476519191869888850497)
        ·
          refine ⟨7158357389393902416637873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9544476519191869888850497 7158357389393902416637873)
          ·
            refine ⟨5368768042045426812478405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7158357389393902416637873 5368768042045426812478405)
            ·
              refine ⟨1006644007883517527339701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5368768042045426812478405 1006644007883517527339701)
              ·
                refine ⟨94372875739079768188097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1006644007883517527339701 94372875739079768188097)
                ·
                  rfl

theorem cell21_1240586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_1240586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240586 prefixEnd_1240586 := by exact prefixLift 1240586
  have htrace : WordTrace (prefixWord ++ tailWord_1240586) baseStart_1240586 baseEnd_1240586 := by
    simpa [prefixWord, tailWord_1240586, baseEnd_1240586] using wordTrace_append hprefix tailTrace_1240586
  have hstable : (prefixWord ++ tailWord_1240586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240586).length < 2 ^ (prefixWord ++ tailWord_1240586).sum := by decide
  have hdescent : baseEnd_1240586 < baseStart_1240586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240631 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_1240631 : Nat := 118140960795 + 1240631 * 2 ^ 59
def prefixEnd_1240631 : Nat := 4983230072969 + 3 ^ 40 * 1240631 * 2
def baseEnd_1240631 : Nat := 283128896830329226314199

theorem tailTrace_1240631 : CollatzResearch.WordTrace tailWord_1240631 prefixEnd_1240631 283128896830329226314199 := by
  unfold tailWord_1240631
  simp only [CollatzResearch.WordTrace]
  refine ⟨45249529968413244751049747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30166353312275496500699831 45249529968413244751049747)
  ·
    refine ⟨67874294952619867126574621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45249529968413244751049747 67874294952619867126574621)
    ·
      refine ⟨25452860607232450172465483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67874294952619867126574621 25452860607232450172465483)
      ·
        refine ⟨38179290910848675258698225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25452860607232450172465483 38179290910848675258698225)
        ·
          refine ⟨28634468183136506444023669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38179290910848675258698225 28634468183136506444023669)
          ·
            refine ⟨2684481392169047479127219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28634468183136506444023669 2684481392169047479127219)
            ·
              refine ⟨4026722088253571218690829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684481392169047479127219 4026722088253571218690829)
              ·
                refine ⟨1510020783095089207009061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4026722088253571218690829 1510020783095089207009061)
                ·
                  refine ⟨283128896830329226314199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1510020783095089207009061 283128896830329226314199)
                  ·
                    rfl

theorem cell21_1240631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_1240631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240631 prefixEnd_1240631 := by exact prefixLift 1240631
  have htrace : WordTrace (prefixWord ++ tailWord_1240631) baseStart_1240631 baseEnd_1240631 := by
    simpa [prefixWord, tailWord_1240631, baseEnd_1240631] using wordTrace_append hprefix tailTrace_1240631
  have hstable : (prefixWord ++ tailWord_1240631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240631).length < 2 ^ (prefixWord ++ tailWord_1240631).sum := by decide
  have hdescent : baseEnd_1240631 < baseStart_1240631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240693 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 5]
def baseStart_1240693 : Nat := 118140960795 + 1240693 * 2 ^ 59
def prefixEnd_1240693 : Nat := 4983230072969 + 3 ^ 40 * 1240693 * 2
def baseEnd_1240693 : Nat := 283143046075030896280739

theorem tailTrace_1240693 : CollatzResearch.WordTrace tailWord_1240693 prefixEnd_1240693 283143046075030896280739 := by
  unfold tailWord_1240693
  simp only [CollatzResearch.WordTrace]
  refine ⟨45251791294188629339806733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30167860862792419559871155 45251791294188629339806733)
  ·
    refine ⟨16969421735320736002427525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45251791294188629339806733 16969421735320736002427525)
    ·
      refine ⟨3181766575372638000455161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16969421735320736002427525 3181766575372638000455161)
      ·
        refine ⟨2386324931529478500341371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181766575372638000455161 2386324931529478500341371)
        ·
          refine ⟨3579487397294217750512057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386324931529478500341371 3579487397294217750512057)
          ·
            refine ⟨2684615547970663312884043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579487397294217750512057 2684615547970663312884043)
            ·
              refine ⟨4026923321955994969326065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684615547970663312884043 4026923321955994969326065)
              ·
                refine ⟨3020192491466996226994549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4026923321955994969326065 3020192491466996226994549)
                ·
                  refine ⟨283143046075030896280739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020192491466996226994549 283143046075030896280739)
                  ·
                    rfl

theorem cell21_1240693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 5].length) (baseStart_1240693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240693 prefixEnd_1240693 := by exact prefixLift 1240693
  have htrace : WordTrace (prefixWord ++ tailWord_1240693) baseStart_1240693 baseEnd_1240693 := by
    simpa [prefixWord, tailWord_1240693, baseEnd_1240693] using wordTrace_append hprefix tailTrace_1240693
  have hstable : (prefixWord ++ tailWord_1240693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240693).length < 2 ^ (prefixWord ++ tailWord_1240693).sum := by decide
  have hdescent : baseEnd_1240693 < baseStart_1240693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240724 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_1240724 : Nat := 118140960795 + 1240724 * 2 ^ 59
def prefixEnd_1240724 : Nat := 4983230072969 + 3 ^ 40 * 1240724 * 2
def baseEnd_1240724 : Nat := 283150120697381731264009

theorem tailTrace_1240724 : CollatzResearch.WordTrace tailWord_1240724 prefixEnd_1240724 283150120697381731264009 := by
  unfold tailWord_1240724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22626460978538160817092613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30168614638050881089456817 22626460978538160817092613)
  ·
    refine ⟨4242461433475905153204865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22626460978538160817092613 4242461433475905153204865)
    ·
      refine ⟨3181846075106928864903649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4242461433475905153204865 3181846075106928864903649)
      ·
        refine ⟨2386384556330196648677737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3181846075106928864903649 2386384556330196648677737)
        ·
          refine ⟨1789788417247647486508303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2386384556330196648677737 1789788417247647486508303)
          ·
            refine ⟨2684682625871471229762455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1789788417247647486508303 2684682625871471229762455)
            ·
              refine ⟨4027023938807206844643683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2684682625871471229762455 4027023938807206844643683)
              ·
                refine ⟨6040535908210810266965525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4027023938807206844643683 6040535908210810266965525)
                ·
                  refine ⟨283150120697381731264009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6040535908210810266965525 283150120697381731264009)
                  ·
                    rfl

theorem cell21_1240724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_1240724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240724 prefixEnd_1240724 := by exact prefixLift 1240724
  have htrace : WordTrace (prefixWord ++ tailWord_1240724) baseStart_1240724 baseEnd_1240724 := by
    simpa [prefixWord, tailWord_1240724, baseEnd_1240724] using wordTrace_append hprefix tailTrace_1240724
  have hstable : (prefixWord ++ tailWord_1240724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240724).length < 2 ^ (prefixWord ++ tailWord_1240724).sum := by decide
  have hdescent : baseEnd_1240724 < baseStart_1240724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240811 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_1240811 : Nat := 118140960795 + 1240811 * 2 ^ 59
def prefixEnd_1240811 : Nat := 4983230072969 + 3 ^ 40 * 1240811 * 2
def baseEnd_1240811 : Nat := 283169975282688913313831

theorem tailTrace_1240811 : CollatzResearch.WordTrace tailWord_1240811 prefixEnd_1240811 283169975282688913313831 := by
  unfold tailWord_1240811
  simp only [CollatzResearch.WordTrace]
  refine ⟨45256095107761135492602287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30170730071840756995068191 45256095107761135492602287)
  ·
    refine ⟨67884142661641703238903431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45256095107761135492602287 67884142661641703238903431)
    ·
      refine ⟨101826213992462554858355147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67884142661641703238903431 101826213992462554858355147)
      ·
        refine ⟨152739320988693832287532721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101826213992462554858355147 152739320988693832287532721)
        ·
          refine ⟨114554490741520374215649541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152739320988693832287532721 114554490741520374215649541)
          ·
            refine ⟨21478967014035070165434289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114554490741520374215649541 21478967014035070165434289)
            ·
              refine ⟨16109225260526302624075717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21478967014035070165434289 16109225260526302624075717)
              ·
                refine ⟨3020479736348681742014197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16109225260526302624075717 3020479736348681742014197)
                ·
                  refine ⟨283169975282688913313831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020479736348681742014197 283169975282688913313831)
                  ·
                    rfl

theorem cell21_1240811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_1240811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240811 prefixEnd_1240811 := by exact prefixLift 1240811
  have htrace : WordTrace (prefixWord ++ tailWord_1240811) baseStart_1240811 baseEnd_1240811 := by
    simpa [prefixWord, tailWord_1240811, baseEnd_1240811] using wordTrace_append hprefix tailTrace_1240811
  have hstable : (prefixWord ++ tailWord_1240811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240811).length < 2 ^ (prefixWord ++ tailWord_1240811).sum := by decide
  have hdescent : baseEnd_1240811 < baseStart_1240811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240904 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_1240904 : Nat := 118140960795 + 1240904 * 2 ^ 59
def prefixEnd_1240904 : Nat := 4983230072969 + 3 ^ 40 * 1240904 * 2
def baseEnd_1240904 : Nat := 283191199149741418263641

theorem tailTrace_1240904 : CollatzResearch.WordTrace tailWord_1240904 prefixEnd_1240904 283191199149741418263641 := by
  unfold tailWord_1240904
  simp only [CollatzResearch.WordTrace]
  refine ⟨22629743548212106187868883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30172991397616141583825177 22629743548212106187868883)
  ·
    refine ⟨33944615322318159281803325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22629743548212106187868883 33944615322318159281803325)
    ·
      refine ⟨12729230745869309730676247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33944615322318159281803325 12729230745869309730676247)
      ·
        refine ⟨19093846118803964596014371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12729230745869309730676247 19093846118803964596014371)
        ·
          refine ⟨28640769178205946894021557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19093846118803964596014371 28640769178205946894021557)
          ·
            refine ⟨2685072110456807521314521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28640769178205946894021557 2685072110456807521314521)
            ·
              refine ⟨2013804082842605640985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2685072110456807521314521 2013804082842605640985891)
              ·
                refine ⟨3020706124263908461478837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013804082842605640985891 3020706124263908461478837)
                ·
                  refine ⟨283191199149741418263641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3020706124263908461478837 283191199149741418263641)
                  ·
                    rfl

theorem cell21_1240904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_1240904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240904 prefixEnd_1240904 := by exact prefixLift 1240904
  have htrace : WordTrace (prefixWord ++ tailWord_1240904) baseStart_1240904 baseEnd_1240904 := by
    simpa [prefixWord, tailWord_1240904, baseEnd_1240904] using wordTrace_append hprefix tailTrace_1240904
  have hstable : (prefixWord ++ tailWord_1240904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240904).length < 2 ^ (prefixWord ++ tailWord_1240904).sum := by decide
  have hdescent : baseEnd_1240904 < baseStart_1240904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1240924 : List Nat := [2, 2, 4, 2, 3, 1, 2, 5]
def baseStart_1240924 : Nat := 118140960795 + 1240924 * 2 ^ 59
def prefixEnd_1240924 : Nat := 4983230072969 + 3 ^ 40 * 1240924 * 2
def baseEnd_1240924 : Nat := 94398587807408609310089

theorem tailTrace_1240924 : CollatzResearch.WordTrace tailWord_1240924 prefixEnd_1240924 94398587807408609310089 := by
  unfold tailWord_1240924
  simp only [CollatzResearch.WordTrace]
  refine ⟨22630108278175877895732913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30173477704234503860977217 22630108278175877895732913)
  ·
    refine ⟨16972581208631908421799685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22630108278175877895732913 16972581208631908421799685)
    ·
      refine ⟨3182358976618482829087441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16972581208631908421799685 3182358976618482829087441)
      ·
        refine ⟨2386769232463862121815581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3182358976618482829087441 2386769232463862121815581)
        ·
          refine ⟨895038462173948295680843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2386769232463862121815581 895038462173948295680843)
          ·
            refine ⟨1342557693260922443521265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895038462173948295680843 1342557693260922443521265)
            ·
              refine ⟨1006918269945691832640949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342557693260922443521265 1006918269945691832640949)
              ·
                refine ⟨94398587807408609310089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1006918269945691832640949 94398587807408609310089)
                ·
                  rfl

theorem cell21_1240924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_1240924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1240924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1240924 prefixEnd_1240924 := by exact prefixLift 1240924
  have htrace : WordTrace (prefixWord ++ tailWord_1240924) baseStart_1240924 baseEnd_1240924 := by
    simpa [prefixWord, tailWord_1240924, baseEnd_1240924] using wordTrace_append hprefix tailTrace_1240924
  have hstable : (prefixWord ++ tailWord_1240924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1240924).length < 2 ^ (prefixWord ++ tailWord_1240924).sum := by decide
  have hdescent : baseEnd_1240924 < baseStart_1240924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1240924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241006 : List Nat := [4, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_1241006 : Nat := 118140960795 + 1241006 * 2 ^ 59
def prefixEnd_1241006 : Nat := 4983230072969 + 3 ^ 40 * 1241006 * 2
def baseEnd_1241006 : Nat := 283214476939411907563433

theorem tailTrace_1241006 : CollatzResearch.WordTrace tailWord_1241006 prefixEnd_1241006 283214476939411907563433 := by
  unfold tailWord_1241006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657900917756835474493859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30175471561369789197300581 5657900917756835474493859)
  ·
    refine ⟨8486851376635253211740789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657900917756835474493859 8486851376635253211740789)
    ·
      refine ⟨795642316559554988600699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8486851376635253211740789 795642316559554988600699)
      ·
        refine ⟨1193463474839332482901049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795642316559554988600699 1193463474839332482901049)
        ·
          refine ⟨895097606129499362175787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193463474839332482901049 895097606129499362175787)
          ·
            refine ⟨1342646409194249043263681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895097606129499362175787 1342646409194249043263681)
            ·
              refine ⟨1006984806895686782447761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342646409194249043263681 1006984806895686782447761)
              ·
                refine ⟨755238605171765086835821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1006984806895686782447761 755238605171765086835821)
                ·
                  refine ⟨283214476939411907563433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755238605171765086835821 283214476939411907563433)
                  ·
                    rfl

theorem cell21_1241006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_1241006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241006 prefixEnd_1241006 := by exact prefixLift 1241006
  have htrace : WordTrace (prefixWord ++ tailWord_1241006) baseStart_1241006 baseEnd_1241006 := by
    simpa [prefixWord, tailWord_1241006, baseEnd_1241006] using wordTrace_append hprefix tailTrace_1241006
  have hstable : (prefixWord ++ tailWord_1241006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241006).length < 2 ^ (prefixWord ++ tailWord_1241006).sum := by decide
  have hdescent : baseEnd_1241006 < baseStart_1241006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241039 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_1241039 : Nat := 118140960795 + 1241039 * 2 ^ 59
def prefixEnd_1241039 : Nat := 4983230072969 + 3 ^ 40 * 1241039 * 2
def baseEnd_1241039 : Nat := 283222007989011183513365

theorem tailTrace_1241039 : CollatzResearch.WordTrace tailWord_1241039 prefixEnd_1241039 283222007989011183513365 := by
  unfold tailWord_1241039
  simp only [CollatzResearch.WordTrace]
  refine ⟨45264410950935130431902171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30176273967290086954601447 45264410950935130431902171)
  ·
    refine ⟨67896616426402695647853257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45264410950935130431902171 67896616426402695647853257)
    ·
      refine ⟨50922462319802021735889943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67896616426402695647853257 50922462319802021735889943)
      ·
        refine ⟨76383693479703032603834915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50922462319802021735889943 76383693479703032603834915)
        ·
          refine ⟨114575540219554548905752373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76383693479703032603834915 114575540219554548905752373)
          ·
            refine ⟨10741456895583238959914285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114575540219554548905752373 10741456895583238959914285)
            ·
              refine ⟨4028046335843714609967857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10741456895583238959914285 4028046335843714609967857)
              ·
                refine ⟨3021034751882785957475893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4028046335843714609967857 3021034751882785957475893)
                ·
                  refine ⟨283222007989011183513365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021034751882785957475893 283222007989011183513365)
                  ·
                    rfl

theorem cell21_1241039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_1241039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241039 prefixEnd_1241039 := by exact prefixLift 1241039
  have htrace : WordTrace (prefixWord ++ tailWord_1241039) baseStart_1241039 baseEnd_1241039 := by
    simpa [prefixWord, tailWord_1241039, baseEnd_1241039] using wordTrace_append hprefix tailTrace_1241039
  have hstable : (prefixWord ++ tailWord_1241039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241039).length < 2 ^ (prefixWord ++ tailWord_1241039).sum := by decide
  have hdescent : baseEnd_1241039 < baseStart_1241039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241084 : List Nat := [2, 2, 2, 1, 2, 2, 2, 8]
def baseStart_1241084 : Nat := 118140960795 + 1241084 * 2 ^ 59
def prefixEnd_1241084 : Nat := 4983230072969 + 3 ^ 40 * 1241084 * 2
def baseEnd_1241084 : Nat := 94410759200700368421091

theorem tailTrace_1241084 : CollatzResearch.WordTrace tailWord_1241084 prefixEnd_1241084 94410759200700368421091 := by
  unfold tailWord_1241084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22633026117886051558645153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30177368157181402078193537 22633026117886051558645153)
  ·
    refine ⟨16974769588414538668983865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22633026117886051558645153 16974769588414538668983865)
    ·
      refine ⟨12731077191310904001737899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16974769588414538668983865 12731077191310904001737899)
      ·
        refine ⟨19096615786966356002606849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12731077191310904001737899 19096615786966356002606849)
        ·
          refine ⟨14322461840224767001955137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19096615786966356002606849 14322461840224767001955137)
          ·
            refine ⟨10741846380168575251466353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14322461840224767001955137 10741846380168575251466353)
            ·
              refine ⟨8056384785126431438599765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10741846380168575251466353 8056384785126431438599765)
              ·
                refine ⟨94410759200700368421091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8056384785126431438599765 94410759200700368421091)
                ·
                  rfl

theorem cell21_1241084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_1241084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241084 prefixEnd_1241084 := by exact prefixLift 1241084
  have htrace : WordTrace (prefixWord ++ tailWord_1241084) baseStart_1241084 baseEnd_1241084 := by
    simpa [prefixWord, tailWord_1241084, baseEnd_1241084] using wordTrace_append hprefix tailTrace_1241084
  have hstable : (prefixWord ++ tailWord_1241084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241084).length < 2 ^ (prefixWord ++ tailWord_1241084).sum := by decide
  have hdescent : baseEnd_1241084 < baseStart_1241084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241191 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 5]
def baseStart_1241191 : Nat := 118140960795 + 1241191 * 2 ^ 59
def prefixEnd_1241191 : Nat := 4983230072969 + 3 ^ 40 * 1241191 * 2
def baseEnd_1241191 : Nat := 283256696459892696979721

theorem tailTrace_1241191 : CollatzResearch.WordTrace tailWord_1241191 prefixEnd_1241191 283256696459892696979721 := by
  unfold tailWord_1241191
  simp only [CollatzResearch.WordTrace]
  refine ⟨45269954846384460391435427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30179969897589640260956951 45269954846384460391435427)
  ·
    refine ⟨67904932269576690587153141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45269954846384460391435427 67904932269576690587153141)
    ·
      refine ⟨6366087400272814742545607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67904932269576690587153141 6366087400272814742545607)
      ·
        refine ⟨9549131100409222113818411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6366087400272814742545607 9549131100409222113818411)
        ·
          refine ⟨14323696650613833170727617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9549131100409222113818411 14323696650613833170727617)
          ·
            refine ⟨10742772487960374878045713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14323696650613833170727617 10742772487960374878045713)
            ·
              refine ⟨8057079365970281158534285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10742772487960374878045713 8057079365970281158534285)
              ·
                refine ⟨3021404762238855434450357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8057079365970281158534285 3021404762238855434450357)
                ·
                  refine ⟨283256696459892696979721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021404762238855434450357 283256696459892696979721)
                  ·
                    rfl

theorem cell21_1241191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 5].length) (baseStart_1241191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241191 prefixEnd_1241191 := by exact prefixLift 1241191
  have htrace : WordTrace (prefixWord ++ tailWord_1241191) baseStart_1241191 baseEnd_1241191 := by
    simpa [prefixWord, tailWord_1241191, baseEnd_1241191] using wordTrace_append hprefix tailTrace_1241191
  have hstable : (prefixWord ++ tailWord_1241191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241191).length < 2 ^ (prefixWord ++ tailWord_1241191).sum := by decide
  have hdescent : baseEnd_1241191 < baseStart_1241191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241194 : List Nat := [3, 1, 3, 2, 3, 2, 1, 6]
def baseStart_1241194 : Nat := 118140960795 + 1241194 * 2 ^ 59
def prefixEnd_1241194 : Nat := 4983230072969 + 3 ^ 40 * 1241194 * 2
def baseEnd_1241194 : Nat := 94419127033588452809905

theorem tailTrace_1241194 : CollatzResearch.WordTrace tailWord_1241194 prefixEnd_1241194 94419127033588452809905 := by
  unfold tailWord_1241194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11317516066343397975948659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30180042843582394602529757 11317516066343397975948659)
  ·
    refine ⟨16976274099515096963922989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11317516066343397975948659 16976274099515096963922989)
    ·
      refine ⟨6366102787318161361471121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16976274099515096963922989 6366102787318161361471121)
      ·
        refine ⟨4774577090488621021103341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366102787318161361471121 4774577090488621021103341)
        ·
          refine ⟨1790466408933232882913753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4774577090488621021103341 1790466408933232882913753)
          ·
            refine ⟨1342849806699924662185315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790466408933232882913753 1342849806699924662185315)
            ·
              refine ⟨2014274710049886993277973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342849806699924662185315 2014274710049886993277973)
              ·
                refine ⟨94419127033588452809905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2014274710049886993277973 94419127033588452809905)
                ·
                  rfl

theorem cell21_1241194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_1241194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241194 prefixEnd_1241194 := by exact prefixLift 1241194
  have htrace : WordTrace (prefixWord ++ tailWord_1241194) baseStart_1241194 baseEnd_1241194 := by
    simpa [prefixWord, tailWord_1241194, baseEnd_1241194] using wordTrace_append hprefix tailTrace_1241194
  have hstable : (prefixWord ++ tailWord_1241194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241194).length < 2 ^ (prefixWord ++ tailWord_1241194).sum := by decide
  have hdescent : baseEnd_1241194 < baseStart_1241194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241298 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1241298 : Nat := 118140960795 + 1241298 * 2 ^ 59
def prefixEnd_1241298 : Nat := 4983230072969 + 3 ^ 40 * 1241298 * 2
def baseEnd_1241298 : Nat := 283281115317684288696169

theorem tailTrace_1241298 : CollatzResearch.WordTrace tailWord_1241298 prefixEnd_1241298 283281115317684288696169 := by
  unfold tailWord_1241298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11318464364249204416395137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30182571637997878443720365 11318464364249204416395137)
  ·
    refine ⟨8488848273186903312296353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11318464364249204416395137 8488848273186903312296353)
    ·
      refine ⟨6366636204890177484222265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8488848273186903312296353 6366636204890177484222265)
      ·
        refine ⟨4774977153667633113166699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6366636204890177484222265 4774977153667633113166699)
        ·
          refine ⟨7162465730501449669750049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4774977153667633113166699 7162465730501449669750049)
          ·
            refine ⟨5371849297876087252312537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7162465730501449669750049 5371849297876087252312537)
            ·
              refine ⟨4028886973407065439234403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5371849297876087252312537 4028886973407065439234403)
              ·
                refine ⟨6043330460110598158851605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4028886973407065439234403 6043330460110598158851605)
                ·
                  refine ⟨283281115317684288696169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6043330460110598158851605 283281115317684288696169)
                  ·
                    rfl

theorem cell21_1241298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1241298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241298 prefixEnd_1241298 := by exact prefixLift 1241298
  have htrace : WordTrace (prefixWord ++ tailWord_1241298) baseStart_1241298 baseEnd_1241298 := by
    simpa [prefixWord, tailWord_1241298, baseEnd_1241298] using wordTrace_append hprefix tailTrace_1241298
  have hstable : (prefixWord ++ tailWord_1241298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241298).length < 2 ^ (prefixWord ++ tailWord_1241298).sum := by decide
  have hdescent : baseEnd_1241298 < baseStart_1241298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241301 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 5]
def baseStart_1241301 : Nat := 118140960795 + 1241301 * 2 ^ 59
def prefixEnd_1241301 : Nat := 4983230072969 + 3 ^ 40 * 1241301 * 2
def baseEnd_1241301 : Nat := 283281799958556950146163

theorem tailTrace_1241301 : CollatzResearch.WordTrace tailWord_1241301 prefixEnd_1241301 283281799958556950146163 := by
  unfold tailWord_1241301
  simp only [CollatzResearch.WordTrace]
  refine ⟨45273966875985949177939757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30182644583990632785293171 45273966875985949177939757)
  ·
    refine ⟨16977737578494730941727409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45273966875985949177939757 16977737578494730941727409)
    ·
      refine ⟨12733303183871048206295557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16977737578494730941727409 12733303183871048206295557)
      ·
        refine ⟨2387494346975821538680417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12733303183871048206295557 2387494346975821538680417)
        ·
          refine ⟨1790620760231866154010313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2387494346975821538680417 1790620760231866154010313)
          ·
            refine ⟨1342965570173899615507735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1790620760231866154010313 1342965570173899615507735)
            ·
              refine ⟨2014448355260849423261603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1342965570173899615507735 2014448355260849423261603)
              ·
                refine ⟨3021672532891274134892405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2014448355260849423261603 3021672532891274134892405)
                ·
                  refine ⟨283281799958556950146163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021672532891274134892405 283281799958556950146163)
                  ·
                    rfl

theorem cell21_1241301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_1241301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241301 prefixEnd_1241301 := by exact prefixLift 1241301
  have htrace : WordTrace (prefixWord ++ tailWord_1241301) baseStart_1241301 baseEnd_1241301 := by
    simpa [prefixWord, tailWord_1241301, baseEnd_1241301] using wordTrace_append hprefix tailTrace_1241301
  have hstable : (prefixWord ++ tailWord_1241301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241301).length < 2 ^ (prefixWord ++ tailWord_1241301).sum := by decide
  have hdescent : baseEnd_1241301 < baseStart_1241301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241312 : List Nat := [2, 1, 1, 3, 1, 3, 4, 6]
def baseStart_1241312 : Nat := 118140960795 + 1241312 * 2 ^ 59
def prefixEnd_1241312 : Nat := 4983230072969 + 3 ^ 40 * 1241312 * 2
def baseEnd_1241312 : Nat := 94428103436141125154269

theorem tailTrace_1241312 : CollatzResearch.WordTrace tailWord_1241312 prefixEnd_1241312 94428103436141125154269 := by
  unfold tailWord_1241312
  simp only [CollatzResearch.WordTrace]
  refine ⟨22637184039473049028295095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30182912052630732037726793 22637184039473049028295095)
  ·
    refine ⟨33955776059209573542442643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22637184039473049028295095 33955776059209573542442643)
    ·
      refine ⟨50933664088814360313663965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33955776059209573542442643 50933664088814360313663965)
      ·
        refine ⟨19100124033305385117623987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50933664088814360313663965 19100124033305385117623987)
        ·
          refine ⟨28650186049958077676435981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19100124033305385117623987 28650186049958077676435981)
          ·
            refine ⟨10743819768734279128663493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28650186049958077676435981 10743819768734279128663493)
            ·
              refine ⟨2014466206637677336624405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10743819768734279128663493 2014466206637677336624405)
              ·
                refine ⟨94428103436141125154269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2014466206637677336624405 94428103436141125154269)
                ·
                  rfl

theorem cell21_1241312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_1241312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241312 prefixEnd_1241312 := by exact prefixLift 1241312
  have htrace : WordTrace (prefixWord ++ tailWord_1241312) baseStart_1241312 baseEnd_1241312 := by
    simpa [prefixWord, tailWord_1241312, baseEnd_1241312] using wordTrace_append hprefix tailTrace_1241312
  have hstable : (prefixWord ++ tailWord_1241312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241312).length < 2 ^ (prefixWord ++ tailWord_1241312).sum := by decide
  have hdescent : baseEnd_1241312 < baseStart_1241312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241450 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_1241450 : Nat := 118140960795 + 1241450 * 2 ^ 59
def prefixEnd_1241450 : Nat := 4983230072969 + 3 ^ 40 * 1241450 * 2
def baseEnd_1241450 : Nat := 283315803788565802162525

theorem tailTrace_1241450 : CollatzResearch.WordTrace tailWord_1241450 prefixEnd_1241450 283315803788565802162525 := by
  unfold tailWord_1241450
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319850338111536906278451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30186267568297431750075869 11319850338111536906278451)
  ·
    refine ⟨16979775507167305359417677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11319850338111536906278451 16979775507167305359417677)
    ·
      refine ⟨6367415815187739509781629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16979775507167305359417677 6367415815187739509781629)
      ·
        refine ⟨2387780930695402316168111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6367415815187739509781629 2387780930695402316168111)
        ·
          refine ⟨3581671396043103474252167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2387780930695402316168111 3581671396043103474252167)
          ·
            refine ⟨5372507094064655211378251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581671396043103474252167 5372507094064655211378251)
            ·
              refine ⟨8058760641096982817067377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372507094064655211378251 8058760641096982817067377)
              ·
                refine ⟨6044070480822737112800533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8058760641096982817067377 6044070480822737112800533)
                ·
                  refine ⟨283315803788565802162525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6044070480822737112800533 283315803788565802162525)
                  ·
                    rfl

theorem cell21_1241450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_1241450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241450 prefixEnd_1241450 := by exact prefixLift 1241450
  have htrace : WordTrace (prefixWord ++ tailWord_1241450) baseStart_1241450 baseEnd_1241450 := by
    simpa [prefixWord, tailWord_1241450, baseEnd_1241450] using wordTrace_append hprefix tailTrace_1241450
  have hstable : (prefixWord ++ tailWord_1241450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241450).length < 2 ^ (prefixWord ++ tailWord_1241450).sum := by decide
  have hdescent : baseEnd_1241450 < baseStart_1241450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241529 : List Nat := [1, 2, 1, 4, 3, 1, 4, 2, 3]
def baseStart_1241529 : Nat := 118140960795 + 1241529 * 2 ^ 59
def prefixEnd_1241529 : Nat := 4983230072969 + 3 ^ 40 * 1241529 * 2
def baseEnd_1241529 : Nat := 283333832664879220345697

theorem tailTrace_1241529 : CollatzResearch.WordTrace tailWord_1241529 prefixEnd_1241529 283333832664879220345697 := by
  unfold tailWord_1241529
  simp only [CollatzResearch.WordTrace]
  refine ⟨45282282719159944117239641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30188188479439962744826427 45282282719159944117239641)
  ·
    refine ⟨33961712039369958087929731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45282282719159944117239641 33961712039369958087929731)
    ·
      refine ⟨50942568059054937131894597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33961712039369958087929731 50942568059054937131894597)
      ·
        refine ⟨9551731511072800712230237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50942568059054937131894597 9551731511072800712230237)
        ·
          refine ⟨3581899316652300267086339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9551731511072800712230237 3581899316652300267086339)
          ·
            refine ⟨5372848974978450400629509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581899316652300267086339 5372848974978450400629509)
            ·
              refine ⟨1007409182808459450118033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5372848974978450400629509 1007409182808459450118033)
              ·
                refine ⟨755556887106344587588525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007409182808459450118033 755556887106344587588525)
                ·
                  refine ⟨283333832664879220345697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755556887106344587588525 283333832664879220345697)
                  ·
                    rfl

theorem cell21_1241529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 4, 2, 3].length) (baseStart_1241529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241529 prefixEnd_1241529 := by exact prefixLift 1241529
  have htrace : WordTrace (prefixWord ++ tailWord_1241529) baseStart_1241529 baseEnd_1241529 := by
    simpa [prefixWord, tailWord_1241529, baseEnd_1241529] using wordTrace_append hprefix tailTrace_1241529
  have hstable : (prefixWord ++ tailWord_1241529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241529).length < 2 ^ (prefixWord ++ tailWord_1241529).sum := by decide
  have hdescent : baseEnd_1241529 < baseStart_1241529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241557 : List Nat := [1, 3, 2, 3, 1, 3, 3, 5]
def baseStart_1241557 : Nat := 118140960795 + 1241557 * 2 ^ 59
def prefixEnd_1241557 : Nat := 4983230072969 + 3 ^ 40 * 1241557 * 2
def baseEnd_1241557 : Nat := 94446740882119131292991

theorem tailTrace_1241557 : CollatzResearch.WordTrace tailWord_1241557 prefixEnd_1241557 94446740882119131292991 := by
  unfold tailWord_1241557
  simp only [CollatzResearch.WordTrace]
  refine ⟨45283303963058504899258925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30188869308705669932839283 45283303963058504899258925)
  ·
    refine ⟨16981238986146939337222097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45283303963058504899258925 16981238986146939337222097)
    ·
      refine ⟨12735929239610204502916573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16981238986146939337222097 12735929239610204502916573)
      ·
        refine ⟨4775973464853826688593715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12735929239610204502916573 4775973464853826688593715)
        ·
          refine ⟨7163960197280740032890573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775973464853826688593715 7163960197280740032890573)
          ·
            refine ⟨2686485073980277512333965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7163960197280740032890573 2686485073980277512333965)
            ·
              refine ⟨1007431902742604067125237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686485073980277512333965 1007431902742604067125237)
              ·
                refine ⟨94446740882119131292991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1007431902742604067125237 94446740882119131292991)
                ·
                  rfl

theorem cell21_1241557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 3, 5].length) (baseStart_1241557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241557 prefixEnd_1241557 := by exact prefixLift 1241557
  have htrace : WordTrace (prefixWord ++ tailWord_1241557) baseStart_1241557 baseEnd_1241557 := by
    simpa [prefixWord, tailWord_1241557, baseEnd_1241557] using wordTrace_append hprefix tailTrace_1241557
  have hstable : (prefixWord ++ tailWord_1241557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241557).length < 2 ^ (prefixWord ++ tailWord_1241557).sum := by decide
  have hdescent : baseEnd_1241557 < baseStart_1241557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241585 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_1241585 : Nat := 118140960795 + 1241585 * 2 ^ 59
def prefixEnd_1241585 : Nat := 4983230072969 + 3 ^ 40 * 1241585 * 2
def baseEnd_1241585 : Nat := 283346612627835567412249

theorem tailTrace_1241585 : CollatzResearch.WordTrace tailWord_1241585 prefixEnd_1241585 283346612627835567412249 := by
  unfold tailWord_1241585
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284325206957065681278209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189550137971377120852139 45284325206957065681278209)
  ·
    refine ⟨33963243905217799260958657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45284325206957065681278209 33963243905217799260958657)
    ·
      refine ⟨25472432928913349445718993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33963243905217799260958657 25472432928913349445718993)
      ·
        refine ⟨19104324696685012084289245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25472432928913349445718993 19104324696685012084289245)
        ·
          refine ⟨7164121761256879531608467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19104324696685012084289245 7164121761256879531608467)
          ·
            refine ⟨10746182641885319297412701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164121761256879531608467 10746182641885319297412701)
            ·
              refine ⟨4029818490706994736529763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10746182641885319297412701 4029818490706994736529763)
              ·
                refine ⟨6044727736060492104794645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029818490706994736529763 6044727736060492104794645)
                ·
                  refine ⟨283346612627835567412249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6044727736060492104794645 283346612627835567412249)
                  ·
                    rfl

theorem cell21_1241585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_1241585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241585 prefixEnd_1241585 := by exact prefixLift 1241585
  have htrace : WordTrace (prefixWord ++ tailWord_1241585) baseStart_1241585 baseEnd_1241585 := by
    simpa [prefixWord, tailWord_1241585, baseEnd_1241585] using wordTrace_append hprefix tailTrace_1241585
  have hstable : (prefixWord ++ tailWord_1241585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241585).length < 2 ^ (prefixWord ++ tailWord_1241585).sum := by decide
  have hdescent : baseEnd_1241585 < baseStart_1241585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241599 : List Nat := [1, 1, 2, 2, 1, 2, 4, 8]
def baseStart_1241599 : Nat := 118140960795 + 1241599 * 2 ^ 59
def prefixEnd_1241599 : Nat := 4983230072969 + 3 ^ 40 * 1241599 * 2
def baseEnd_1241599 : Nat := 94449935872858218059629

theorem tailTrace_1241599 : CollatzResearch.WordTrace tailWord_1241599 prefixEnd_1241599 94449935872858218059629 := by
  unfold tailWord_1241599
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284835828906346072287851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30189890552604230714858567 45284835828906346072287851)
  ·
    refine ⟨67927253743359519108431777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45284835828906346072287851 67927253743359519108431777)
    ·
      refine ⟨50945440307519639331323833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67927253743359519108431777 50945440307519639331323833)
      ·
        refine ⟨38209080230639729498492875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50945440307519639331323833 38209080230639729498492875)
        ·
          refine ⟨57313620345959594247739313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38209080230639729498492875 57313620345959594247739313)
          ·
            refine ⟨42985215259469695685804485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57313620345959594247739313 42985215259469695685804485)
            ·
              refine ⟨8059727861150567941088341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42985215259469695685804485 8059727861150567941088341)
              ·
                refine ⟨94449935872858218059629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8059727861150567941088341 94449935872858218059629)
                ·
                  rfl

theorem cell21_1241599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 8].length) (baseStart_1241599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241599 prefixEnd_1241599 := by exact prefixLift 1241599
  have htrace : WordTrace (prefixWord ++ tailWord_1241599) baseStart_1241599 baseEnd_1241599 := by
    simpa [prefixWord, tailWord_1241599, baseEnd_1241599] using wordTrace_append hprefix tailTrace_1241599
  have hstable : (prefixWord ++ tailWord_1241599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241599).length < 2 ^ (prefixWord ++ tailWord_1241599).sum := by decide
  have hdescent : baseEnd_1241599 < baseStart_1241599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241639 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 3]
def baseStart_1241639 : Nat := 118140960795 + 1241639 * 2 ^ 59
def prefixEnd_1241639 : Nat := 4983230072969 + 3 ^ 40 * 1241639 * 2
def baseEnd_1241639 : Nat := 283358936163543473512139

theorem tailTrace_1241639 : CollatzResearch.WordTrace tailWord_1241639 prefixEnd_1241639 283358936163543473512139 := by
  unfold tailWord_1241639
  simp only [CollatzResearch.WordTrace]
  refine ⟨45286294748761432903743971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30190863165840955269162647 45286294748761432903743971)
  ·
    refine ⟨67929442123142149355615957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45286294748761432903743971 67929442123142149355615957)
    ·
      refine ⟨1592096299761144125522249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 67929442123142149355615957 1592096299761144125522249)
      ·
        refine ⟨1194072224820858094141687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1592096299761144125522249 1194072224820858094141687)
        ·
          refine ⟨1791108337231287141212531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194072224820858094141687 1791108337231287141212531)
          ·
            refine ⟨2686662505846930711818797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791108337231287141212531 2686662505846930711818797)
            ·
              refine ⟨1007498439692599016932049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2686662505846930711818797 1007498439692599016932049)
              ·
                refine ⟨755623829769449262699037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1007498439692599016932049 755623829769449262699037)
                ·
                  refine ⟨283358936163543473512139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755623829769449262699037 283358936163543473512139)
                  ·
                    rfl

theorem cell21_1241639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].length) (baseStart_1241639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241639 prefixEnd_1241639 := by exact prefixLift 1241639
  have htrace : WordTrace (prefixWord ++ tailWord_1241639) baseStart_1241639 baseEnd_1241639 := by
    simpa [prefixWord, tailWord_1241639, baseEnd_1241639] using wordTrace_append hprefix tailTrace_1241639
  have hstable : (prefixWord ++ tailWord_1241639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241639).length < 2 ^ (prefixWord ++ tailWord_1241639).sum := by decide
  have hdescent : baseEnd_1241639 < baseStart_1241639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241675 : List Nat := [1, 1, 1, 1, 3, 1, 6, 7]
def baseStart_1241675 : Nat := 118140960795 + 1241675 * 2 ^ 59
def prefixEnd_1241675 : Nat := 4983230072969 + 3 ^ 40 * 1241675 * 2
def baseEnd_1241675 : Nat := 94455717284671803637355

theorem tailTrace_1241675 : CollatzResearch.WordTrace tailWord_1241675 prefixEnd_1241675 94455717284671803637355 := by
  unfold tailWord_1241675
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287607776631011052054479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30191738517754007368036319 45287607776631011052054479)
  ·
    refine ⟨67931411664946516578081719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45287607776631011052054479 67931411664946516578081719)
    ·
      refine ⟨101897117497419774867122579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67931411664946516578081719 101897117497419774867122579)
      ·
        refine ⟨152845676246129662300683869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101897117497419774867122579 152845676246129662300683869)
        ·
          refine ⟨57317128592298623362756451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152845676246129662300683869 57317128592298623362756451)
          ·
            refine ⟨85975692888447935044134677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57317128592298623362756451 85975692888447935044134677)
            ·
              refine ⟨4030110604145996955193813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 85975692888447935044134677 4030110604145996955193813)
              ·
                refine ⟨94455717284671803637355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4030110604145996955193813 94455717284671803637355)
                ·
                  rfl

theorem cell21_1241675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_1241675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241675 prefixEnd_1241675 := by exact prefixLift 1241675
  have htrace : WordTrace (prefixWord ++ tailWord_1241675) baseStart_1241675 baseEnd_1241675 := by
    simpa [prefixWord, tailWord_1241675, baseEnd_1241675] using wordTrace_append hprefix tailTrace_1241675
  have hstable : (prefixWord ++ tailWord_1241675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241675).length < 2 ^ (prefixWord ++ tailWord_1241675).sum := by decide
  have hdescent : baseEnd_1241675 < baseStart_1241675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241692 : List Nat := [2, 2, 4, 1, 3, 9]
def baseStart_1241692 : Nat := 118140960795 + 1241692 * 2 ^ 59
def prefixEnd_1241692 : Nat := 4983230072969 + 3 ^ 40 * 1241692 * 2
def baseEnd_1241692 : Nat := 10495223388356561449211

theorem tailTrace_1241692 : CollatzResearch.WordTrace tailWord_1241692 prefixEnd_1241692 10495223388356561449211 := by
  unfold tailWord_1241692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644113908784711477711665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30192151878379615303615553 22644113908784711477711665)
  ·
    refine ⟨16983085431588533608283749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22644113908784711477711665 16983085431588533608283749)
    ·
      refine ⟨3184328518422850051553203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16983085431588533608283749 3184328518422850051553203)
      ·
        refine ⟨4776492777634275077329805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184328518422850051553203 4776492777634275077329805)
        ·
          refine ⟨1791184791612853153998677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4776492777634275077329805 1791184791612853153998677)
          ·
            refine ⟨10495223388356561449211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1791184791612853153998677 10495223388356561449211)
            ·
              rfl

theorem cell21_1241692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 9].length) (baseStart_1241692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241692 prefixEnd_1241692 := by exact prefixLift 1241692
  have htrace : WordTrace (prefixWord ++ tailWord_1241692) baseStart_1241692 baseEnd_1241692 := by
    simpa [prefixWord, tailWord_1241692, baseEnd_1241692] using wordTrace_append hprefix tailTrace_1241692
  have hstable : (prefixWord ++ tailWord_1241692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241692).length < 2 ^ (prefixWord ++ tailWord_1241692).sum := by decide
  have hdescent : baseEnd_1241692 < baseStart_1241692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241698 : List Nat := [3, 3, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1241698 : Nat := 118140960795 + 1241698 * 2 ^ 59
def prefixEnd_1241698 : Nat := 4983230072969 + 3 ^ 40 * 1241698 * 2
def baseEnd_1241698 : Nat := 283372400767372482028685

theorem tailTrace_1241698 : CollatzResearch.WordTrace tailWord_1241698 prefixEnd_1241698 283372400767372482028685 := by
  unfold tailWord_1241698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11322111663886921495035437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30192297770365123986761165 11322111663886921495035437)
  ·
    refine ⟨4245791873957595560638289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11322111663886921495035437 4245791873957595560638289)
    ·
      refine ⟨3184343905468196670478717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4245791873957595560638289 3184343905468196670478717)
      ·
        refine ⟨1194128964550573751429519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3184343905468196670478717 1194128964550573751429519)
        ·
          refine ⟨1791193446825860627144279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194128964550573751429519 1791193446825860627144279)
          ·
            refine ⟨2686790170238790940716419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1791193446825860627144279 2686790170238790940716419)
            ·
              refine ⟨4030185255358186411074629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2686790170238790940716419 4030185255358186411074629)
              ·
                refine ⟨755659735379659952076493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4030185255358186411074629 755659735379659952076493)
                ·
                  refine ⟨283372400767372482028685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755659735379659952076493 283372400767372482028685)
                  ·
                    rfl

theorem cell21_1241698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1241698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241698 prefixEnd_1241698 := by exact prefixLift 1241698
  have htrace : WordTrace (prefixWord ++ tailWord_1241698) baseStart_1241698 baseEnd_1241698 := by
    simpa [prefixWord, tailWord_1241698, baseEnd_1241698] using wordTrace_append hprefix tailTrace_1241698
  have hstable : (prefixWord ++ tailWord_1241698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241698).length < 2 ^ (prefixWord ++ tailWord_1241698).sum := by decide
  have hdescent : baseEnd_1241698 < baseStart_1241698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241709 : List Nat := [1, 5, 1, 1, 3, 3, 1, 6]
def baseStart_1241709 : Nat := 118140960795 + 1241709 * 2 ^ 59
def prefixEnd_1241709 : Nat := 4983230072969 + 3 ^ 40 * 1241709 * 2
def baseEnd_1241709 : Nat := 94458303705746302448443

theorem tailTrace_1241709 : CollatzResearch.WordTrace tailWord_1241709 prefixEnd_1241709 94458303705746302448443 := by
  unfold tailWord_1241709
  simp only [CollatzResearch.WordTrace]
  refine ⟨45288847858507834858792181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30192565239005223239194787 45288847858507834858792181)
  ·
    refine ⟨4245829486735109518011767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45288847858507834858792181 4245829486735109518011767)
    ·
      refine ⟨6368744230102664277017651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245829486735109518011767 6368744230102664277017651)
      ·
        refine ⟨9553116345153996415526477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368744230102664277017651 9553116345153996415526477)
        ·
          refine ⟨3582418629432748655822429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9553116345153996415526477 3582418629432748655822429)
          ·
            refine ⟨1343406986037280745933411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3582418629432748655822429 1343406986037280745933411)
            ·
              refine ⟨2015110479055921118900117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1343406986037280745933411 2015110479055921118900117)
              ·
                refine ⟨94458303705746302448443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2015110479055921118900117 94458303705746302448443)
                ·
                  rfl

theorem cell21_1241709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 6].length) (baseStart_1241709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241709 prefixEnd_1241709 := by exact prefixLift 1241709
  have htrace : WordTrace (prefixWord ++ tailWord_1241709) baseStart_1241709 baseEnd_1241709 := by
    simpa [prefixWord, tailWord_1241709, baseEnd_1241709] using wordTrace_append hprefix tailTrace_1241709
  have hstable : (prefixWord ++ tailWord_1241709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241709).length < 2 ^ (prefixWord ++ tailWord_1241709).sum := by decide
  have hdescent : baseEnd_1241709 < baseStart_1241709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241751 : List Nat := [1, 1, 3, 3, 2, 1, 10]
def baseStart_1241751 : Nat := 118140960795 + 1241751 * 2 ^ 59
def prefixEnd_1241751 : Nat := 4983230072969 + 3 ^ 40 * 1241751 * 2
def baseEnd_1241751 : Nat := 31487166232161796405027

theorem tailTrace_1241751 : CollatzResearch.WordTrace tailWord_1241751 prefixEnd_1241751 31487166232161796405027 := by
  unfold tailWord_1241751
  simp only [CollatzResearch.WordTrace]
  refine ⟨45290379724355676031821107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30193586482903784021214071 45290379724355676031821107)
  ·
    refine ⟨67935569586533514047731661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45290379724355676031821107 67935569586533514047731661)
    ·
      refine ⟨25475838594950067767899373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67935569586533514047731661 25475838594950067767899373)
      ·
        refine ⟨9553439473106275412962265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25475838594950067767899373 9553439473106275412962265)
        ·
          refine ⟨7165079604829706559721699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9553439473106275412962265 7165079604829706559721699)
          ·
            refine ⟨10747619407244559839582549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165079604829706559721699 10747619407244559839582549)
            ·
              refine ⟨31487166232161796405027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10747619407244559839582549 31487166232161796405027)
              ·
                rfl

theorem cell21_1241751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 10].length) (baseStart_1241751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241751 prefixEnd_1241751 := by exact prefixLift 1241751
  have htrace : WordTrace (prefixWord ++ tailWord_1241751) baseStart_1241751 baseEnd_1241751 := by
    simpa [prefixWord, tailWord_1241751, baseEnd_1241751] using wordTrace_append hprefix tailTrace_1241751
  have hstable : (prefixWord ++ tailWord_1241751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241751).length < 2 ^ (prefixWord ++ tailWord_1241751).sum := by decide
  have hdescent : baseEnd_1241751 < baseStart_1241751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241799 : List Nat := [1, 1, 4, 1, 1, 1, 2, 7, 3]
def baseStart_1241799 : Nat := 118140960795 + 1241799 * 2 ^ 59
def prefixEnd_1241799 : Nat := 4983230072969 + 3 ^ 40 * 1241799 * 2
def baseEnd_1241799 : Nat := 283395450343418750845145

theorem tailTrace_1241799 : CollatzResearch.WordTrace tailWord_1241799 prefixEnd_1241799 283395450343418750845145 := by
  unfold tailWord_1241799
  simp only [CollatzResearch.WordTrace]
  refine ⟨45292130428181780229568451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30194753618787853486378967 45292130428181780229568451)
  ·
    refine ⟨67938195642272670344352677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45292130428181780229568451 67938195642272670344352677)
    ·
      refine ⟨12738411682926125689566127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67938195642272670344352677 12738411682926125689566127)
      ·
        refine ⟨19107617524389188534349191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12738411682926125689566127 19107617524389188534349191)
        ·
          refine ⟨28661426286583782801523787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19107617524389188534349191 28661426286583782801523787)
          ·
            refine ⟨42992139429875674202285681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28661426286583782801523787 42992139429875674202285681)
            ·
              refine ⟨32244104572406755651714261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42992139429875674202285681 32244104572406755651714261)
              ·
                refine ⟨755721200915783335587053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32244104572406755651714261 755721200915783335587053)
                ·
                  refine ⟨283395450343418750845145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755721200915783335587053 283395450343418750845145)
                  ·
                    rfl

theorem cell21_1241799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 7, 3].length) (baseStart_1241799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241799 prefixEnd_1241799 := by exact prefixLift 1241799
  have htrace : WordTrace (prefixWord ++ tailWord_1241799) baseStart_1241799 baseEnd_1241799 := by
    simpa [prefixWord, tailWord_1241799, baseEnd_1241799] using wordTrace_append hprefix tailTrace_1241799
  have hstable : (prefixWord ++ tailWord_1241799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241799).length < 2 ^ (prefixWord ++ tailWord_1241799).sum := by decide
  have hdescent : baseEnd_1241799 < baseStart_1241799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241875 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 3]
def baseStart_1241875 : Nat := 118140960795 + 1241875 * 2 ^ 59
def prefixEnd_1241875 : Nat := 4983230072969 + 3 ^ 40 * 1241875 * 2
def baseEnd_1241875 : Nat := 283412794578859507578323

theorem tailTrace_1241875 : CollatzResearch.WordTrace tailWord_1241875 prefixEnd_1241875 283412794578859507578323 := by
  unfold tailWord_1241875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45294902375906445209335079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30196601583937630139556719 45294902375906445209335079)
  ·
    refine ⟨67942353563859667814002619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45294902375906445209335079 67942353563859667814002619)
    ·
      refine ⟨101913530345789501721003929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67942353563859667814002619 101913530345789501721003929)
      ·
        refine ⟨76435147759342126290752947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101913530345789501721003929 76435147759342126290752947)
        ·
          refine ⟨114652721639013189436129421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76435147759342126290752947 114652721639013189436129421)
          ·
            refine ⟨42994770614629946038548533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114652721639013189436129421 42994770614629946038548533)
            ·
              refine ⟨4030759745121557441113925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42994770614629946038548533 4030759745121557441113925)
              ·
                refine ⟨755767452210292020208861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4030759745121557441113925 755767452210292020208861)
                ·
                  refine ⟨283412794578859507578323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 755767452210292020208861 283412794578859507578323)
                  ·
                    rfl

theorem cell21_1241875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 3].length) (baseStart_1241875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241875 prefixEnd_1241875 := by exact prefixLift 1241875
  have htrace : WordTrace (prefixWord ++ tailWord_1241875) baseStart_1241875 baseEnd_1241875 := by
    simpa [prefixWord, tailWord_1241875, baseEnd_1241875] using wordTrace_append hprefix tailTrace_1241875
  have hstable : (prefixWord ++ tailWord_1241875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241875).length < 2 ^ (prefixWord ++ tailWord_1241875).sum := by decide
  have hdescent : baseEnd_1241875 < baseStart_1241875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241889 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 4]
def baseStart_1241889 : Nat := 118140960795 + 1241889 * 2 ^ 59
def prefixEnd_1241889 : Nat := 4983230072969 + 3 ^ 40 * 1241889 * 2
def baseEnd_1241889 : Nat := 283415989569598594344961

theorem tailTrace_1241889 : CollatzResearch.WordTrace tailWord_1241889 prefixEnd_1241889 283415989569598594344961 := by
  unfold tailWord_1241889
  simp only [CollatzResearch.WordTrace]
  refine ⟨45295412997855725600344721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30196941998570483733563147 45295412997855725600344721)
  ·
    refine ⟨33971559748391794200258541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45295412997855725600344721 33971559748391794200258541)
    ·
      refine ⟨12739334905646922825096953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33971559748391794200258541 12739334905646922825096953)
      ·
        refine ⟨9554501179235192118822715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12739334905646922825096953 9554501179235192118822715)
        ·
          refine ⟨14331751768852788178234073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554501179235192118822715 14331751768852788178234073)
          ·
            refine ⟨10748813826639591133675555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14331751768852788178234073 10748813826639591133675555)
            ·
              refine ⟨16123220739959386700513333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748813826639591133675555 16123220739959386700513333)
              ·
                refine ⟨1511551944371192503173125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16123220739959386700513333 1511551944371192503173125)
                ·
                  refine ⟨283415989569598594344961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511551944371192503173125 283415989569598594344961)
                  ·
                    rfl

theorem cell21_1241889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 4].length) (baseStart_1241889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241889 prefixEnd_1241889 := by exact prefixLift 1241889
  have htrace : WordTrace (prefixWord ++ tailWord_1241889) baseStart_1241889 baseEnd_1241889 := by
    simpa [prefixWord, tailWord_1241889, baseEnd_1241889] using wordTrace_append hprefix tailTrace_1241889
  have hstable : (prefixWord ++ tailWord_1241889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241889).length < 2 ^ (prefixWord ++ tailWord_1241889).sum := by decide
  have hdescent : baseEnd_1241889 < baseStart_1241889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1241954 : List Nat := [3, 3, 2, 1, 3, 2, 2, 5]
def baseStart_1241954 : Nat := 118140960795 + 1241954 * 2 ^ 59
def prefixEnd_1241954 : Nat := 4983230072969 + 3 ^ 40 * 1241954 * 2
def baseEnd_1241954 : Nat := 94476941151724308587165

theorem tailTrace_1241954 : CollatzResearch.WordTrace tailWord_1241954 prefixEnd_1241954 94476941151724308587165 := by
  unfold tailWord_1241954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324445935655060425365229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30198522495080161134307277 11324445935655060425365229)
  ·
    refine ⟨4246667225870647659511961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11324445935655060425365229 4246667225870647659511961)
    ·
      refine ⟨3185000419402985744633971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4246667225870647659511961 3185000419402985744633971)
      ·
        refine ⟨4777500629104478616950957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185000419402985744633971 4777500629104478616950957)
        ·
          refine ⟨1791562735914179481356609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4777500629104478616950957 1791562735914179481356609)
          ·
            refine ⟨1343672051935634611017457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1791562735914179481356609 1343672051935634611017457)
            ·
              refine ⟨1007754038951725958263093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1343672051935634611017457 1007754038951725958263093)
              ·
                refine ⟨94476941151724308587165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1007754038951725958263093 94476941151724308587165)
                ·
                  rfl

theorem cell21_1241954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_1241954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1241954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1241954 prefixEnd_1241954 := by exact prefixLift 1241954
  have htrace : WordTrace (prefixWord ++ tailWord_1241954) baseStart_1241954 baseEnd_1241954 := by
    simpa [prefixWord, tailWord_1241954, baseEnd_1241954] using wordTrace_append hprefix tailTrace_1241954
  have hstable : (prefixWord ++ tailWord_1241954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1241954).length < 2 ^ (prefixWord ++ tailWord_1241954).sum := by decide
  have hdescent : baseEnd_1241954 < baseStart_1241954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1241954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242041 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_1242041 : Nat := 118140960795 + 1242041 * 2 ^ 59
def prefixEnd_1242041 : Nat := 4983230072969 + 3 ^ 40 * 1242041 * 2
def baseEnd_1242041 : Nat := 283450678040480107811317

theorem tailTrace_1242041 : CollatzResearch.WordTrace tailWord_1242041 prefixEnd_1242041 283450678040480107811317 := by
  unfold tailWord_1242041
  simp only [CollatzResearch.WordTrace]
  refine ⟨45300956893305055559877977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30200637928870037039918651 45300956893305055559877977)
  ·
    refine ⟨33975717669978791669908483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45300956893305055559877977 33975717669978791669908483)
    ·
      refine ⟨50963576504968187504862725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33975717669978791669908483 50963576504968187504862725)
      ·
        refine ⟨9555670594681535157161761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50963576504968187504862725 9555670594681535157161761)
        ·
          refine ⟨7166752946011151367871321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9555670594681535157161761 7166752946011151367871321)
          ·
            refine ⟨5375064709508363525903491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7166752946011151367871321 5375064709508363525903491)
            ·
              refine ⟨8062597064262545288855237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375064709508363525903491 8062597064262545288855237)
              ·
                refine ⟨1511736949549227241660357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8062597064262545288855237 1511736949549227241660357)
                ·
                  refine ⟨283450678040480107811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511736949549227241660357 283450678040480107811317)
                  ·
                    rfl

theorem cell21_1242041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_1242041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242041 prefixEnd_1242041 := by exact prefixLift 1242041
  have htrace : WordTrace (prefixWord ++ tailWord_1242041) baseStart_1242041 baseEnd_1242041 := by
    simpa [prefixWord, tailWord_1242041, baseEnd_1242041] using wordTrace_append hprefix tailTrace_1242041
  have hstable : (prefixWord ++ tailWord_1242041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242041).length < 2 ^ (prefixWord ++ tailWord_1242041).sum := by decide
  have hdescent : baseEnd_1242041 < baseStart_1242041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242055 : List Nat := [1, 1, 4, 1, 1, 2, 5, 6]
def baseStart_1242055 : Nat := 118140960795 + 1242055 * 2 ^ 59
def prefixEnd_1242055 : Nat := 4983230072969 + 3 ^ 40 * 1242055 * 2
def baseEnd_1242055 : Nat := 94484624343739731525985

theorem tailTrace_1242055 : CollatzResearch.WordTrace tailWord_1242055 prefixEnd_1242055 94484624343739731525985 := by
  unfold tailWord_1242055
  simp only [CollatzResearch.WordTrace]
  refine ⟨45301467515254335950887619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30200978343502890633925079 45301467515254335950887619)
  ·
    refine ⟨67952201272881503926331429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45301467515254335950887619 67952201272881503926331429)
    ·
      refine ⟨12741037738665281986187143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67952201272881503926331429 12741037738665281986187143)
      ·
        refine ⟨19111556607997922979280715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12741037738665281986187143 19111556607997922979280715)
        ·
          refine ⟨28667334911996884468921073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19111556607997922979280715 28667334911996884468921073)
          ·
            refine ⟨21500501183997663351690805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28667334911996884468921073 21500501183997663351690805)
            ·
              refine ⟨2015671985999780939221013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21500501183997663351690805 2015671985999780939221013)
              ·
                refine ⟨94484624343739731525985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2015671985999780939221013 94484624343739731525985)
                ·
                  rfl

theorem cell21_1242055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 6].length) (baseStart_1242055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242055 prefixEnd_1242055 := by exact prefixLift 1242055
  have htrace : WordTrace (prefixWord ++ tailWord_1242055) baseStart_1242055 baseEnd_1242055 := by
    simpa [prefixWord, tailWord_1242055, baseEnd_1242055] using wordTrace_append hprefix tailTrace_1242055
  have hstable : (prefixWord ++ tailWord_1242055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242055).length < 2 ^ (prefixWord ++ tailWord_1242055).sum := by decide
  have hdescent : baseEnd_1242055 < baseStart_1242055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242072 : List Nat := [2, 1, 2, 2, 2, 4, 3, 5]
def baseStart_1242072 : Nat := 118140960795 + 1242072 * 2 ^ 59
def prefixEnd_1242072 : Nat := 4983230072969 + 3 ^ 40 * 1242072 * 2
def baseEnd_1242072 : Nat := 94485917554276980931529

theorem tailTrace_1242072 : CollatzResearch.WordTrace tailWord_1242072 prefixEnd_1242072 94485917554276980931529 := by
  unfold tailWord_1242072
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651043778096373927128235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30201391704128498569504313 22651043778096373927128235)
  ·
    refine ⟨33976565667144560890692353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22651043778096373927128235 33976565667144560890692353)
    ·
      refine ⟨25482424250358420668019265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33976565667144560890692353 25482424250358420668019265)
      ·
        refine ⟨19111818187768815501014449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25482424250358420668019265 19111818187768815501014449)
        ·
          refine ⟨14333863640826611625760837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19111818187768815501014449 14333863640826611625760837)
          ·
            refine ⟨2687599432654989679830157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14333863640826611625760837 2687599432654989679830157)
            ·
              refine ⟨1007849787245621129936309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2687599432654989679830157 1007849787245621129936309)
              ·
                refine ⟨94485917554276980931529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1007849787245621129936309 94485917554276980931529)
                ·
                  rfl

theorem cell21_1242072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 5].length) (baseStart_1242072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242072 prefixEnd_1242072 := by exact prefixLift 1242072
  have htrace : WordTrace (prefixWord ++ tailWord_1242072) baseStart_1242072 baseEnd_1242072 := by
    simpa [prefixWord, tailWord_1242072, baseEnd_1242072] using wordTrace_append hprefix tailTrace_1242072
  have hstable : (prefixWord ++ tailWord_1242072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242072).length < 2 ^ (prefixWord ++ tailWord_1242072).sum := by decide
  have hdescent : baseEnd_1242072 < baseStart_1242072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242148 : List Nat := [2, 3, 1, 4, 1, 3, 7]
def baseStart_1242148 : Nat := 118140960795 + 1242148 * 2 ^ 59
def prefixEnd_1242148 : Nat := 4983230072969 + 3 ^ 40 * 1242148 * 2
def baseEnd_1242148 : Nat := 31497232988696855503085

theorem tailTrace_1242148 : CollatzResearch.WordTrace tailWord_1242148 prefixEnd_1242148 31497232988696855503085 := by
  unfold tailWord_1242148
  simp only [CollatzResearch.WordTrace]
  refine ⟨22652429751958706417011549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30203239669278275222682065 22652429751958706417011549)
  ·
    refine ⟨8494661156984514906379331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22652429751958706417011549 8494661156984514906379331)
    ·
      refine ⟨12741991735476772359568997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494661156984514906379331 12741991735476772359568997)
      ·
        refine ⟨2389123450401894817419187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12741991735476772359568997 2389123450401894817419187)
        ·
          refine ⟨3583685175602842226128781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389123450401894817419187 3583685175602842226128781)
          ·
            refine ⟨1343881940851065834798293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3583685175602842226128781 1343881940851065834798293)
            ·
              refine ⟨31497232988696855503085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1343881940851065834798293 31497232988696855503085)
              ·
                rfl

theorem cell21_1242148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 7].length) (baseStart_1242148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242148 prefixEnd_1242148 := by exact prefixLift 1242148
  have htrace : WordTrace (prefixWord ++ tailWord_1242148) baseStart_1242148 baseEnd_1242148 := by
    simpa [prefixWord, tailWord_1242148, baseEnd_1242148] using wordTrace_append hprefix tailTrace_1242148
  have hstable : (prefixWord ++ tailWord_1242148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242148).length < 2 ^ (prefixWord ++ tailWord_1242148).sum := by decide
  have hdescent : baseEnd_1242148 < baseStart_1242148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242210 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1242210 : Nat := 118140960795 + 1242210 * 2 ^ 59
def prefixEnd_1242210 : Nat := 4983230072969 + 3 ^ 40 * 1242210 * 2
def baseEnd_1242210 : Nat := 283489246142973369494305

theorem tailTrace_1242210 : CollatzResearch.WordTrace tailWord_1242210 prefixEnd_1242210 283489246142973369494305 := by
  unfold tailWord_1242210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326780207423199355695021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30204747219795198281853389 11326780207423199355695021)
  ·
    refine ⟨4247542577783699758385633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11326780207423199355695021 4247542577783699758385633)
    ·
      refine ⟨3185656933337774818789225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4247542577783699758385633 3185656933337774818789225)
      ·
        refine ⟨2389242700003331114091919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3185656933337774818789225 2389242700003331114091919)
        ·
          refine ⟨3583864050004996671137879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389242700003331114091919 3583864050004996671137879)
          ·
            refine ⟨5375796075007495006706819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583864050004996671137879 5375796075007495006706819)
            ·
              refine ⟨8063694112511242510060229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375796075007495006706819 8063694112511242510060229)
              ·
                refine ⟨1511942646095857970636293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8063694112511242510060229 1511942646095857970636293)
                ·
                  refine ⟨283489246142973369494305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1511942646095857970636293 283489246142973369494305)
                  ·
                    rfl

theorem cell21_1242210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1242210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242210 prefixEnd_1242210 := by exact prefixLift 1242210
  have htrace : WordTrace (prefixWord ++ tailWord_1242210) baseStart_1242210 baseEnd_1242210 := by
    simpa [prefixWord, tailWord_1242210, baseEnd_1242210] using wordTrace_append hprefix tailTrace_1242210
  have hstable : (prefixWord ++ tailWord_1242210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242210).length < 2 ^ (prefixWord ++ tailWord_1242210).sum := by decide
  have hdescent : baseEnd_1242210 < baseStart_1242210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242300 : List Nat := [2, 2, 2, 3, 2, 1, 4, 5]
def baseStart_1242300 : Nat := 118140960795 + 1242300 * 2 ^ 59
def prefixEnd_1242300 : Nat := 4983230072969 + 3 ^ 40 * 1242300 * 2
def baseEnd_1242300 : Nat := 94503261789717737664707

theorem tailTrace_1242300 : CollatzResearch.WordTrace tailWord_1242300 prefixEnd_1242300 94503261789717737664707 := by
  unfold tailWord_1242300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22655201699683371396778177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30206935599577828529037569 22655201699683371396778177)
  ·
    refine ⟨16991401274762528547583633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22655201699683371396778177 16991401274762528547583633)
    ·
      refine ⟨12743550956071896410687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16991401274762528547583633 12743550956071896410687725)
      ·
        refine ⟨4778831608526961154007897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12743550956071896410687725 4778831608526961154007897)
        ·
          refine ⟨3584123706395220865505923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778831608526961154007897 3584123706395220865505923)
          ·
            refine ⟨5376185559592831298258885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584123706395220865505923 5376185559592831298258885)
            ·
              refine ⟨1008034792423655868423541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5376185559592831298258885 1008034792423655868423541)
              ·
                refine ⟨94503261789717737664707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008034792423655868423541 94503261789717737664707)
                ·
                  rfl

theorem cell21_1242300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_1242300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242300 prefixEnd_1242300 := by exact prefixLift 1242300
  have htrace : WordTrace (prefixWord ++ tailWord_1242300) baseStart_1242300 baseEnd_1242300 := by
    simpa [prefixWord, tailWord_1242300, baseEnd_1242300] using wordTrace_append hprefix tailTrace_1242300
  have hstable : (prefixWord ++ tailWord_1242300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242300).length < 2 ^ (prefixWord ++ tailWord_1242300).sum := by decide
  have hdescent : baseEnd_1242300 < baseStart_1242300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242466 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1242466 : Nat := 118140960795 + 1242466 * 2 ^ 59
def prefixEnd_1242466 : Nat := 4983230072969 + 3 ^ 40 * 1242466 * 2
def baseEnd_1242466 : Nat := 283547668830773813227115

theorem tailTrace_1242466 : CollatzResearch.WordTrace tailWord_1242466 prefixEnd_1242466 283547668830773813227115 := by
  unfold tailWord_1242466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11329114479191338286024813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30210971944510235429399501 11329114479191338286024813)
  ·
    refine ⟨4248417929696751857259305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11329114479191338286024813 4248417929696751857259305)
    ·
      refine ⟨3186313447272563892944479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4248417929696751857259305 3186313447272563892944479)
      ·
        refine ⟨4779470170908845839416719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186313447272563892944479 4779470170908845839416719)
        ·
          refine ⟨7169205256363268759125079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779470170908845839416719 7169205256363268759125079)
          ·
            refine ⟨10753807884544903138687619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169205256363268759125079 10753807884544903138687619)
            ·
              refine ⟨16130711826817354708031429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10753807884544903138687619 16130711826817354708031429)
              ·
                refine ⟨3024508467528254007755893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16130711826817354708031429 3024508467528254007755893)
                ·
                  refine ⟨283547668830773813227115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024508467528254007755893 283547668830773813227115)
                  ·
                    rfl

theorem cell21_1242466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1242466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242466 prefixEnd_1242466 := by exact prefixLift 1242466
  have htrace : WordTrace (prefixWord ++ tailWord_1242466) baseStart_1242466 baseEnd_1242466 := by
    simpa [prefixWord, tailWord_1242466, baseEnd_1242466] using wordTrace_append hprefix tailTrace_1242466
  have hstable : (prefixWord ++ tailWord_1242466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242466).length < 2 ^ (prefixWord ++ tailWord_1242466).sum := by decide
  have hdescent : baseEnd_1242466 < baseStart_1242466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242500 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_1242500 : Nat := 118140960795 + 1242500 * 2 ^ 59
def prefixEnd_1242500 : Nat := 4983230072969 + 3 ^ 40 * 1242500 * 2
def baseEnd_1242500 : Nat := 283555428093997309660379

theorem tailTrace_1242500 : CollatzResearch.WordTrace tailWord_1242500 prefixEnd_1242500 283555428093997309660379 := by
  unfold tailWord_1242500
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658848999321088475418477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30211798665761451300557969 22658848999321088475418477)
  ·
    refine ⟨8497068374745408178281929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22658848999321088475418477 8497068374745408178281929)
    ·
      refine ⟨6372801281059056133711447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497068374745408178281929 6372801281059056133711447)
      ·
        refine ⟨9559201921588584200567171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6372801281059056133711447 9559201921588584200567171)
        ·
          refine ⟨14338802882382876300850757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559201921588584200567171 14338802882382876300850757)
          ·
            refine ⟨2688525540446789306409517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14338802882382876300850757 2688525540446789306409517)
            ·
              refine ⟨1008197077667545989903569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2688525540446789306409517 1008197077667545989903569)
              ·
                refine ⟨756147808250659492427677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008197077667545989903569 756147808250659492427677)
                ·
                  refine ⟨283555428093997309660379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756147808250659492427677 283555428093997309660379)
                  ·
                    rfl

theorem cell21_1242500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_1242500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242500 prefixEnd_1242500 := by exact prefixLift 1242500
  have htrace : WordTrace (prefixWord ++ tailWord_1242500) baseStart_1242500 baseEnd_1242500 := by
    simpa [prefixWord, tailWord_1242500, baseEnd_1242500] using wordTrace_append hprefix tailTrace_1242500
  have hstable : (prefixWord ++ tailWord_1242500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242500).length < 2 ^ (prefixWord ++ tailWord_1242500).sum := by decide
  have hdescent : baseEnd_1242500 < baseStart_1242500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242618 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 3]
def baseStart_1242618 : Nat := 118140960795 + 1242618 * 2 ^ 59
def prefixEnd_1242618 : Nat := 4983230072969 + 3 ^ 40 * 1242618 * 2
def baseEnd_1242618 : Nat := 283582357301655326693471

theorem tailTrace_1242618 : CollatzResearch.WordTrace tailWord_1242618 prefixEnd_1242618 283582357301655326693471 := by
  unfold tailWord_1242618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330500453053670775908127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30214667874809788735755005 11330500453053670775908127)
  ·
    refine ⟨16995750679580506163862191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11330500453053670775908127 16995750679580506163862191)
    ·
      refine ⟨25493626019370759245793287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16995750679580506163862191 25493626019370759245793287)
      ·
        refine ⟨38240439029056138868689931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25493626019370759245793287 38240439029056138868689931)
        ·
          refine ⟨57360658543584208303034897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38240439029056138868689931 57360658543584208303034897)
          ·
            refine ⟨43020493907688156227276173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57360658543584208303034897 43020493907688156227276173)
            ·
              refine ⟨16132685215383058585228565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43020493907688156227276173 16132685215383058585228565)
              ·
                refine ⟨756219619471080871182589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16132685215383058585228565 756219619471080871182589)
                ·
                  refine ⟨283582357301655326693471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756219619471080871182589 283582357301655326693471)
                  ·
                    rfl

theorem cell21_1242618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 3].length) (baseStart_1242618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242618 prefixEnd_1242618 := by exact prefixLift 1242618
  have htrace : WordTrace (prefixWord ++ tailWord_1242618) baseStart_1242618 baseEnd_1242618 := by
    simpa [prefixWord, tailWord_1242618, baseEnd_1242618] using wordTrace_append hprefix tailTrace_1242618
  have hstable : (prefixWord ++ tailWord_1242618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242618).length < 2 ^ (prefixWord ++ tailWord_1242618).sum := by decide
  have hdescent : baseEnd_1242618 < baseStart_1242618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242632 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_1242632 : Nat := 118140960795 + 1242632 * 2 ^ 59
def prefixEnd_1242632 : Nat := 4983230072969 + 3 ^ 40 * 1242632 * 2
def baseEnd_1242632 : Nat := 283585552292394413460109

theorem tailTrace_1242632 : CollatzResearch.WordTrace tailWord_1242632 prefixEnd_1242632 283585552292394413460109 := by
  unfold tailWord_1242632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661256217081981747321075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30215008289442642329761433 22661256217081981747321075)
  ·
    refine ⟨33991884325622972620981613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22661256217081981747321075 33991884325622972620981613)
    ·
      refine ⟨12746956622108614732868105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33991884325622972620981613 12746956622108614732868105)
      ·
        refine ⟨9560217466581461049651079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12746956622108614732868105 9560217466581461049651079)
        ·
          refine ⟨14340326199872191574476619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9560217466581461049651079 14340326199872191574476619)
          ·
            refine ⟨21510489299808287361714929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14340326199872191574476619 21510489299808287361714929)
            ·
              refine ⟨16132866974856215521286197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21510489299808287361714929 16132866974856215521286197)
              ·
                refine ⟨1512456278892770205120581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16132866974856215521286197 1512456278892770205120581)
                ·
                  refine ⟨283585552292394413460109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512456278892770205120581 283585552292394413460109)
                  ·
                    rfl

theorem cell21_1242632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_1242632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242632 prefixEnd_1242632 := by exact prefixLift 1242632
  have htrace : WordTrace (prefixWord ++ tailWord_1242632) baseStart_1242632 baseEnd_1242632 := by
    simpa [prefixWord, tailWord_1242632, baseEnd_1242632] using wordTrace_append hprefix tailTrace_1242632
  have hstable : (prefixWord ++ tailWord_1242632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242632).length < 2 ^ (prefixWord ++ tailWord_1242632).sum := by decide
  have hdescent : baseEnd_1242632 < baseStart_1242632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242722 : List Nat := [3, 3, 2, 13]
def baseStart_1242722 : Nat := 118140960795 + 1242722 * 2 ^ 59
def prefixEnd_1242722 : Nat := 4983230072969 + 3 ^ 40 * 1242722 * 2
def baseEnd_1242722 : Nat := 1167103257278083361975

theorem tailTrace_1242722 : CollatzResearch.WordTrace tailWord_1242722 prefixEnd_1242722 1167103257278083361975 := by
  unfold tailWord_1242722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331448750959477216354605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30217196669225272576945613 11331448750959477216354605)
  ·
    refine ⟨4249293281609803956132977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11331448750959477216354605 4249293281609803956132977)
    ·
      refine ⟨3186969961207352967099733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4249293281609803956132977 3186969961207352967099733)
      ·
        refine ⟨1167103257278083361975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3186969961207352967099733 1167103257278083361975)
        ·
          rfl

theorem cell21_1242722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 13].length) (baseStart_1242722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242722 prefixEnd_1242722 := by exact prefixLift 1242722
  have htrace : WordTrace (prefixWord ++ tailWord_1242722) baseStart_1242722 baseEnd_1242722 := by
    simpa [prefixWord, tailWord_1242722, baseEnd_1242722] using wordTrace_append hprefix tailTrace_1242722
  have hstable : (prefixWord ++ tailWord_1242722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242722).length < 2 ^ (prefixWord ++ tailWord_1242722).sum := by decide
  have hdescent : baseEnd_1242722 < baseStart_1242722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242725 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_1242725 : Nat := 118140960795 + 1242725 * 2 ^ 59
def prefixEnd_1242725 : Nat := 4983230072969 + 3 ^ 40 * 1242725 * 2
def baseEnd_1242725 : Nat := 283606776159446918409919

theorem tailTrace_1242725 : CollatzResearch.WordTrace tailWord_1242725 prefixEnd_1242725 283606776159446918409919 := by
  unfold tailWord_1242725
  simp only [CollatzResearch.WordTrace]
  refine ⟨45325904422827040377777629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30217269615218026918518419 45325904422827040377777629)
  ·
    refine ⟨16997214158560140141666611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45325904422827040377777629 16997214158560140141666611)
    ·
      refine ⟨25495821237840210212499917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16997214158560140141666611 25495821237840210212499917)
      ·
        refine ⟨9560932964190078829687469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25495821237840210212499917 9560932964190078829687469)
        ·
          refine ⟨3585349861571279561132801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9560932964190078829687469 3585349861571279561132801)
          ·
            refine ⟨2689012396178459670849601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585349861571279561132801 2689012396178459670849601)
            ·
              refine ⟨2016759297133844753137201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689012396178459670849601 2016759297133844753137201)
              ·
                refine ⟨1512569472850383564852901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016759297133844753137201 1512569472850383564852901)
                ·
                  refine ⟨283606776159446918409919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1512569472850383564852901 283606776159446918409919)
                  ·
                    rfl

theorem cell21_1242725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_1242725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242725 prefixEnd_1242725 := by exact prefixLift 1242725
  have htrace : WordTrace (prefixWord ++ tailWord_1242725) baseStart_1242725 baseEnd_1242725 := by
    simpa [prefixWord, tailWord_1242725, baseEnd_1242725] using wordTrace_append hprefix tailTrace_1242725
  have hstable : (prefixWord ++ tailWord_1242725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242725).length < 2 ^ (prefixWord ++ tailWord_1242725).sum := by decide
  have hdescent : baseEnd_1242725 < baseStart_1242725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242728 : List Nat := [2, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_1242728 : Nat := 118140960795 + 1242728 * 2 ^ 59
def prefixEnd_1242728 : Nat := 4983230072969 + 3 ^ 40 * 1242728 * 2
def baseEnd_1242728 : Nat := 283607460800319579859913

theorem tailTrace_1242728 : CollatzResearch.WordTrace tailWord_1242728 prefixEnd_1242728 283607460800319579859913 := by
  unfold tailWord_1242728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663006920908085945068419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30217342561210781260091225 22663006920908085945068419)
  ·
    refine ⟨33994510381362128917602629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22663006920908085945068419 33994510381362128917602629)
    ·
      refine ⟨6373970696505399172050493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33994510381362128917602629 6373970696505399172050493)
      ·
        refine ⟨2390239011189524689518935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6373970696505399172050493 2390239011189524689518935)
        ·
          refine ⟨3585358516784287034278403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390239011189524689518935 3585358516784287034278403)
          ·
            refine ⟨5378037775176430551417605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585358516784287034278403 5378037775176430551417605)
            ·
              refine ⟨1008382082845580728390801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5378037775176430551417605 1008382082845580728390801)
              ·
                refine ⟨756286562134185546293101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008382082845580728390801 756286562134185546293101)
                ·
                  refine ⟨283607460800319579859913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756286562134185546293101 283607460800319579859913)
                  ·
                    rfl

theorem cell21_1242728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_1242728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242728 prefixEnd_1242728 := by exact prefixLift 1242728
  have htrace : WordTrace (prefixWord ++ tailWord_1242728) baseStart_1242728 baseEnd_1242728 := by
    simpa [prefixWord, tailWord_1242728, baseEnd_1242728] using wordTrace_append hprefix tailTrace_1242728
  have hstable : (prefixWord ++ tailWord_1242728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242728).length < 2 ^ (prefixWord ++ tailWord_1242728).sum := by decide
  have hdescent : baseEnd_1242728 < baseStart_1242728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242753 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 7]
def baseStart_1242753 : Nat := 118140960795 + 1242753 * 2 ^ 59
def prefixEnd_1242753 : Nat := 4983230072969 + 3 ^ 40 * 1242753 * 2
def baseEnd_1242753 : Nat := 283613166140925091943195

theorem tailTrace_1242753 : CollatzResearch.WordTrace tailWord_1242753 prefixEnd_1242753 283613166140925091943195 := by
  unfold tailWord_1242753
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326925666725601159796913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30217950444483734106531275 45326925666725601159796913)
  ·
    refine ⟨33995194250044200869847685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45326925666725601159796913 33995194250044200869847685)
    ·
      refine ⟨6374098921883287663096441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33995194250044200869847685 6374098921883287663096441)
      ·
        refine ⟨4780574191412465747322331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374098921883287663096441 4780574191412465747322331)
        ·
          refine ⟨7170861287118698620983497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780574191412465747322331 7170861287118698620983497)
          ·
            refine ⟨5378145965339023965737623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170861287118698620983497 5378145965339023965737623)
            ·
              refine ⟨8067218948008535948606435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378145965339023965737623 8067218948008535948606435)
              ·
                refine ⟨12100828422012803922909653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067218948008535948606435 12100828422012803922909653)
                ·
                  refine ⟨283613166140925091943195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12100828422012803922909653 283613166140925091943195)
                  ·
                    rfl

theorem cell21_1242753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 7].length) (baseStart_1242753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242753 prefixEnd_1242753 := by exact prefixLift 1242753
  have htrace : WordTrace (prefixWord ++ tailWord_1242753) baseStart_1242753 baseEnd_1242753 := by
    simpa [prefixWord, tailWord_1242753, baseEnd_1242753] using wordTrace_append hprefix tailTrace_1242753
  have hstable : (prefixWord ++ tailWord_1242753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242753).length < 2 ^ (prefixWord ++ tailWord_1242753).sum := by decide
  have hdescent : baseEnd_1242753 < baseStart_1242753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242756 : List Nat := [2, 3, 2, 1, 4, 1, 3, 5]
def baseStart_1242756 : Nat := 118140960795 + 1242756 * 2 ^ 59
def prefixEnd_1242756 : Nat := 4983230072969 + 3 ^ 40 * 1242756 * 2
def baseEnd_1242756 : Nat := 94537950260599251131063

theorem tailTrace_1242756 : CollatzResearch.WordTrace tailWord_1242756 prefixEnd_1242756 94537950260599251131063 := by
  unfold tailWord_1242756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663517542857366336078061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30218023390476488448104081 22663517542857366336078061)
  ·
    refine ⟨8498819078571512376029273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22663517542857366336078061 8498819078571512376029273)
    ·
      refine ⟨6374114308928634282021955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8498819078571512376029273 6374114308928634282021955)
      ·
        refine ⟨9561171463392951423032933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6374114308928634282021955 9561171463392951423032933)
        ·
          refine ⟨1792719649386178391818675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9561171463392951423032933 1792719649386178391818675)
          ·
            refine ⟨2689079474079267587728013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792719649386178391818675 2689079474079267587728013)
            ·
              refine ⟨1008404802779725345398005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2689079474079267587728013 1008404802779725345398005)
              ·
                refine ⟨94537950260599251131063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1008404802779725345398005 94537950260599251131063)
                ·
                  rfl

theorem cell21_1242756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_1242756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242756 prefixEnd_1242756 := by exact prefixLift 1242756
  have htrace : WordTrace (prefixWord ++ tailWord_1242756) baseStart_1242756 baseEnd_1242756 := by
    simpa [prefixWord, tailWord_1242756, baseEnd_1242756] using wordTrace_append hprefix tailTrace_1242756
  have hstable : (prefixWord ++ tailWord_1242756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242756).length < 2 ^ (prefixWord ++ tailWord_1242756).sum := by decide
  have hdescent : baseEnd_1242756 < baseStart_1242756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242784 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 6]
def baseStart_1242784 : Nat := 118140960795 + 1242784 * 2 ^ 59
def prefixEnd_1242784 : Nat := 4983230072969 + 3 ^ 40 * 1242784 * 2
def baseEnd_1242784 : Nat := 283620240763275926926465

theorem tailTrace_1242784 : CollatzResearch.WordTrace tailWord_1242784 prefixEnd_1242784 283620240763275926926465 := by
  unfold tailWord_1242784
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664028164806646727087703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30218704219742195636116937 22664028164806646727087703)
  ·
    refine ⟨33996042247209970090631555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22664028164806646727087703 33996042247209970090631555)
    ·
      refine ⟨50994063370814955135947333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33996042247209970090631555 50994063370814955135947333)
      ·
        refine ⟨9561386882027804087990125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50994063370814955135947333 9561386882027804087990125)
        ·
          refine ⟨3585520080760426532996297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9561386882027804087990125 3585520080760426532996297)
          ·
            refine ⟨2689140060570319899747223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585520080760426532996297 2689140060570319899747223)
            ·
              refine ⟨4033710090855479849620835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689140060570319899747223 4033710090855479849620835)
              ·
                refine ⟨6050565136283219774431253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033710090855479849620835 6050565136283219774431253)
                ·
                  refine ⟨283620240763275926926465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6050565136283219774431253 283620240763275926926465)
                  ·
                    rfl

theorem cell21_1242784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 6].length) (baseStart_1242784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242784 prefixEnd_1242784 := by exact prefixLift 1242784
  have htrace : WordTrace (prefixWord ++ tailWord_1242784) baseStart_1242784 baseEnd_1242784 := by
    simpa [prefixWord, tailWord_1242784, baseEnd_1242784] using wordTrace_append hprefix tailTrace_1242784
  have hstable : (prefixWord ++ tailWord_1242784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242784).length < 2 ^ (prefixWord ++ tailWord_1242784).sum := by decide
  have hdescent : baseEnd_1242784 < baseStart_1242784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1242838 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 3]
def baseStart_1242838 : Nat := 118140960795 + 1242838 * 2 ^ 59
def prefixEnd_1242838 : Nat := 4983230072969 + 3 ^ 40 * 1242838 * 2
def baseEnd_1242838 : Nat := 283632564298983833026355

theorem tailTrace_1242838 : CollatzResearch.WordTrace tailWord_1242838 prefixEnd_1242838 283632564298983833026355 := by
  unfold tailWord_1242838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2833126616963603792290073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30220017247611773784427445 2833126616963603792290073)
  ·
    refine ⟨2124844962722702844217555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2833126616963603792290073 2124844962722702844217555)
    ·
      refine ⟨3187267444084054266326333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124844962722702844217555 3187267444084054266326333)
      ·
        refine ⟨1195225291531520349872375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3187267444084054266326333 1195225291531520349872375)
        ·
          refine ⟨1792837937297280524808563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195225291531520349872375 1792837937297280524808563)
          ·
            refine ⟨2689256905945920787212845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792837937297280524808563 2689256905945920787212845)
            ·
              refine ⟨1008471339729720295204817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2689256905945920787212845 1008471339729720295204817)
              ·
                refine ⟨756353504797290221403613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008471339729720295204817 756353504797290221403613)
                ·
                  refine ⟨283632564298983833026355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756353504797290221403613 283632564298983833026355)
                  ·
                    rfl

theorem cell21_1242838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_1242838 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1242838 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1242838 prefixEnd_1242838 := by exact prefixLift 1242838
  have htrace : WordTrace (prefixWord ++ tailWord_1242838) baseStart_1242838 baseEnd_1242838 := by
    simpa [prefixWord, tailWord_1242838, baseEnd_1242838] using wordTrace_append hprefix tailTrace_1242838
  have hstable : (prefixWord ++ tailWord_1242838).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1242838).length < 2 ^ (prefixWord ++ tailWord_1242838).sum := by decide
  have hdescent : baseEnd_1242838 < baseStart_1242838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1242838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243015 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 5]
def baseStart_1243015 : Nat := 118140960795 + 1243015 * 2 ^ 59
def prefixEnd_1243015 : Nat := 4983230072969 + 3 ^ 40 * 1243015 * 2
def baseEnd_1243015 : Nat := 283672958110470858575993

theorem tailTrace_1243015 : CollatzResearch.WordTrace tailWord_1243015 prefixEnd_1243015 283672958110470858575993 := by
  unfold tailWord_1243015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45336481591776419905834499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30224321061184279937222999 45336481591776419905834499)
  ·
    refine ⟨68004722387664629858751749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45336481591776419905834499 68004722387664629858751749)
    ·
      refine ⟨12750885447687118098515953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68004722387664629858751749 12750885447687118098515953)
      ·
        refine ⟨9563164085765338573886965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12750885447687118098515953 9563164085765338573886965)
        ·
          refine ⟨896546633040500491301903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9563164085765338573886965 896546633040500491301903)
          ·
            refine ⟨1344819949560750736952855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896546633040500491301903 1344819949560750736952855)
            ·
              refine ⟨2017229924341126105429283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344819949560750736952855 2017229924341126105429283)
              ·
                refine ⟨3025844886511689158143925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017229924341126105429283 3025844886511689158143925)
                ·
                  refine ⟨283672958110470858575993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3025844886511689158143925 283672958110470858575993)
                  ·
                    rfl

theorem cell21_1243015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 5].length) (baseStart_1243015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243015 prefixEnd_1243015 := by exact prefixLift 1243015
  have htrace : WordTrace (prefixWord ++ tailWord_1243015) baseStart_1243015 baseEnd_1243015 := by
    simpa [prefixWord, tailWord_1243015, baseEnd_1243015] using wordTrace_append hprefix tailTrace_1243015
  have hstable : (prefixWord ++ tailWord_1243015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243015).length < 2 ^ (prefixWord ++ tailWord_1243015).sum := by decide
  have hdescent : baseEnd_1243015 < baseStart_1243015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243040 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_1243040 : Nat := 118140960795 + 1243040 * 2 ^ 59
def prefixEnd_1243040 : Nat := 4983230072969 + 3 ^ 40 * 1243040 * 2
def baseEnd_1243040 : Nat := 283678663451076370659275

theorem tailTrace_1243040 : CollatzResearch.WordTrace tailWord_1243040 prefixEnd_1243040 283678663451076370659275 := by
  unfold tailWord_1243040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22668696708342924587747287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30224928944457232783663049 22668696708342924587747287)
  ·
    refine ⟨34003045062514386881620931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22668696708342924587747287 34003045062514386881620931)
    ·
      refine ⟨51004567593771580322431397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34003045062514386881620931 51004567593771580322431397)
      ·
        refine ⟨9563356423832171310455887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51004567593771580322431397 9563356423832171310455887)
        ·
          refine ⟨14345034635748256965683831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9563356423832171310455887 14345034635748256965683831)
          ·
            refine ⟨21517551953622385448525747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14345034635748256965683831 21517551953622385448525747)
            ·
              refine ⟨32276327930433578172788621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21517551953622385448525747 32276327930433578172788621)
              ·
                refine ⟨12103622973912591814795733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32276327930433578172788621 12103622973912591814795733)
                ·
                  refine ⟨283678663451076370659275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12103622973912591814795733 283678663451076370659275)
                  ·
                    rfl

theorem cell21_1243040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_1243040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243040 prefixEnd_1243040 := by exact prefixLift 1243040
  have htrace : WordTrace (prefixWord ++ tailWord_1243040) baseStart_1243040 baseEnd_1243040 := by
    simpa [prefixWord, tailWord_1243040, baseEnd_1243040] using wordTrace_append hprefix tailTrace_1243040
  have hstable : (prefixWord ++ tailWord_1243040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243040).length < 2 ^ (prefixWord ++ tailWord_1243040).sum := by decide
  have hdescent : baseEnd_1243040 < baseStart_1243040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243060 : List Nat := [2, 5, 2, 1, 3, 8]
def baseStart_1243060 : Nat := 118140960795 + 1243060 * 2 ^ 59
def prefixEnd_1243060 : Nat := 4983230072969 + 3 ^ 40 * 1243060 * 2
def baseEnd_1243060 : Nat := 10506786211983732604663

theorem tailTrace_1243060 : CollatzResearch.WordTrace tailWord_1243060 prefixEnd_1243060 10506786211983732604663 := by
  unfold tailWord_1243060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669061438306696295611317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30225415251075595060815089 22669061438306696295611317)
  ·
    refine ⟨2125224509841252777713561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22669061438306696295611317 2125224509841252777713561)
    ·
      refine ⟨1593918382380939583285171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2125224509841252777713561 1593918382380939583285171)
      ·
        refine ⟨2390877573571409374927757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593918382380939583285171 2390877573571409374927757)
        ·
          refine ⟨896579090089278515597909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2390877573571409374927757 896579090089278515597909)
          ·
            refine ⟨10506786211983732604663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 896579090089278515597909 10506786211983732604663)
            ·
              rfl

theorem cell21_1243060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 8].length) (baseStart_1243060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243060 prefixEnd_1243060 := by exact prefixLift 1243060
  have htrace : WordTrace (prefixWord ++ tailWord_1243060) baseStart_1243060 baseEnd_1243060 := by
    simpa [prefixWord, tailWord_1243060, baseEnd_1243060] using wordTrace_append hprefix tailTrace_1243060
  have hstable : (prefixWord ++ tailWord_1243060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243060).length < 2 ^ (prefixWord ++ tailWord_1243060).sum := by decide
  have hdescent : baseEnd_1243060 < baseStart_1243060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243178 : List Nat := [3, 1, 4, 1, 2, 1, 9]
def baseStart_1243178 : Nat := 118140960795 + 1243178 * 2 ^ 59
def prefixEnd_1243178 : Nat := 4983230072969 + 3 ^ 40 * 1243178 * 2
def baseEnd_1243178 : Nat := 31523350770135421928777

theorem tailTrace_1243178 : CollatzResearch.WordTrace tailWord_1243178 prefixEnd_1243178 31523350770135421928777 := by
  unfold tailWord_1243178
  simp only [CollatzResearch.WordTrace]
  refine ⟨11335606672546474686004547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30228284460123932496012125 11335606672546474686004547)
  ·
    refine ⟨17003410008819712029006821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11335606672546474686004547 17003410008819712029006821)
    ·
      refine ⟨3188139376653696005438779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17003410008819712029006821 3188139376653696005438779)
      ·
        refine ⟨4782209064980544008158169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188139376653696005438779 4782209064980544008158169)
        ·
          refine ⟨3586656798735408006118627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782209064980544008158169 3586656798735408006118627)
          ·
            refine ⟨5379985198103112009177941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586656798735408006118627 5379985198103112009177941)
            ·
              refine ⟨31523350770135421928777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5379985198103112009177941 31523350770135421928777)
              ·
                rfl

theorem cell21_1243178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 9].length) (baseStart_1243178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243178 prefixEnd_1243178 := by exact prefixLift 1243178
  have htrace : WordTrace (prefixWord ++ tailWord_1243178) baseStart_1243178 baseEnd_1243178 := by
    simpa [prefixWord, tailWord_1243178, baseEnd_1243178] using wordTrace_append hprefix tailTrace_1243178
  have hstable : (prefixWord ++ tailWord_1243178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243178).length < 2 ^ (prefixWord ++ tailWord_1243178).sum := by decide
  have hdescent : baseEnd_1243178 < baseStart_1243178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243237 : List Nat := [1, 3, 1, 3, 2, 11]
def baseStart_1243237 : Nat := 118140960795 + 1243237 * 2 ^ 59
def prefixEnd_1243237 : Nat := 4983230072969 + 3 ^ 40 * 1243237 * 2
def baseEnd_1243237 : Nat := 10508282279075844662057

theorem tailTrace_1243237 : CollatzResearch.WordTrace tailWord_1243237 prefixEnd_1243237 10508282279075844662057 := by
  unfold tailWord_1243237
  simp only [CollatzResearch.WordTrace]
  refine ⟨45344578596972151820415965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30229719064648101213610643 45344578596972151820415965)
  ·
    refine ⟨17004216973864556932655987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45344578596972151820415965 17004216973864556932655987)
    ·
      refine ⟨25506325460796835398983981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17004216973864556932655987 25506325460796835398983981)
      ·
        refine ⟨9564872047798813274618993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25506325460796835398983981 9564872047798813274618993)
        ·
          refine ⟨7173654035849109955964245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9564872047798813274618993 7173654035849109955964245)
          ·
            refine ⟨10508282279075844662057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7173654035849109955964245 10508282279075844662057)
            ·
              rfl

theorem cell21_1243237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 11].length) (baseStart_1243237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243237 prefixEnd_1243237 := by exact prefixLift 1243237
  have htrace : WordTrace (prefixWord ++ tailWord_1243237) baseStart_1243237 baseEnd_1243237 := by
    simpa [prefixWord, tailWord_1243237, baseEnd_1243237] using wordTrace_append hprefix tailTrace_1243237
  have hstable : (prefixWord ++ tailWord_1243237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243237).length < 2 ^ (prefixWord ++ tailWord_1243237).sum := by decide
  have hdescent : baseEnd_1243237 < baseStart_1243237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243420 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1243420 : Nat := 118140960795 + 1243420 * 2 ^ 59
def prefixEnd_1243420 : Nat := 4983230072969 + 3 ^ 40 * 1243420 * 2
def baseEnd_1243420 : Nat := 283765384628280154325165

theorem tailTrace_1243420 : CollatzResearch.WordTrace tailWord_1243420 prefixEnd_1243420 283765384628280154325165 := by
  unfold tailWord_1243420
  simp only [CollatzResearch.WordTrace]
  refine ⟨22675626577654587037163857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30234168770206116049551809 22675626577654587037163857)
  ·
    refine ⟨17006719933240940277872893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22675626577654587037163857 17006719933240940277872893)
    ·
      refine ⟨6377519974965352604202335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17006719933240940277872893 6377519974965352604202335)
      ·
        refine ⟨9566279962448028906303503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6377519974965352604202335 9566279962448028906303503)
        ·
          refine ⟨14349419943672043359455255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9566279962448028906303503 14349419943672043359455255)
          ·
            refine ⟨21524129915508065039182883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14349419943672043359455255 21524129915508065039182883)
            ·
              refine ⟨32286194873262097558774325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21524129915508065039182883 32286194873262097558774325)
              ·
                refine ⟨3026830769368321646135093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32286194873262097558774325 3026830769368321646135093)
                ·
                  refine ⟨283765384628280154325165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3026830769368321646135093 283765384628280154325165)
                  ·
                    rfl

theorem cell21_1243420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1243420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243420 prefixEnd_1243420 := by exact prefixLift 1243420
  have htrace : WordTrace (prefixWord ++ tailWord_1243420) baseStart_1243420 baseEnd_1243420 := by
    simpa [prefixWord, tailWord_1243420, baseEnd_1243420] using wordTrace_append hprefix tailTrace_1243420
  have hstable : (prefixWord ++ tailWord_1243420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243420).length < 2 ^ (prefixWord ++ tailWord_1243420).sum := by decide
  have hdescent : baseEnd_1243420 < baseStart_1243420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243454 : List Nat := [4, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_1243454 : Nat := 118140960795 + 1243454 * 2 ^ 59
def prefixEnd_1243454 : Nat := 4983230072969 + 3 ^ 40 * 1243454 * 2
def baseEnd_1243454 : Nat := 283773143891503650758429

theorem tailTrace_1243454 : CollatzResearch.WordTrace tailWord_1243454 prefixEnd_1243454 283773143891503650758429 := by
  unfold tailWord_1243454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669061654648249735133177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30234995491457331920710277 5669061654648249735133177)
  ·
    refine ⟨4251796240986187301349883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5669061654648249735133177 4251796240986187301349883)
    ·
      refine ⟨6377694361479280952024825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4251796240986187301349883 6377694361479280952024825)
      ·
        refine ⟨4783270771109460714018619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6377694361479280952024825 4783270771109460714018619)
        ·
          refine ⟨7174906156664191071027929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783270771109460714018619 7174906156664191071027929)
          ·
            refine ⟨5381179617498143303270947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7174906156664191071027929 5381179617498143303270947)
            ·
              refine ⟨8071769426247214954906421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381179617498143303270947 8071769426247214954906421)
              ·
                refine ⟨756728383710676402022477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8071769426247214954906421 756728383710676402022477)
                ·
                  refine ⟨283773143891503650758429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756728383710676402022477 283773143891503650758429)
                  ·
                    rfl

theorem cell21_1243454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_1243454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243454 prefixEnd_1243454 := by exact prefixLift 1243454
  have htrace : WordTrace (prefixWord ++ tailWord_1243454) baseStart_1243454 baseEnd_1243454 := by
    simpa [prefixWord, tailWord_1243454, baseEnd_1243454] using wordTrace_append hprefix tailTrace_1243454
  have hstable : (prefixWord ++ tailWord_1243454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243454).length < 2 ^ (prefixWord ++ tailWord_1243454).sum := by decide
  have hdescent : baseEnd_1243454 < baseStart_1243454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243527 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 4]
def baseStart_1243527 : Nat := 118140960795 + 1243527 * 2 ^ 59
def prefixEnd_1243527 : Nat := 4983230072969 + 3 ^ 40 * 1243527 * 2
def baseEnd_1243527 : Nat := 283789803486071746041613

theorem tailTrace_1243527 : CollatzResearch.WordTrace tailWord_1243527 prefixEnd_1243527 283789803486071746041613 := by
  unfold tailWord_1243527
  simp only [CollatzResearch.WordTrace]
  refine ⟨45355155765921531348472835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30236770510614354232315223 45355155765921531348472835)
  ·
    refine ⟨68032733648882297022709253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45355155765921531348472835 68032733648882297022709253)
    ·
      refine ⟨12756137559165430691757985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68032733648882297022709253 12756137559165430691757985)
      ·
        refine ⟨9567103169374073018818489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12756137559165430691757985 9567103169374073018818489)
        ·
          refine ⟨7175327377030554764113867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9567103169374073018818489 7175327377030554764113867)
          ·
            refine ⟨10762991065545832146170801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175327377030554764113867 10762991065545832146170801)
            ·
              refine ⟨8072243299159374109628101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10762991065545832146170801 8072243299159374109628101)
              ·
                refine ⟨1513545618592382645555269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8072243299159374109628101 1513545618592382645555269)
                ·
                  refine ⟨283789803486071746041613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513545618592382645555269 283789803486071746041613)
                  ·
                    rfl

theorem cell21_1243527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 4].length) (baseStart_1243527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243527 prefixEnd_1243527 := by exact prefixLift 1243527
  have htrace : WordTrace (prefixWord ++ tailWord_1243527) baseStart_1243527 baseEnd_1243527 := by
    simpa [prefixWord, tailWord_1243527, baseEnd_1243527] using wordTrace_append hprefix tailTrace_1243527
  have hstable : (prefixWord ++ tailWord_1243527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243527).length < 2 ^ (prefixWord ++ tailWord_1243527).sum := by decide
  have hdescent : baseEnd_1243527 < baseStart_1243527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243544 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_1243544 : Nat := 118140960795 + 1243544 * 2 ^ 59
def prefixEnd_1243544 : Nat := 4983230072969 + 3 ^ 40 * 1243544 * 2
def baseEnd_1243544 : Nat := 283793683117683494258245

theorem tailTrace_1243544 : CollatzResearch.WordTrace tailWord_1243544 prefixEnd_1243544 283793683117683494258245 := by
  unfold tailWord_1243544
  simp only [CollatzResearch.WordTrace]
  refine ⟨22677887903429971625920843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30237183871239962167894457 22677887903429971625920843)
  ·
    refine ⟨34016831855144957438881265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22677887903429971625920843 34016831855144957438881265)
    ·
      refine ⟨25512623891358718079160949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34016831855144957438881265 25512623891358718079160949)
      ·
        refine ⟨2391808489814879819921339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25512623891358718079160949 2391808489814879819921339)
        ·
          refine ⟨3587712734722319729882009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391808489814879819921339 3587712734722319729882009)
          ·
            refine ⟨2690784551041739797411507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587712734722319729882009 2690784551041739797411507)
            ·
              refine ⟨4036176826562609696117261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690784551041739797411507 4036176826562609696117261)
              ·
                refine ⟨1513566309960978636043973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4036176826562609696117261 1513566309960978636043973)
                ·
                  refine ⟨283793683117683494258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513566309960978636043973 283793683117683494258245)
                  ·
                    rfl

theorem cell21_1243544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_1243544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243544 prefixEnd_1243544 := by exact prefixLift 1243544
  have htrace : WordTrace (prefixWord ++ tailWord_1243544) baseStart_1243544 baseEnd_1243544 := by
    simpa [prefixWord, tailWord_1243544, baseEnd_1243544] using wordTrace_append hprefix tailTrace_1243544
  have hstable : (prefixWord ++ tailWord_1243544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243544).length < 2 ^ (prefixWord ++ tailWord_1243544).sum := by decide
  have hdescent : baseEnd_1243544 < baseStart_1243544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243631 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_1243631 : Nat := 118140960795 + 1243631 * 2 ^ 59
def prefixEnd_1243631 : Nat := 4983230072969 + 3 ^ 40 * 1243631 * 2
def baseEnd_1243631 : Nat := 283813537702990676308067

theorem tailTrace_1243631 : CollatzResearch.WordTrace tailWord_1243631 prefixEnd_1243631 283813537702990676308067 := by
  unfold tailWord_1243631
  simp only [CollatzResearch.WordTrace]
  refine ⟨45358948957544757110258747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30239299305029838073505831 45358948957544757110258747)
  ·
    refine ⟨68038423436317135665388121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45358948957544757110258747 68038423436317135665388121)
    ·
      refine ⟨51028817577237851749041091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68038423436317135665388121 51028817577237851749041091)
      ·
        refine ⟨76543226365856777623561637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51028817577237851749041091 76543226365856777623561637)
        ·
          refine ⟨14351854943598145804417807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76543226365856777623561637 14351854943598145804417807)
          ·
            refine ⟨21527782415397218706626711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14351854943598145804417807 21527782415397218706626711)
            ·
              refine ⟨32291673623095828059940067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21527782415397218706626711 32291673623095828059940067)
              ·
                refine ⟨48437510434643742089910101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32291673623095828059940067 48437510434643742089910101)
                ·
                  refine ⟨283813537702990676308067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48437510434643742089910101 283813537702990676308067)
                  ·
                    rfl

theorem cell21_1243631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_1243631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243631 prefixEnd_1243631 := by exact prefixLift 1243631
  have htrace : WordTrace (prefixWord ++ tailWord_1243631) baseStart_1243631 baseEnd_1243631 := by
    simpa [prefixWord, tailWord_1243631, baseEnd_1243631] using wordTrace_append hprefix tailTrace_1243631
  have hstable : (prefixWord ++ tailWord_1243631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243631).length < 2 ^ (prefixWord ++ tailWord_1243631).sum := by decide
  have hdescent : baseEnd_1243631 < baseStart_1243631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243634 : List Nat := [3, 2, 1, 4, 2, 1, 8]
def baseStart_1243634 : Nat := 118140960795 + 1243634 * 2 ^ 59
def prefixEnd_1243634 : Nat := 4983230072969 + 3 ^ 40 * 1243634 * 2
def baseEnd_1243634 : Nat := 31534913593762593084229

theorem tailTrace_1243634 : CollatzResearch.WordTrace tailWord_1243634 prefixEnd_1243634 31534913593762593084229 := by
  unfold tailWord_1243634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11339764594133472155654489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30239372251022592415078637 11339764594133472155654489)
  ·
    refine ⟨8504823445600104116740867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11339764594133472155654489 8504823445600104116740867)
    ·
      refine ⟨12757235168400156175111301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504823445600104116740867 12757235168400156175111301)
      ·
        refine ⟨2391981594075029282833369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12757235168400156175111301 2391981594075029282833369)
        ·
          refine ⟨1793986195556271962125027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2391981594075029282833369 1793986195556271962125027)
          ·
            refine ⟨2690979293334407943187541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793986195556271962125027 2690979293334407943187541)
            ·
              refine ⟨31534913593762593084229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2690979293334407943187541 31534913593762593084229)
              ·
                rfl

theorem cell21_1243634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 8].length) (baseStart_1243634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243634 prefixEnd_1243634 := by exact prefixLift 1243634
  have htrace : WordTrace (prefixWord ++ tailWord_1243634) baseStart_1243634 baseEnd_1243634 := by
    simpa [prefixWord, tailWord_1243634, baseEnd_1243634] using wordTrace_append hprefix tailTrace_1243634
  have hstable : (prefixWord ++ tailWord_1243634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243634).length < 2 ^ (prefixWord ++ tailWord_1243634).sum := by decide
  have hdescent : baseEnd_1243634 < baseStart_1243634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243668 : List Nat := [2, 4, 3, 1, 1, 3, 2, 5]
def baseStart_1243668 : Nat := 118140960795 + 1243668 * 2 ^ 59
def prefixEnd_1243668 : Nat := 4983230072969 + 3 ^ 40 * 1243668 * 2
def baseEnd_1243668 : Nat := 94607327202362278063775

theorem tailTrace_1243668 : CollatzResearch.WordTrace tailWord_1243668 prefixEnd_1243668 94607327202362278063775 := by
  unfold tailWord_1243668
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680149229205356214677829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30240198972273808286237105 22680149229205356214677829)
  ·
    refine ⟨4252527980476004290252093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22680149229205356214677829 4252527980476004290252093)
    ·
      refine ⟨1594697992678501608844535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4252527980476004290252093 1594697992678501608844535)
      ·
        refine ⟨2392046989017752413266803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594697992678501608844535 2392046989017752413266803)
        ·
          refine ⟨3588070483526628619900205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392046989017752413266803 3588070483526628619900205)
          ·
            refine ⟨1345526431322485732462577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3588070483526628619900205 1345526431322485732462577)
            ·
              refine ⟨1009144823491864299346933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345526431322485732462577 1009144823491864299346933)
              ·
                refine ⟨94607327202362278063775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1009144823491864299346933 94607327202362278063775)
                ·
                  rfl

theorem cell21_1243668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 2, 5].length) (baseStart_1243668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243668 prefixEnd_1243668 := by exact prefixLift 1243668
  have htrace : WordTrace (prefixWord ++ tailWord_1243668) baseStart_1243668 baseEnd_1243668 := by
    simpa [prefixWord, tailWord_1243668, baseEnd_1243668] using wordTrace_append hprefix tailTrace_1243668
  have hstable : (prefixWord ++ tailWord_1243668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243668).length < 2 ^ (prefixWord ++ tailWord_1243668).sum := by decide
  have hdescent : baseEnd_1243668 < baseStart_1243668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243713 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 4]
def baseStart_1243713 : Nat := 118140960795 + 1243713 * 2 ^ 59
def prefixEnd_1243713 : Nat := 4983230072969 + 3 ^ 40 * 1243713 * 2
def baseEnd_1243713 : Nat := 283832251220176755941233

theorem tailTrace_1243713 : CollatzResearch.WordTrace tailWord_1243713 prefixEnd_1243713 283832251220176755941233 := by
  unfold tailWord_1243713
  simp only [CollatzResearch.WordTrace]
  refine ⟨45361939743247685114743793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30241293162165123409829195 45361939743247685114743793)
  ·
    refine ⟨34021454807435763836057845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45361939743247685114743793 34021454807435763836057845)
    ·
      refine ⟨3189511388197102859630423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34021454807435763836057845 3189511388197102859630423)
      ·
        refine ⟨4784267082295654289445635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189511388197102859630423 4784267082295654289445635)
        ·
          refine ⟨7176400623443481434168453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784267082295654289445635 7176400623443481434168453)
          ·
            refine ⟨1345575116895652768906585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7176400623443481434168453 1345575116895652768906585)
            ·
              refine ⟨1009181337671739576679939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345575116895652768906585 1009181337671739576679939)
              ·
                refine ⟨1513772006507609365019909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009181337671739576679939 1513772006507609365019909)
                ·
                  refine ⟨283832251220176755941233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1513772006507609365019909 283832251220176755941233)
                  ·
                    rfl

theorem cell21_1243713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 4].length) (baseStart_1243713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243713 prefixEnd_1243713 := by exact prefixLift 1243713
  have htrace : WordTrace (prefixWord ++ tailWord_1243713) baseStart_1243713 baseEnd_1243713 := by
    simpa [prefixWord, tailWord_1243713, baseEnd_1243713] using wordTrace_append hprefix tailTrace_1243713
  have hstable : (prefixWord ++ tailWord_1243713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243713).length < 2 ^ (prefixWord ++ tailWord_1243713).sum := by decide
  have hdescent : baseEnd_1243713 < baseStart_1243713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243758 : List Nat := [4, 1, 2, 2, 2, 2, 1, 4, 3]
def baseStart_1243758 : Nat := 118140960795 + 1243758 * 2 ^ 59
def prefixEnd_1243758 : Nat := 4983230072969 + 3 ^ 40 * 1243758 * 2
def baseEnd_1243758 : Nat := 283842520833266677691141

theorem tailTrace_1243758 : CollatzResearch.WordTrace tailWord_1243758 prefixEnd_1243758 283842520833266677691141 := by
  unfold tailWord_1243758
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670447628510582225016491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30242387352056438533421285 5670447628510582225016491)
  ·
    refine ⟨8505671442765873337524737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5670447628510582225016491 8505671442765873337524737)
    ·
      refine ⟨6379253582074405003143553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8505671442765873337524737 6379253582074405003143553)
      ·
        refine ⟨4784440186555803752357665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6379253582074405003143553 4784440186555803752357665)
        ·
          refine ⟨3588330139916852814268249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784440186555803752357665 3588330139916852814268249)
          ·
            refine ⟨2691247604937639610701187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588330139916852814268249 2691247604937639610701187)
            ·
              refine ⟨4036871407406459416051781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691247604937639610701187 4036871407406459416051781)
              ·
                refine ⟨756913388888711140509709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4036871407406459416051781 756913388888711140509709)
                ·
                  refine ⟨283842520833266677691141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 756913388888711140509709 283842520833266677691141)
                  ·
                    rfl

theorem cell21_1243758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_1243758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243758 prefixEnd_1243758 := by exact prefixLift 1243758
  have htrace : WordTrace (prefixWord ++ tailWord_1243758) baseStart_1243758 baseEnd_1243758 := by
    simpa [prefixWord, tailWord_1243758, baseEnd_1243758] using wordTrace_append hprefix tailTrace_1243758
  have hstable : (prefixWord ++ tailWord_1243758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243758).length < 2 ^ (prefixWord ++ tailWord_1243758).sum := by decide
  have hdescent : baseEnd_1243758 < baseStart_1243758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243769 : List Nat := [1, 2, 1, 3, 3, 2, 3, 6]
def baseStart_1243769 : Nat := 118140960795 + 1243769 * 2 ^ 59
def prefixEnd_1243769 : Nat := 4983230072969 + 3 ^ 40 * 1243769 * 2
def baseEnd_1243769 : Nat := 94615010394377701002595

theorem tailTrace_1243769 : CollatzResearch.WordTrace tailWord_1243769 prefixEnd_1243769 94615010394377701002595 := by
  unfold tailWord_1243769
  simp only [CollatzResearch.WordTrace]
  refine ⟨45363982231044806678782361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30242654820696537785854907 45363982231044806678782361)
  ·
    refine ⟨34022986673283605009086771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45363982231044806678782361 34022986673283605009086771)
    ·
      refine ⟨51034480009925407513630157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34022986673283605009086771 51034480009925407513630157)
      ·
        refine ⟨19137930003722027817611309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51034480009925407513630157 19137930003722027817611309)
        ·
          refine ⟨7176723751395760431604241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19137930003722027817611309 7176723751395760431604241)
          ·
            refine ⟨5382542813546820323703181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7176723751395760431604241 5382542813546820323703181)
            ·
              refine ⟨2018453555080057621388693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5382542813546820323703181 2018453555080057621388693)
              ·
                refine ⟨94615010394377701002595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2018453555080057621388693 94615010394377701002595)
                ·
                  rfl

theorem cell21_1243769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_1243769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243769 prefixEnd_1243769 := by exact prefixLift 1243769
  have htrace : WordTrace (prefixWord ++ tailWord_1243769) baseStart_1243769 baseEnd_1243769 := by
    simpa [prefixWord, tailWord_1243769, baseEnd_1243769] using wordTrace_append hprefix tailTrace_1243769
  have hstable : (prefixWord ++ tailWord_1243769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243769).length < 2 ^ (prefixWord ++ tailWord_1243769).sum := by decide
  have hdescent : baseEnd_1243769 < baseStart_1243769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243876 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 5]
def baseStart_1243876 : Nat := 118140960795 + 1243876 * 2 ^ 59
def prefixEnd_1243876 : Nat := 4983230072969 + 3 ^ 40 * 1243876 * 2
def baseEnd_1243876 : Nat := 283869450040924694724233

theorem tailTrace_1243876 : CollatzResearch.WordTrace tailWord_1243876 prefixEnd_1243876 283869450040924694724233 := by
  unfold tailWord_1243876
  simp only [CollatzResearch.WordTrace]
  refine ⟨22683942420828581976463741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30245256561104775968618321 22683942420828581976463741)
  ·
    refine ⟨8506478407810718241173903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22683942420828581976463741 8506478407810718241173903)
    ·
      refine ⟨12759717611716077361760855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506478407810718241173903 12759717611716077361760855)
      ·
        refine ⟨19139576417574116042641283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12759717611716077361760855 19139576417574116042641283)
        ·
          refine ⟨28709364626361174063961925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19139576417574116042641283 28709364626361174063961925)
          ·
            refine ⟨5383005867442720136992861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28709364626361174063961925 5383005867442720136992861)
            ·
              refine ⟨2018627200291020051372323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5383005867442720136992861 2018627200291020051372323)
              ·
                refine ⟨3027940800436530077058485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018627200291020051372323 3027940800436530077058485)
                ·
                  refine ⟨283869450040924694724233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3027940800436530077058485 283869450040924694724233)
                  ·
                    rfl

theorem cell21_1243876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_1243876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243876 prefixEnd_1243876 := by exact prefixLift 1243876
  have htrace : WordTrace (prefixWord ++ tailWord_1243876) baseStart_1243876 baseEnd_1243876 := by
    simpa [prefixWord, tailWord_1243876, baseEnd_1243876] using wordTrace_append hprefix tailTrace_1243876
  have hstable : (prefixWord ++ tailWord_1243876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243876).length < 2 ^ (prefixWord ++ tailWord_1243876).sum := by decide
  have hdescent : baseEnd_1243876 < baseStart_1243876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243927 : List Nat := [1, 1, 3, 4, 3, 2, 2, 2, 3]
def baseStart_1243927 : Nat := 118140960795 + 1243927 * 2 ^ 59
def prefixEnd_1243927 : Nat := 4983230072969 + 3 ^ 40 * 1243927 * 2
def baseEnd_1243927 : Nat := 283881088935759939374129

theorem tailTrace_1243927 : CollatzResearch.WordTrace tailWord_1243927 prefixEnd_1243927 283881088935759939374129 := by
  unfold tailWord_1243927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45369744964472399663034035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30246496642981599775356023 45369744964472399663034035)
  ·
    refine ⟨68054617446708599494551053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45369744964472399663034035 68054617446708599494551053)
    ·
      refine ⟨25520481542515724810456645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68054617446708599494551053 25520481542515724810456645)
      ·
        refine ⟨4785090289221698401960621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25520481542515724810456645 4785090289221698401960621)
        ·
          refine ⟨1794408858458136900735233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4785090289221698401960621 1794408858458136900735233)
          ·
            refine ⟨1345806643843602675551425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1794408858458136900735233 1345806643843602675551425)
            ·
              refine ⟨1009354982882702006663569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345806643843602675551425 1009354982882702006663569)
              ·
                refine ⟨757016237162026504997677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009354982882702006663569 757016237162026504997677)
                ·
                  refine ⟨283881088935759939374129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757016237162026504997677 283881088935759939374129)
                  ·
                    rfl

theorem cell21_1243927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 3].length) (baseStart_1243927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243927 prefixEnd_1243927 := by exact prefixLift 1243927
  have htrace : WordTrace (prefixWord ++ tailWord_1243927) baseStart_1243927 baseEnd_1243927 := by
    simpa [prefixWord, tailWord_1243927, baseEnd_1243927] using wordTrace_append hprefix tailTrace_1243927
  have hstable : (prefixWord ++ tailWord_1243927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243927).length < 2 ^ (prefixWord ++ tailWord_1243927).sum := by decide
  have hdescent : baseEnd_1243927 < baseStart_1243927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1243938 : List Nat := [3, 3, 1, 1, 2, 4, 1, 6]
def baseStart_1243938 : Nat := 118140960795 + 1243938 * 2 ^ 59
def prefixEnd_1243938 : Nat := 4983230072969 + 3 ^ 40 * 1243938 * 2
def baseEnd_1243938 : Nat := 94627866428542121563591

theorem tailTrace_1243938 : CollatzResearch.WordTrace tailWord_1243938 prefixEnd_1243938 94627866428542121563591 := by
  unfold tailWord_1243938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11342536541858137135421117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30246764111621699027789645 11342536541858137135421117)
  ·
    refine ⟨4253451203196801425782919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11342536541858137135421117 4253451203196801425782919)
    ·
      refine ⟨6380176804795202138674379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253451203196801425782919 6380176804795202138674379)
      ·
        refine ⟨9570265207192803208011569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6380176804795202138674379 9570265207192803208011569)
        ·
          refine ⟨7177698905394602406008677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9570265207192803208011569 7177698905394602406008677)
          ·
            refine ⟨1345818544761487951126627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7177698905394602406008677 1345818544761487951126627)
            ·
              refine ⟨2018727817142231926689941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345818544761487951126627 2018727817142231926689941)
              ·
                refine ⟨94627866428542121563591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2018727817142231926689941 94627866428542121563591)
                ·
                  rfl

theorem cell21_1243938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 6].length) (baseStart_1243938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1243938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1243938 prefixEnd_1243938 := by exact prefixLift 1243938
  have htrace : WordTrace (prefixWord ++ tailWord_1243938) baseStart_1243938 baseEnd_1243938 := by
    simpa [prefixWord, tailWord_1243938, baseEnd_1243938] using wordTrace_append hprefix tailTrace_1243938
  have hstable : (prefixWord ++ tailWord_1243938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1243938).length < 2 ^ (prefixWord ++ tailWord_1243938).sum := by decide
  have hdescent : baseEnd_1243938 < baseStart_1243938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1243938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244011 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 5]
def baseStart_1244011 : Nat := 118140960795 + 1244011 * 2 ^ 59
def prefixEnd_1244011 : Nat := 4983230072969 + 3 ^ 40 * 1244011 * 2
def baseEnd_1244011 : Nat := 283900258880194459973957

theorem tailTrace_1244011 : CollatzResearch.WordTrace tailWord_1244011 prefixEnd_1244011 283900258880194459973957 := by
  unfold tailWord_1244011
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372808696168082009091887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30248539130778721339394591 45372808696168082009091887)
  ·
    refine ⟨68059213044252123013637831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45372808696168082009091887 68059213044252123013637831)
    ·
      refine ⟨102088819566378184520456747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68059213044252123013637831 102088819566378184520456747)
      ·
        refine ⟨153133229349567276780685121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102088819566378184520456747 153133229349567276780685121)
        ·
          refine ⟨114849922012175457585513841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153133229349567276780685121 114849922012175457585513841)
          ·
            refine ⟨86137441509131593189135381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114849922012175457585513841 86137441509131593189135381)
            ·
              refine ⟨4037692570740543430740721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86137441509131593189135381 4037692570740543430740721)
              ·
                refine ⟨3028269428055407573055541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037692570740543430740721 3028269428055407573055541)
                ·
                  refine ⟨283900258880194459973957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3028269428055407573055541 283900258880194459973957)
                  ·
                    rfl

theorem cell21_1244011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_1244011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244011 prefixEnd_1244011 := by exact prefixLift 1244011
  have htrace : WordTrace (prefixWord ++ tailWord_1244011) baseStart_1244011 baseEnd_1244011 := by
    simpa [prefixWord, tailWord_1244011, baseEnd_1244011] using wordTrace_append hprefix tailTrace_1244011
  have hstable : (prefixWord ++ tailWord_1244011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244011).length < 2 ^ (prefixWord ++ tailWord_1244011).sum := by decide
  have hdescent : baseEnd_1244011 < baseStart_1244011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244014 : List Nat := [4, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1244014 : Nat := 118140960795 + 1244014 * 2 ^ 59
def prefixEnd_1244014 : Nat := 4983230072969 + 3 ^ 40 * 1244014 * 2
def baseEnd_1244014 : Nat := 94633647840355707141317

theorem tailTrace_1244014 : CollatzResearch.WordTrace tailWord_1244014 prefixEnd_1244014 94633647840355707141317 := by
  unfold tailWord_1244014
  simp only [CollatzResearch.WordTrace]
  refine ⟨5671614764394651690181387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30248612076771475680967397 5671614764394651690181387)
  ·
    refine ⟨8507422146591977535272081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5671614764394651690181387 8507422146591977535272081)
    ·
      refine ⟨6380566609943983151454061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8507422146591977535272081 6380566609943983151454061)
      ·
        refine ⟨2392712478728993681795273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6380566609943983151454061 2392712478728993681795273)
        ·
          refine ⟨1794534359046745261346455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2392712478728993681795273 1794534359046745261346455)
          ·
            refine ⟨2691801538570117892019683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794534359046745261346455 2691801538570117892019683)
            ·
              refine ⟨4037702307855176838029525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691801538570117892019683 4037702307855176838029525)
              ·
                refine ⟨94633647840355707141317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4037702307855176838029525 94633647840355707141317)
                ·
                  rfl

theorem cell21_1244014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1244014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244014 prefixEnd_1244014 := by exact prefixLift 1244014
  have htrace : WordTrace (prefixWord ++ tailWord_1244014) baseStart_1244014 baseEnd_1244014 := by
    simpa [prefixWord, tailWord_1244014, baseEnd_1244014] using wordTrace_append hprefix tailTrace_1244014
  have hstable : (prefixWord ++ tailWord_1244014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244014).length < 2 ^ (prefixWord ++ tailWord_1244014).sum := by decide
  have hdescent : baseEnd_1244014 < baseStart_1244014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244101 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 10]
def baseStart_1244101 : Nat := 118140960795 + 1244101 * 2 ^ 59
def prefixEnd_1244101 : Nat := 4983230072969 + 3 ^ 40 * 1244101 * 2
def baseEnd_1244101 : Nat := 283920798106374303473773

theorem tailTrace_1244101 : CollatzResearch.WordTrace tailWord_1244101 prefixEnd_1244101 283920798106374303473773 := by
  unfold tailWord_1244101
  simp only [CollatzResearch.WordTrace]
  refine ⟨45376091265842027379868157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30250727510561351586578771 45376091265842027379868157)
  ·
    refine ⟨17016034224690760267450559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45376091265842027379868157 17016034224690760267450559)
    ·
      refine ⟨25524051337036140401175839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016034224690760267450559 25524051337036140401175839)
      ·
        refine ⟨38286077005554210601763759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25524051337036140401175839 38286077005554210601763759)
        ·
          refine ⟨57429115508331315902645639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38286077005554210601763759 57429115508331315902645639)
          ·
            refine ⟨86143673262496973853968459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57429115508331315902645639 86143673262496973853968459)
            ·
              refine ⟨129215509893745460780952689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86143673262496973853968459 129215509893745460780952689)
              ·
                refine ⟨96911632420309095585714517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129215509893745460780952689 96911632420309095585714517)
                ·
                  refine ⟨283920798106374303473773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96911632420309095585714517 283920798106374303473773)
                  ·
                    rfl

theorem cell21_1244101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_1244101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244101 prefixEnd_1244101 := by exact prefixLift 1244101
  have htrace : WordTrace (prefixWord ++ tailWord_1244101) baseStart_1244101 baseEnd_1244101 := by
    simpa [prefixWord, tailWord_1244101, baseEnd_1244101] using wordTrace_append hprefix tailTrace_1244101
  have hstable : (prefixWord ++ tailWord_1244101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244101).length < 2 ^ (prefixWord ++ tailWord_1244101).sum := by decide
  have hdescent : baseEnd_1244101 < baseStart_1244101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244194 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1244194 : Nat := 118140960795 + 1244194 * 2 ^ 59
def prefixEnd_1244194 : Nat := 4983230072969 + 3 ^ 40 * 1244194 * 2
def baseEnd_1244194 : Nat := 283942021973426808423583

theorem tailTrace_1244194 : CollatzResearch.WordTrace tailWord_1244194 prefixEnd_1244194 283942021973426808423583 := by
  unfold tailWord_1244194
  simp only [CollatzResearch.WordTrace]
  refine ⟨11344870813626276065750909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30252988836336736175335757 11344870813626276065750909)
  ·
    refine ⟨4254326555109853524656591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11344870813626276065750909 4254326555109853524656591)
    ·
      refine ⟨6381489832664780286984887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254326555109853524656591 6381489832664780286984887)
      ·
        refine ⟨9572234748997170430477331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6381489832664780286984887 9572234748997170430477331)
        ·
          refine ⟨14358352123495755645715997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9572234748997170430477331 14358352123495755645715997)
          ·
            refine ⟨5384382046310908367143499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14358352123495755645715997 5384382046310908367143499)
            ·
              refine ⟨8076573069466362550715249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384382046310908367143499 8076573069466362550715249)
              ·
                refine ⟨6057429802099771913036437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8076573069466362550715249 6057429802099771913036437)
                ·
                  refine ⟨283942021973426808423583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6057429802099771913036437 283942021973426808423583)
                  ·
                    rfl

theorem cell21_1244194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1244194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244194 prefixEnd_1244194 := by exact prefixLift 1244194
  have htrace : WordTrace (prefixWord ++ tailWord_1244194) baseStart_1244194 baseEnd_1244194 := by
    simpa [prefixWord, tailWord_1244194, baseEnd_1244194] using wordTrace_append hprefix tailTrace_1244194
  have hstable : (prefixWord ++ tailWord_1244194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244194).length < 2 ^ (prefixWord ++ tailWord_1244194).sum := by decide
  have hdescent : baseEnd_1244194 < baseStart_1244194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244256 : List Nat := [2, 1, 1, 3, 2, 2, 2, 5, 3]
def baseStart_1244256 : Nat := 118140960795 + 1244256 * 2 ^ 59
def prefixEnd_1244256 : Nat := 4983230072969 + 3 ^ 40 * 1244256 * 2
def baseEnd_1244256 : Nat := 283956171218128478390123

theorem tailTrace_1244256 : CollatzResearch.WordTrace tailWord_1244256 prefixEnd_1244256 283956171218128478390123 := by
  unfold tailWord_1244256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22690872290140244425880311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30254496386853659234507081 22690872290140244425880311)
  ·
    refine ⟨34036308435210366638820467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22690872290140244425880311 34036308435210366638820467)
    ·
      refine ⟨51054462652815549958230701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34036308435210366638820467 51054462652815549958230701)
      ·
        refine ⟨19145423494805831234336513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51054462652815549958230701 19145423494805831234336513)
        ·
          refine ⟨14359067621104373425752385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19145423494805831234336513 14359067621104373425752385)
          ·
            refine ⟨10769300715828280069314289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14359067621104373425752385 10769300715828280069314289)
            ·
              refine ⟨8076975536871210051985717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10769300715828280069314289 8076975536871210051985717)
              ·
                refine ⟨757216456581675942373661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8076975536871210051985717 757216456581675942373661)
                ·
                  refine ⟨283956171218128478390123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757216456581675942373661 283956171218128478390123)
                  ·
                    rfl

theorem cell21_1244256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 5, 3].length) (baseStart_1244256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244256 prefixEnd_1244256 := by exact prefixLift 1244256
  have htrace : WordTrace (prefixWord ++ tailWord_1244256) baseStart_1244256 baseEnd_1244256 := by
    simpa [prefixWord, tailWord_1244256, baseEnd_1244256] using wordTrace_append hprefix tailTrace_1244256
  have hstable : (prefixWord ++ tailWord_1244256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244256).length < 2 ^ (prefixWord ++ tailWord_1244256).sum := by decide
  have hdescent : baseEnd_1244256 < baseStart_1244256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244366 : List Nat := [4, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_1244366 : Nat := 118140960795 + 1244366 * 2 ^ 59
def prefixEnd_1244366 : Nat := 4983230072969 + 3 ^ 40 * 1244366 * 2
def baseEnd_1244366 : Nat := 283981274716792731556565

theorem tailTrace_1244366 : CollatzResearch.WordTrace tailWord_1244366 prefixEnd_1244366 283981274716792731556565 := by
  unfold tailWord_1244366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673219576235247204783119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30257171073254651758843301 5673219576235247204783119)
  ·
    refine ⟨8509829364352870807174679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5673219576235247204783119 8509829364352870807174679)
    ·
      refine ⟨12764744046529306210762019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8509829364352870807174679 12764744046529306210762019)
      ·
        refine ⟨19147116069793959316143029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764744046529306210762019 19147116069793959316143029)
        ·
          refine ⟨1795042131543183685888409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19147116069793959316143029 1795042131543183685888409)
          ·
            refine ⟨1346281598657387764416307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1795042131543183685888409 1346281598657387764416307)
            ·
              refine ⟨2019422397986081646624461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346281598657387764416307 2019422397986081646624461)
              ·
                refine ⟨757283399244780617484173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2019422397986081646624461 757283399244780617484173)
                ·
                  refine ⟨283981274716792731556565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757283399244780617484173 283981274716792731556565)
                  ·
                    rfl

theorem cell21_1244366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_1244366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244366 prefixEnd_1244366 := by exact prefixLift 1244366
  have htrace : WordTrace (prefixWord ++ tailWord_1244366) baseStart_1244366 baseEnd_1244366 := by
    simpa [prefixWord, tailWord_1244366, baseEnd_1244366] using wordTrace_append hprefix tailTrace_1244366
  have hstable : (prefixWord ++ tailWord_1244366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244366).length < 2 ^ (prefixWord ++ tailWord_1244366).sum := by decide
  have hdescent : baseEnd_1244366 < baseStart_1244366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244442 : List Nat := [3, 1, 1, 3, 3, 3, 2, 2, 3]
def baseStart_1244442 : Nat := 118140960795 + 1244442 * 2 ^ 59
def prefixEnd_1244442 : Nat := 4983230072969 + 3 ^ 40 * 1244442 * 2
def baseEnd_1244442 : Nat := 283998618952233488289743

theorem tailTrace_1244442 : CollatzResearch.WordTrace tailWord_1244442 prefixEnd_1244442 283998618952233488289743 := by
  unfold tailWord_1244442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347132139401660654507895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30259019038404428412021053 11347132139401660654507895)
  ·
    refine ⟨17020698209102490981761843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11347132139401660654507895 17020698209102490981761843)
    ·
      refine ⟨25531047313653736472642765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020698209102490981761843 25531047313653736472642765)
      ·
        refine ⟨9574142742620151177241037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25531047313653736472642765 9574142742620151177241037)
        ·
          refine ⟨3590303528482556691465389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9574142742620151177241037 3590303528482556691465389)
          ·
            refine ⟨1346363823180958759299521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3590303528482556691465389 1346363823180958759299521)
            ·
              refine ⟨1009772867385719069474641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346363823180958759299521 1009772867385719069474641)
              ·
                refine ⟨757329650539289302105981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009772867385719069474641 757329650539289302105981)
                ·
                  refine ⟨283998618952233488289743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757329650539289302105981 283998618952233488289743)
                  ·
                    rfl

theorem cell21_1244442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 2, 3].length) (baseStart_1244442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244442 prefixEnd_1244442 := by exact prefixLift 1244442
  have htrace : WordTrace (prefixWord ++ tailWord_1244442) baseStart_1244442 baseEnd_1244442 := by
    simpa [prefixWord, tailWord_1244442, baseEnd_1244442] using wordTrace_append hprefix tailTrace_1244442
  have hstable : (prefixWord ++ tailWord_1244442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244442).length < 2 ^ (prefixWord ++ tailWord_1244442).sum := by decide
  have hdescent : baseEnd_1244442 < baseStart_1244442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244453 : List Nat := [1, 3, 1, 2, 4, 3, 1, 6]
def baseStart_1244453 : Nat := 118140960795 + 1244453 * 2 ^ 59
def prefixEnd_1244453 : Nat := 4983230072969 + 3 ^ 40 * 1244453 * 2
def baseEnd_1244453 : Nat := 94667043100699971202129

theorem tailTrace_1244453 : CollatzResearch.WordTrace tailWord_1244453 prefixEnd_1244453 94667043100699971202129 := by
  unfold tailWord_1244453
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388929760566791496682013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30259286507044527664454675 45388929760566791496682013)
  ·
    refine ⟨17020848660212546811255755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45388929760566791496682013 17020848660212546811255755)
    ·
      refine ⟨25531272990318820216883633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17020848660212546811255755 25531272990318820216883633)
      ·
        refine ⟨19148454742739115162662725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25531272990318820216883633 19148454742739115162662725)
        ·
          refine ⟨3590335264263584092999261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19148454742739115162662725 3590335264263584092999261)
          ·
            refine ⟨1346375724098844034874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3590335264263584092999261 1346375724098844034874723)
            ·
              refine ⟨2019563586148266052312085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1346375724098844034874723 2019563586148266052312085)
              ·
                refine ⟨94667043100699971202129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2019563586148266052312085 94667043100699971202129)
                ·
                  rfl

theorem cell21_1244453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_1244453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244453 prefixEnd_1244453 := by exact prefixLift 1244453
  have htrace : WordTrace (prefixWord ++ tailWord_1244453) baseStart_1244453 baseEnd_1244453 := by
    simpa [prefixWord, tailWord_1244453, baseEnd_1244453] using wordTrace_append hprefix tailTrace_1244453
  have hstable : (prefixWord ++ tailWord_1244453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244453).length < 2 ^ (prefixWord ++ tailWord_1244453).sum := by decide
  have hdescent : baseEnd_1244453 < baseStart_1244453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244467 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 5]
def baseStart_1244467 : Nat := 118140960795 + 1244467 * 2 ^ 59
def prefixEnd_1244467 : Nat := 4983230072969 + 3 ^ 40 * 1244467 * 2
def baseEnd_1244467 : Nat := 284004324292839000373025

theorem tailTrace_1244467 : CollatzResearch.WordTrace tailWord_1244467 prefixEnd_1244467 284004324292839000373025 := by
  unfold tailWord_1244467
  simp only [CollatzResearch.WordTrace]
  refine ⟨45389440382516071887691655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30259626921677381258461103 45389440382516071887691655)
  ·
    refine ⟨68084160573774107831537483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45389440382516071887691655 68084160573774107831537483)
    ·
      refine ⟨102126240860661161747306225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68084160573774107831537483 102126240860661161747306225)
      ·
        refine ⟨76594680645495871310479669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102126240860661161747306225 76594680645495871310479669)
        ·
          refine ⟨7180751310515237935357469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76594680645495871310479669 7180751310515237935357469)
          ·
            refine ⟨2692781741443214225759051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7180751310515237935357469 2692781741443214225759051)
            ·
              refine ⟨4039172612164821338638577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692781741443214225759051 4039172612164821338638577)
              ·
                refine ⟨3029379459123616003978933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039172612164821338638577 3029379459123616003978933)
                ·
                  refine ⟨284004324292839000373025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3029379459123616003978933 284004324292839000373025)
                  ·
                    rfl

theorem cell21_1244467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_1244467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244467 prefixEnd_1244467 := by exact prefixLift 1244467
  have htrace : WordTrace (prefixWord ++ tailWord_1244467) baseStart_1244467 baseEnd_1244467 := by
    simpa [prefixWord, tailWord_1244467, baseEnd_1244467] using wordTrace_append hprefix tailTrace_1244467
  have hstable : (prefixWord ++ tailWord_1244467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244467).length < 2 ^ (prefixWord ++ tailWord_1244467).sum := by decide
  have hdescent : baseEnd_1244467 < baseStart_1244467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244515 : List Nat := [1, 1, 1, 5, 2, 3, 3, 1, 4]
def baseStart_1244515 : Nat := 118140960795 + 1244515 * 2 ^ 59
def prefixEnd_1244515 : Nat := 4983230072969 + 3 ^ 40 * 1244515 * 2
def baseEnd_1244515 : Nat := 284015278546801583572927

theorem tailTrace_1244515 : CollatzResearch.WordTrace tailWord_1244515 prefixEnd_1244515 284015278546801583572927 := by
  unfold tailWord_1244515
  simp only [CollatzResearch.WordTrace]
  refine ⟨45391191086342176085438999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30260794057561450723625999 45391191086342176085438999)
  ·
    refine ⟨68086786629513264128158499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45391191086342176085438999 68086786629513264128158499)
    ·
      refine ⟨102130179944269896192237749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68086786629513264128158499 102130179944269896192237749)
      ·
        refine ⟨9574704369775302768022289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102130179944269896192237749 9574704369775302768022289)
        ·
          refine ⟨7181028277331477076016717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9574704369775302768022289 7181028277331477076016717)
          ·
            refine ⟨2692885603999303903506269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7181028277331477076016717 2692885603999303903506269)
            ·
              refine ⟨1009832101499738963814851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2692885603999303903506269 1009832101499738963814851)
              ·
                refine ⟨1514748152249608445722277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009832101499738963814851 1514748152249608445722277)
                ·
                  refine ⟨284015278546801583572927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1514748152249608445722277 284015278546801583572927)
                  ·
                    rfl

theorem cell21_1244515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 1, 4].length) (baseStart_1244515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244515 prefixEnd_1244515 := by exact prefixLift 1244515
  have htrace : WordTrace (prefixWord ++ tailWord_1244515) baseStart_1244515 baseEnd_1244515 := by
    simpa [prefixWord, tailWord_1244515, baseEnd_1244515] using wordTrace_append hprefix tailTrace_1244515
  have hstable : (prefixWord ++ tailWord_1244515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244515).length < 2 ^ (prefixWord ++ tailWord_1244515).sum := by decide
  have hdescent : baseEnd_1244515 < baseStart_1244515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244546 : List Nat := [3, 4, 2, 1, 1, 3, 7]
def baseStart_1244546 : Nat := 118140960795 + 1244546 * 2 ^ 59
def prefixEnd_1244546 : Nat := 4983230072969 + 3 ^ 40 * 1244546 * 2
def baseEnd_1244546 : Nat := 31558039241016935395133

theorem tailTrace_1244546 : CollatzResearch.WordTrace tailWord_1244546 prefixEnd_1244546 31558039241016935395133 := by
  unfold tailWord_1244546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348080437307467094954373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30261547832819912253211661 11348080437307467094954373)
  ·
    refine ⟨2127765081995150080303945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11348080437307467094954373 2127765081995150080303945)
    ·
      refine ⟨1595823811496362560227959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2127765081995150080303945 1595823811496362560227959)
      ·
        refine ⟨2393735717244543840341939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595823811496362560227959 2393735717244543840341939)
        ·
          refine ⟨3590603575866815760512909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393735717244543840341939 3590603575866815760512909)
          ·
            refine ⟨1346476340950055910192341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3590603575866815760512909 1346476340950055910192341)
            ·
              refine ⟨31558039241016935395133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1346476340950055910192341 31558039241016935395133)
              ·
                rfl

theorem cell21_1244546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 7].length) (baseStart_1244546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244546 prefixEnd_1244546 := by exact prefixLift 1244546
  have htrace : WordTrace (prefixWord ++ tailWord_1244546) baseStart_1244546 baseEnd_1244546 := by
    simpa [prefixWord, tailWord_1244546, baseEnd_1244546] using wordTrace_append hprefix tailTrace_1244546
  have hstable : (prefixWord ++ tailWord_1244546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244546).length < 2 ^ (prefixWord ++ tailWord_1244546).sum := by decide
  have hdescent : baseEnd_1244546 < baseStart_1244546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244723 : List Nat := [1, 1, 1, 2, 4, 3, 9]
def baseStart_1244723 : Nat := 118140960795 + 1244723 * 2 ^ 59
def prefixEnd_1244723 : Nat := 4983230072969 + 3 ^ 40 * 1244723 * 2
def baseEnd_1244723 : Nat := 31562527442293271567315

theorem tailTrace_1244723 : CollatzResearch.WordTrace tailWord_1244723 prefixEnd_1244723 31562527442293271567315 := by
  unfold tailWord_1244723
  simp only [CollatzResearch.WordTrace]
  refine ⟨45398777469588627609010823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30265851646392418406007215 45398777469588627609010823)
  ·
    refine ⟨68098166204382941413516235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45398777469588627609010823 68098166204382941413516235)
    ·
      refine ⟨102147249306574412120274353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68098166204382941413516235 102147249306574412120274353)
      ·
        refine ⟨76610436979930809090205765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102147249306574412120274353 76610436979930809090205765)
        ·
          refine ⟨14364456933737026704413581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76610436979930809090205765 14364456933737026704413581)
          ·
            refine ⟨5386671350151385014155093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14364456933737026704413581 5386671350151385014155093)
            ·
              refine ⟨31562527442293271567315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5386671350151385014155093 31562527442293271567315)
              ·
                rfl

theorem cell21_1244723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_1244723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244723 prefixEnd_1244723 := by exact prefixLift 1244723
  have htrace : WordTrace (prefixWord ++ tailWord_1244723) baseStart_1244723 baseEnd_1244723 := by
    simpa [prefixWord, tailWord_1244723, baseEnd_1244723] using wordTrace_append hprefix tailTrace_1244723
  have hstable : (prefixWord ++ tailWord_1244723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244723).length < 2 ^ (prefixWord ++ tailWord_1244723).sum := by decide
  have hdescent : baseEnd_1244723 < baseStart_1244723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244729 : List Nat := [1, 2, 1, 5, 1, 3, 3, 2, 3]
def baseStart_1244729 : Nat := 118140960795 + 1244729 * 2 ^ 59
def prefixEnd_1244729 : Nat := 4983230072969 + 3 ^ 40 * 1244729 * 2
def baseEnd_1244729 : Nat := 284064116262384767005823

theorem tailTrace_1244729 : CollatzResearch.WordTrace tailWord_1244729 prefixEnd_1244729 284064116262384767005823 := by
  unfold tailWord_1244729
  simp only [CollatzResearch.WordTrace]
  refine ⟨45398996307566890633729241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30265997538377927089152827 45398996307566890633729241)
  ·
    refine ⟨34049247230675167975296931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45398996307566890633729241 34049247230675167975296931)
    ·
      refine ⟨51073870846012751962945397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34049247230675167975296931 51073870846012751962945397)
      ·
        refine ⟨4788175391813695496526131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51073870846012751962945397 4788175391813695496526131)
        ·
          refine ⟨7182263087720543244789197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788175391813695496526131 7182263087720543244789197)
          ·
            refine ⟨2693348657895203716795949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7182263087720543244789197 2693348657895203716795949)
            ·
              refine ⟨1010005746710701393798481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2693348657895203716795949 1010005746710701393798481)
              ·
                refine ⟨757504310033026045348861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010005746710701393798481 757504310033026045348861)
                ·
                  refine ⟨284064116262384767005823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757504310033026045348861 284064116262384767005823)
                  ·
                    rfl

theorem cell21_1244729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_1244729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244729 prefixEnd_1244729 := by exact prefixLift 1244729
  have htrace : WordTrace (prefixWord ++ tailWord_1244729) baseStart_1244729 baseEnd_1244729 := by
    simpa [prefixWord, tailWord_1244729, baseEnd_1244729] using wordTrace_append hprefix tailTrace_1244729
  have hstable : (prefixWord ++ tailWord_1244729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244729).length < 2 ^ (prefixWord ++ tailWord_1244729).sum := by decide
  have hdescent : baseEnd_1244729 < baseStart_1244729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244847 : List Nat := [1, 1, 2, 1, 2, 4, 1, 6, 3]
def baseStart_1244847 : Nat := 118140960795 + 1244847 * 2 ^ 59
def prefixEnd_1244847 : Nat := 4983230072969 + 3 ^ 40 * 1244847 * 2
def baseEnd_1244847 : Nat := 284091045470042784038915

theorem tailTrace_1244847 : CollatzResearch.WordTrace tailWord_1244847 prefixEnd_1244847 284091045470042784038915 := by
  unfold tailWord_1244847
  simp only [CollatzResearch.WordTrace]
  refine ⟨45403300121139396786524795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30268866747426264524349863 45403300121139396786524795)
  ·
    refine ⟨68104950181709095179787193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45403300121139396786524795 68104950181709095179787193)
    ·
      refine ⟨51078712636281821384840395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68104950181709095179787193 51078712636281821384840395)
      ·
        refine ⟨76618068954422732077260593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51078712636281821384840395 76618068954422732077260593)
        ·
          refine ⟨57463551715817049057945445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76618068954422732077260593 57463551715817049057945445)
          ·
            refine ⟨10774415946715696698364771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57463551715817049057945445 10774415946715696698364771)
            ·
              refine ⟨16161623920073545047547157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10774415946715696698364771 16161623920073545047547157)
              ·
                refine ⟨757576121253447424103773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16161623920073545047547157 757576121253447424103773)
                ·
                  refine ⟨284091045470042784038915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757576121253447424103773 284091045470042784038915)
                  ·
                    rfl

theorem cell21_1244847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 6, 3].length) (baseStart_1244847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244847 prefixEnd_1244847 := by exact prefixLift 1244847
  have htrace : WordTrace (prefixWord ++ tailWord_1244847) baseStart_1244847 baseEnd_1244847 := by
    simpa [prefixWord, tailWord_1244847, baseEnd_1244847] using wordTrace_append hprefix tailTrace_1244847
  have hstable : (prefixWord ++ tailWord_1244847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244847).length < 2 ^ (prefixWord ++ tailWord_1244847).sum := by decide
  have hdescent : baseEnd_1244847 < baseStart_1244847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244920 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 8]
def baseStart_1244920 : Nat := 118140960795 + 1244920 * 2 ^ 59
def prefixEnd_1244920 : Nat := 4983230072969 + 3 ^ 40 * 1244920 * 2
def baseEnd_1244920 : Nat := 284107705064610879322099

theorem tailTrace_1244920 : CollatzResearch.WordTrace tailWord_1244920 prefixEnd_1244920 284107705064610879322099 := by
  unfold tailWord_1244920
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702981324937465126966107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30270641766583286835954809 22702981324937465126966107)
  ·
    refine ⟨34054471987406197690449161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22702981324937465126966107 34054471987406197690449161)
    ·
      refine ⟨25540853990554648267836871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34054471987406197690449161 25540853990554648267836871)
      ·
        refine ⟨38311280985831972401755307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25540853990554648267836871 38311280985831972401755307)
        ·
          refine ⟨57466921478747958602632961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38311280985831972401755307 57466921478747958602632961)
          ·
            refine ⟨43100191109060968951974721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57466921478747958602632961 43100191109060968951974721)
            ·
              refine ⟨32325143331795726713981041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43100191109060968951974721 32325143331795726713981041)
              ·
                refine ⟨24243857498846795035485781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32325143331795726713981041 24243857498846795035485781)
                ·
                  refine ⟨284107705064610879322099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24243857498846795035485781 284107705064610879322099)
                  ·
                    rfl

theorem cell21_1244920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 8].length) (baseStart_1244920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244920 prefixEnd_1244920 := by exact prefixLift 1244920
  have htrace : WordTrace (prefixWord ++ tailWord_1244920) baseStart_1244920 baseEnd_1244920 := by
    simpa [prefixWord, tailWord_1244920, baseEnd_1244920] using wordTrace_append hprefix tailTrace_1244920
  have hstable : (prefixWord ++ tailWord_1244920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244920).length < 2 ^ (prefixWord ++ tailWord_1244920).sum := by decide
  have hdescent : baseEnd_1244920 < baseStart_1244920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244951 : List Nat := [1, 1, 3, 4, 2, 10]
def baseStart_1244951 : Nat := 118140960795 + 1244951 * 2 ^ 59
def prefixEnd_1244951 : Nat := 4983230072969 + 3 ^ 40 * 1244951 * 2
def baseEnd_1244951 : Nat := 10522769618035619048347

theorem tailTrace_1244951 : CollatzResearch.WordTrace tailWord_1244951 prefixEnd_1244951 10522769618035619048347 := by
  unfold tailWord_1244951
  simp only [CollatzResearch.WordTrace]
  refine ⟨45407093312762622548310707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30271395541841748365540471 45407093312762622548310707)
  ·
    refine ⟨68110639969143933822466061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45407093312762622548310707 68110639969143933822466061)
    ·
      refine ⟨25541489988428975183424773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68110639969143933822466061 25541489988428975183424773)
      ·
        refine ⟨4789029372830432846892145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25541489988428975183424773 4789029372830432846892145)
        ·
          refine ⟨3591772029622824635169109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4789029372830432846892145 3591772029622824635169109)
          ·
            refine ⟨10522769618035619048347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3591772029622824635169109 10522769618035619048347)
            ·
              rfl

theorem cell21_1244951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 10].length) (baseStart_1244951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244951 prefixEnd_1244951 := by exact prefixLift 1244951
  have htrace : WordTrace (prefixWord ++ tailWord_1244951) baseStart_1244951 baseEnd_1244951 := by
    simpa [prefixWord, tailWord_1244951, baseEnd_1244951] using wordTrace_append hprefix tailTrace_1244951
  have hstable : (prefixWord ++ tailWord_1244951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244951).length < 2 ^ (prefixWord ++ tailWord_1244951).sum := by decide
  have hdescent : baseEnd_1244951 < baseStart_1244951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244954 : List Nat := [3, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_1244954 : Nat := 118140960795 + 1244954 * 2 ^ 59
def prefixEnd_1244954 : Nat := 4983230072969 + 3 ^ 40 * 1244954 * 2
def baseEnd_1244954 : Nat := 284115464327834375755363

theorem tailTrace_1244954 : CollatzResearch.WordTrace tailWord_1244954 prefixEnd_1244954 284115464327834375755363 := by
  unfold tailWord_1244954
  simp only [CollatzResearch.WordTrace]
  refine ⟨11351800682937938515167479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30271468487834502707113277 11351800682937938515167479)
  ·
    refine ⟨17027701024406907772751219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11351800682937938515167479 17027701024406907772751219)
    ·
      refine ⟨25541551536610361659126829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17027701024406907772751219 25541551536610361659126829)
      ·
        refine ⟨9578081826228885622172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25541551536610361659126829 9578081826228885622172561)
        ·
          refine ⟨7183561369671664216629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9578081826228885622172561 7183561369671664216629421)
          ·
            refine ⟨2693835513626874081236033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7183561369671664216629421 2693835513626874081236033)
            ·
              refine ⟨2020376635220155560927025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2693835513626874081236033 2020376635220155560927025)
              ·
                refine ⟨1515282476415116670695269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2020376635220155560927025 1515282476415116670695269)
                ·
                  refine ⟨284115464327834375755363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515282476415116670695269 284115464327834375755363)
                  ·
                    rfl

theorem cell21_1244954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_1244954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244954 prefixEnd_1244954 := by exact prefixLift 1244954
  have htrace : WordTrace (prefixWord ++ tailWord_1244954) baseStart_1244954 baseEnd_1244954 := by
    simpa [prefixWord, tailWord_1244954, baseEnd_1244954] using wordTrace_append hprefix tailTrace_1244954
  have hstable : (prefixWord ++ tailWord_1244954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244954).length < 2 ^ (prefixWord ++ tailWord_1244954).sum := by decide
  have hdescent : baseEnd_1244954 < baseStart_1244954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244968 : List Nat := [2, 1, 5, 1, 1, 2, 3, 6]
def baseStart_1244968 : Nat := 118140960795 + 1244968 * 2 ^ 59
def prefixEnd_1244968 : Nat := 4983230072969 + 3 ^ 40 * 1244968 * 2
def baseEnd_1244968 : Nat := 94706219772857820840667

theorem tailTrace_1244968 : CollatzResearch.WordTrace tailWord_1244968 prefixEnd_1244968 94706219772857820840667 := by
  unfold tailWord_1244968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22703856676850517225839779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30271808902467356301119705 22703856676850517225839779)
  ·
    refine ⟨34055785015275775838759669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22703856676850517225839779 34055785015275775838759669)
    ·
      refine ⟨3192729845182103984883719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34055785015275775838759669 3192729845182103984883719)
      ·
        refine ⟨4789094767773155977325579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192729845182103984883719 4789094767773155977325579)
        ·
          refine ⟨7183642151659733965988369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4789094767773155977325579 7183642151659733965988369)
          ·
            refine ⟨5387731613744800474491277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7183642151659733965988369 5387731613744800474491277)
            ·
              refine ⟨2020399355154300177934229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5387731613744800474491277 2020399355154300177934229)
              ·
                refine ⟨94706219772857820840667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2020399355154300177934229 94706219772857820840667)
                ·
                  rfl

theorem cell21_1244968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_1244968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244968 prefixEnd_1244968 := by exact prefixLift 1244968
  have htrace : WordTrace (prefixWord ++ tailWord_1244968) baseStart_1244968 baseEnd_1244968 := by
    simpa [prefixWord, tailWord_1244968, baseEnd_1244968] using wordTrace_append hprefix tailTrace_1244968
  have hstable : (prefixWord ++ tailWord_1244968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244968).length < 2 ^ (prefixWord ++ tailWord_1244968).sum := by decide
  have hdescent : baseEnd_1244968 < baseStart_1244968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1244999 : List Nat := [1, 1, 4, 1, 2, 1, 3, 5, 3]
def baseStart_1244999 : Nat := 118140960795 + 1244999 * 2 ^ 59
def prefixEnd_1244999 : Nat := 4983230072969 + 3 ^ 40 * 1244999 * 2
def baseEnd_1244999 : Nat := 284125733940924297505271

theorem tailTrace_1244999 : CollatzResearch.WordTrace tailWord_1244999 prefixEnd_1244999 284125733940924297505271 := by
  unfold tailWord_1244999
  simp only [CollatzResearch.WordTrace]
  refine ⟨45408844016588726746058051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30272562677725817830705367 45408844016588726746058051)
  ·
    refine ⟨68113266024883090119087077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45408844016588726746058051 68113266024883090119087077)
    ·
      refine ⟨12771237379665579397328827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68113266024883090119087077 12771237379665579397328827)
      ·
        refine ⟨19156856069498369095993241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12771237379665579397328827 19156856069498369095993241)
        ·
          refine ⟨14367642052123776821994931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19156856069498369095993241 14367642052123776821994931)
          ·
            refine ⟨21551463078185665232992397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14367642052123776821994931 21551463078185665232992397)
            ·
              refine ⟨8081798654319624462372149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21551463078185665232992397 8081798654319624462372149)
              ·
                refine ⟨757668623842464793347389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8081798654319624462372149 757668623842464793347389)
                ·
                  refine ⟨284125733940924297505271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757668623842464793347389 284125733940924297505271)
                  ·
                    rfl

theorem cell21_1244999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].length) (baseStart_1244999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1244999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1244999 prefixEnd_1244999 := by exact prefixLift 1244999
  have htrace : WordTrace (prefixWord ++ tailWord_1244999) baseStart_1244999 baseEnd_1244999 := by
    simpa [prefixWord, tailWord_1244999, baseEnd_1244999] using wordTrace_append hprefix tailTrace_1244999
  have hstable : (prefixWord ++ tailWord_1244999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1244999).length < 2 ^ (prefixWord ++ tailWord_1244999).sum := by decide
  have hdescent : baseEnd_1244999 < baseStart_1244999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1244999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245013 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 6]
def baseStart_1245013 : Nat := 118140960795 + 1245013 * 2 ^ 59
def prefixEnd_1245013 : Nat := 4983230072969 + 3 ^ 40 * 1245013 * 2
def baseEnd_1245013 : Nat := 284128928931663384271909

theorem tailTrace_1245013 : CollatzResearch.WordTrace tailWord_1245013 prefixEnd_1245013 284128928931663384271909 := by
  unfold tailWord_1245013
  simp only [CollatzResearch.WordTrace]
  refine ⟨45409354638538007137067693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30272903092358671424711795 45409354638538007137067693)
  ·
    refine ⟨17028507989451752676400385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45409354638538007137067693 17028507989451752676400385)
    ·
      refine ⟨12771380992088814507300289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17028507989451752676400385 12771380992088814507300289)
      ·
        refine ⟨9578535744066610880475217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12771380992088814507300289 9578535744066610880475217)
        ·
          refine ⟨7183901808049958160356413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9578535744066610880475217 7183901808049958160356413)
          ·
            refine ⟨2693963178018734310133655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7183901808049958160356413 2693963178018734310133655)
            ·
              refine ⟨4040944767028101465200483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693963178018734310133655 4040944767028101465200483)
              ·
                refine ⟨6061417150542152197800725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040944767028101465200483 6061417150542152197800725)
                ·
                  refine ⟨284128928931663384271909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6061417150542152197800725 284128928931663384271909)
                  ·
                    rfl

theorem cell21_1245013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_1245013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245013 prefixEnd_1245013 := by exact prefixLift 1245013
  have htrace : WordTrace (prefixWord ++ tailWord_1245013) baseStart_1245013 baseEnd_1245013 := by
    simpa [prefixWord, tailWord_1245013, baseEnd_1245013] using wordTrace_append hprefix tailTrace_1245013
  have hstable : (prefixWord ++ tailWord_1245013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245013).length < 2 ^ (prefixWord ++ tailWord_1245013).sum := by decide
  have hdescent : baseEnd_1245013 < baseStart_1245013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245134 : List Nat := [4, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_1245134 : Nat := 118140960795 + 1245134 * 2 ^ 59
def prefixEnd_1245134 : Nat := 4983230072969 + 3 ^ 40 * 1245134 * 2
def baseEnd_1245134 : Nat := 284156542780194062754995

theorem tailTrace_1245134 : CollatzResearch.WordTrace tailWord_1245134 prefixEnd_1245134 284156542780194062754995 := by
  unfold tailWord_1245134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676720983887455600277807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30275845247399763201481637 5676720983887455600277807)
  ·
    refine ⟨8515081475831183400416711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5676720983887455600277807 8515081475831183400416711)
    ·
      refine ⟨12772622213746775100625067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8515081475831183400416711 12772622213746775100625067)
      ·
        refine ⟨19158933320620162650937601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12772622213746775100625067 19158933320620162650937601)
        ·
          refine ⟨14369199990465121988203201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19158933320620162650937601 14369199990465121988203201)
          ·
            refine ⟨10776899992848841491152401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14369199990465121988203201 10776899992848841491152401)
            ·
              refine ⟨8082674994636631118364301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10776899992848841491152401 8082674994636631118364301)
              ·
                refine ⟨3031003122988736669386613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8082674994636631118364301 3031003122988736669386613)
                ·
                  refine ⟨284156542780194062754995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031003122988736669386613 284156542780194062754995)
                  ·
                    rfl

theorem cell21_1245134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_1245134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245134 prefixEnd_1245134 := by exact prefixLift 1245134
  have htrace : WordTrace (prefixWord ++ tailWord_1245134) baseStart_1245134 baseEnd_1245134 := by
    simpa [prefixWord, tailWord_1245134, baseEnd_1245134] using wordTrace_append hprefix tailTrace_1245134
  have hstable : (prefixWord ++ tailWord_1245134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245134).length < 2 ^ (prefixWord ++ tailWord_1245134).sum := by decide
  have hdescent : baseEnd_1245134 < baseStart_1245134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245154 : List Nat := [3, 3, 3, 1, 2, 1, 3, 5]
def baseStart_1245154 : Nat := 118140960795 + 1245154 * 2 ^ 59
def prefixEnd_1245154 : Nat := 4983230072969 + 3 ^ 40 * 1245154 * 2
def baseEnd_1245154 : Nat := 94720369017559490807207

theorem tailTrace_1245154 : CollatzResearch.WordTrace tailWord_1245154 prefixEnd_1245154 94720369017559490807207 := by
  unfold tailWord_1245154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11353624332756797054487629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30276331554018125478633677 11353624332756797054487629)
  ·
    refine ⟨4257609124783798895432861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11353624332756797054487629 4257609124783798895432861)
    ·
      refine ⟨1596603421793924585787323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4257609124783798895432861 1596603421793924585787323)
      ·
        refine ⟨2394905132690886878680985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596603421793924585787323 2394905132690886878680985)
        ·
          refine ⟨1796178849518165159010739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394905132690886878680985 1796178849518165159010739)
          ·
            refine ⟨2694268274277247738516109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1796178849518165159010739 2694268274277247738516109)
            ·
              refine ⟨1010350602853967901943541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2694268274277247738516109 1010350602853967901943541)
              ·
                refine ⟨94720369017559490807207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1010350602853967901943541 94720369017559490807207)
                ·
                  rfl

theorem cell21_1245154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_1245154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245154 prefixEnd_1245154 := by exact prefixLift 1245154
  have htrace : WordTrace (prefixWord ++ tailWord_1245154) baseStart_1245154 baseEnd_1245154 := by
    simpa [prefixWord, tailWord_1245154, baseEnd_1245154] using wordTrace_append hprefix tailTrace_1245154
  have hstable : (prefixWord ++ tailWord_1245154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245154).length < 2 ^ (prefixWord ++ tailWord_1245154).sum := by decide
  have hdescent : baseEnd_1245154 < baseStart_1245154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245182 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_1245182 : Nat := 118140960795 + 1245182 * 2 ^ 59
def prefixEnd_1245182 : Nat := 4983230072969 + 3 ^ 40 * 1245182 * 2
def baseEnd_1245182 : Nat := 284167497034156645954897

theorem tailTrace_1245182 : CollatzResearch.WordTrace tailWord_1245182 prefixEnd_1245182 284167497034156645954897 := by
  unfold tailWord_1245182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676939821865718624996225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30277012383283832666646533 5676939821865718624996225)
  ·
    refine ⟨4257704866399288968747169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5676939821865718624996225 4257704866399288968747169)
    ·
      refine ⟨3193278649799466726560377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4257704866399288968747169 3193278649799466726560377)
      ·
        refine ⟨2394958987349600044920283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3193278649799466726560377 2394958987349600044920283)
        ·
          refine ⟨3592438481024400067380425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394958987349600044920283 3592438481024400067380425)
          ·
            refine ⟨2694328860768300050535319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3592438481024400067380425 2694328860768300050535319)
            ·
              refine ⟨4041493291152450075802979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694328860768300050535319 4041493291152450075802979)
              ·
                refine ⟨6062239936728675113704469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4041493291152450075802979 6062239936728675113704469)
                ·
                  refine ⟨284167497034156645954897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6062239936728675113704469 284167497034156645954897)
                  ·
                    rfl

theorem cell21_1245182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_1245182 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245182 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245182 prefixEnd_1245182 := by exact prefixLift 1245182
  have htrace : WordTrace (prefixWord ++ tailWord_1245182) baseStart_1245182 baseEnd_1245182 := by
    simpa [prefixWord, tailWord_1245182, baseEnd_1245182] using wordTrace_append hprefix tailTrace_1245182
  have hstable : (prefixWord ++ tailWord_1245182).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245182).length < 2 ^ (prefixWord ++ tailWord_1245182).sum := by decide
  have hdescent : baseEnd_1245182 < baseStart_1245182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245210 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 5]
def baseStart_1245210 : Nat := 118140960795 + 1245210 * 2 ^ 59
def prefixEnd_1245210 : Nat := 4983230072969 + 3 ^ 40 * 1245210 * 2
def baseEnd_1245210 : Nat := 284173887015634819488173

theorem tailTrace_1245210 : CollatzResearch.WordTrace tailWord_1245210 prefixEnd_1245210 284173887015634819488173 := by
  unfold tailWord_1245210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354134954706077445497271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30277693212549539854659389 11354134954706077445497271)
  ·
    refine ⟨17031202432059116168245907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11354134954706077445497271 17031202432059116168245907)
    ·
      refine ⟨25546803648088674252368861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17031202432059116168245907 25546803648088674252368861)
      ·
        refine ⟨9580051368033252844638323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25546803648088674252368861 9580051368033252844638323)
        ·
          refine ⟨14370077052049879266957485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9580051368033252844638323 14370077052049879266957485)
          ·
            refine ⟨5388778894518704725109057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14370077052049879266957485 5388778894518704725109057)
            ·
              refine ⟨4041584170889028543831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5388778894518704725109057 4041584170889028543831793)
              ·
                refine ⟨3031188128166771407873845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4041584170889028543831793 3031188128166771407873845)
                ·
                  refine ⟨284173887015634819488173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031188128166771407873845 284173887015634819488173)
                  ·
                    rfl

theorem cell21_1245210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_1245210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245210 prefixEnd_1245210 := by exact prefixLift 1245210
  have htrace : WordTrace (prefixWord ++ tailWord_1245210) baseStart_1245210 baseEnd_1245210 := by
    simpa [prefixWord, tailWord_1245210, baseEnd_1245210] using wordTrace_append hprefix tailTrace_1245210
  have hstable : (prefixWord ++ tailWord_1245210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245210).length < 2 ^ (prefixWord ++ tailWord_1245210).sum := by decide
  have hdescent : baseEnd_1245210 < baseStart_1245210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245213 : List Nat := [1, 4, 2, 2, 2, 3, 2, 5]
def baseStart_1245213 : Nat := 118140960795 + 1245213 * 2 ^ 59
def prefixEnd_1245213 : Nat := 4983230072969 + 3 ^ 40 * 1245213 * 2
def baseEnd_1245213 : Nat := 94724857218835826979389

theorem tailTrace_1245213 : CollatzResearch.WordTrace tailWord_1245213 prefixEnd_1245213 94724857218835826979389 := by
  unfold tailWord_1245213
  simp only [CollatzResearch.WordTrace]
  refine ⟨45416649237813441294348293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30277766158542294196232195 45416649237813441294348293)
  ·
    refine ⟨8515621732090020242690305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45416649237813441294348293 8515621732090020242690305)
    ·
      refine ⟨6386716299067515182017729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8515621732090020242690305 6386716299067515182017729)
      ·
        refine ⟨4790037224300636386513297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6386716299067515182017729 4790037224300636386513297)
        ·
          refine ⟨3592527918225477289884973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4790037224300636386513297 3592527918225477289884973)
          ·
            refine ⟨1347197969334553983706865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3592527918225477289884973 1347197969334553983706865)
            ·
              refine ⟨1010398477000915487780149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1347197969334553983706865 1010398477000915487780149)
              ·
                refine ⟨94724857218835826979389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1010398477000915487780149 94724857218835826979389)
                ·
                  rfl

theorem cell21_1245213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 5].length) (baseStart_1245213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245213 prefixEnd_1245213 := by exact prefixLift 1245213
  have htrace : WordTrace (prefixWord ++ tailWord_1245213) baseStart_1245213 baseEnd_1245213 := by
    simpa [prefixWord, tailWord_1245213, baseEnd_1245213] using wordTrace_append hprefix tailTrace_1245213
  have hstable : (prefixWord ++ tailWord_1245213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245213).length < 2 ^ (prefixWord ++ tailWord_1245213).sum := by decide
  have hdescent : baseEnd_1245213 < baseStart_1245213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245244 : List Nat := [2, 2, 2, 2, 2, 1, 5, 2, 3]
def baseStart_1245244 : Nat := 118140960795 + 1245244 * 2 ^ 59
def prefixEnd_1245244 : Nat := 4983230072969 + 3 ^ 40 * 1245244 * 2
def baseEnd_1245244 : Nat := 284181646278858315921437

theorem tailTrace_1245244 : CollatzResearch.WordTrace tailWord_1245244 prefixEnd_1245244 284181646278858315921437 := by
  unfold tailWord_1245244
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708889950350566794363393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30278519933800755725817857 22708889950350566794363393)
  ·
    refine ⟨17031667462762925095772545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22708889950350566794363393 17031667462762925095772545)
    ·
      refine ⟨12773750597072193821829409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17031667462762925095772545 12773750597072193821829409)
      ·
        refine ⟨9580312947804145366372057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12773750597072193821829409 9580312947804145366372057)
        ·
          refine ⟨7185234710853109024779043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9580312947804145366372057 7185234710853109024779043)
          ·
            refine ⟨10777852066279663537168565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185234710853109024779043 10777852066279663537168565)
            ·
              refine ⟨1010423631213718456609553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10777852066279663537168565 1010423631213718456609553)
              ·
                refine ⟨757817723410288842457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010423631213718456609553 757817723410288842457165)
                ·
                  refine ⟨284181646278858315921437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757817723410288842457165 284181646278858315921437)
                  ·
                    rfl

theorem cell21_1245244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_1245244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245244 prefixEnd_1245244 := by exact prefixLift 1245244
  have htrace : WordTrace (prefixWord ++ tailWord_1245244) baseStart_1245244 baseEnd_1245244 := by
    simpa [prefixWord, tailWord_1245244, baseEnd_1245244] using wordTrace_append hprefix tailTrace_1245244
  have hstable : (prefixWord ++ tailWord_1245244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245244).length < 2 ^ (prefixWord ++ tailWord_1245244).sum := by decide
  have hdescent : baseEnd_1245244 < baseStart_1245244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245255 : List Nat := [1, 1, 4, 1, 3, 1, 4, 6]
def baseStart_1245255 : Nat := 118140960795 + 1245255 * 2 ^ 59
def prefixEnd_1245255 : Nat := 4983230072969 + 3 ^ 40 * 1245255 * 2
def baseEnd_1245255 : Nat := 94728052209574913746027

theorem tailTrace_1245255 : CollatzResearch.WordTrace tailWord_1245255 prefixEnd_1245255 94728052209574913746027 := by
  unfold tailWord_1245255
  simp only [CollatzResearch.WordTrace]
  refine ⟨45418181103661282467377219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30278787402440854978251479 45418181103661282467377219)
  ·
    refine ⟨68127271655491923701065829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45418181103661282467377219 68127271655491923701065829)
    ·
      refine ⟨12773863435404735693949843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68127271655491923701065829 12773863435404735693949843)
      ·
        refine ⟨19160795153107103540924765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12773863435404735693949843 19160795153107103540924765)
        ·
          refine ⟨7185298182415163827846787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19160795153107103540924765 7185298182415163827846787)
          ·
            refine ⟨10777947273622745741770181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7185298182415163827846787 10777947273622745741770181)
            ·
              refine ⟨2020865113804264826581909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10777947273622745741770181 2020865113804264826581909)
              ·
                refine ⟨94728052209574913746027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2020865113804264826581909 94728052209574913746027)
                ·
                  rfl

theorem cell21_1245255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 6].length) (baseStart_1245255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245255 prefixEnd_1245255 := by exact prefixLift 1245255
  have htrace : WordTrace (prefixWord ++ tailWord_1245255) baseStart_1245255 baseEnd_1245255 := by
    simpa [prefixWord, tailWord_1245255, baseEnd_1245255] using wordTrace_append hprefix tailTrace_1245255
  have hstable : (prefixWord ++ tailWord_1245255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245255).length < 2 ^ (prefixWord ++ tailWord_1245255).sum := by decide
  have hdescent : baseEnd_1245255 < baseStart_1245255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245303 : List Nat := [1, 1, 3, 1, 1, 6, 1, 4, 3]
def baseStart_1245303 : Nat := 118140960795 + 1245303 * 2 ^ 59
def prefixEnd_1245303 : Nat := 4983230072969 + 3 ^ 40 * 1245303 * 2
def baseEnd_1245303 : Nat := 284195110882687324437983

theorem tailTrace_1245303 : CollatzResearch.WordTrace tailWord_1245303 prefixEnd_1245303 284195110882687324437983 := by
  unfold tailWord_1245303
  simp only [CollatzResearch.WordTrace]
  refine ⟨45419931807487386665124563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30279954538324924443416375 45419931807487386665124563)
  ·
    refine ⟨68129897711231079997686845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45419931807487386665124563 68129897711231079997686845)
    ·
      refine ⟨25548711641711654999132567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68129897711231079997686845 25548711641711654999132567)
      ·
        refine ⟨38323067462567482498698851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25548711641711654999132567 38323067462567482498698851)
        ·
          refine ⟨57484601193851223748048277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38323067462567482498698851 57484601193851223748048277)
          ·
            refine ⟨2694590680961776113189763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57484601193851223748048277 2694590680961776113189763)
            ·
              refine ⟨4041886021442664169784645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2694590680961776113189763 4041886021442664169784645)
              ·
                refine ⟨757853629020499531834621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4041886021442664169784645 757853629020499531834621)
                ·
                  refine ⟨284195110882687324437983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757853629020499531834621 284195110882687324437983)
                  ·
                    rfl

theorem cell21_1245303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 4, 3].length) (baseStart_1245303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245303 prefixEnd_1245303 := by exact prefixLift 1245303
  have htrace : WordTrace (prefixWord ++ tailWord_1245303) baseStart_1245303 baseEnd_1245303 := by
    simpa [prefixWord, tailWord_1245303, baseEnd_1245303] using wordTrace_append hprefix tailTrace_1245303
  have hstable : (prefixWord ++ tailWord_1245303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245303).length < 2 ^ (prefixWord ++ tailWord_1245303).sum := by decide
  have hdescent : baseEnd_1245303 < baseStart_1245303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245317 : List Nat := [1, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_1245317 : Nat := 118140960795 + 1245317 * 2 ^ 59
def prefixEnd_1245317 : Nat := 4983230072969 + 3 ^ 40 * 1245317 * 2
def baseEnd_1245317 : Nat := 284198305873426411204621

theorem tailTrace_1245317 : CollatzResearch.WordTrace tailWord_1245317 prefixEnd_1245317 284198305873426411204621 := by
  unfold tailWord_1245317
  simp only [CollatzResearch.WordTrace]
  refine ⟨45420442429436667056134205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30280294952957778037422803 45420442429436667056134205)
  ·
    refine ⟨17032665911038750146050327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45420442429436667056134205 17032665911038750146050327)
    ·
      refine ⟨25548998866558125219075491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17032665911038750146050327 25548998866558125219075491)
      ·
        refine ⟨38323498299837187828613237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25548998866558125219075491 38323498299837187828613237)
        ·
          refine ⟨3592827965609736358932491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38323498299837187828613237 3592827965609736358932491)
          ·
            refine ⟨5389241948414604538398737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592827965609736358932491 5389241948414604538398737)
            ·
              refine ⟨4041931461310953403799053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5389241948414604538398737 4041931461310953403799053)
              ·
                refine ⟨1515724297991607526424645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4041931461310953403799053 1515724297991607526424645)
                ·
                  refine ⟨284198305873426411204621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515724297991607526424645 284198305873426411204621)
                  ·
                    rfl

theorem cell21_1245317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_1245317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245317 prefixEnd_1245317 := by exact prefixLift 1245317
  have htrace : WordTrace (prefixWord ++ tailWord_1245317) baseStart_1245317 baseEnd_1245317 := by
    simpa [prefixWord, tailWord_1245317, baseEnd_1245317] using wordTrace_append hprefix tailTrace_1245317
  have hstable : (prefixWord ++ tailWord_1245317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245317).length < 2 ^ (prefixWord ++ tailWord_1245317).sum := by decide
  have hdescent : baseEnd_1245317 < baseStart_1245317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245351 : List Nat := [1, 1, 6, 2, 2, 2, 1, 2, 4]
def baseStart_1245351 : Nat := 118140960795 + 1245351 * 2 ^ 59
def prefixEnd_1245351 : Nat := 4983230072969 + 3 ^ 40 * 1245351 * 2
def baseEnd_1245351 : Nat := 284206065136649907637885

theorem tailTrace_1245351 : CollatzResearch.WordTrace tailWord_1245351 prefixEnd_1245351 284206065136649907637885 := by
  unfold tailWord_1245351
  simp only [CollatzResearch.WordTrace]
  refine ⟨45421682511313490862871907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30281121674208993908581271 45421682511313490862871907)
  ·
    refine ⟨68132523766970236294307861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45421682511313490862871907 68132523766970236294307861)
    ·
      refine ⟨3193712051576729826295681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68132523766970236294307861 3193712051576729826295681)
      ·
        refine ⟨2395284038682547369721761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3193712051576729826295681 2395284038682547369721761)
        ·
          refine ⟨1796463029011910527291321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2395284038682547369721761 1796463029011910527291321)
          ·
            refine ⟨1347347271758932895468491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796463029011910527291321 1347347271758932895468491)
            ·
              refine ⟨2021020907638399343202737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347347271758932895468491 2021020907638399343202737)
              ·
                refine ⟨1515765680728799507402053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021020907638399343202737 1515765680728799507402053)
                ·
                  refine ⟨284206065136649907637885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515765680728799507402053 284206065136649907637885)
                  ·
                    rfl

theorem cell21_1245351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 2, 4].length) (baseStart_1245351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245351 prefixEnd_1245351 := by exact prefixLift 1245351
  have htrace : WordTrace (prefixWord ++ tailWord_1245351) baseStart_1245351 baseEnd_1245351 := by
    simpa [prefixWord, tailWord_1245351, baseEnd_1245351] using wordTrace_append hprefix tailTrace_1245351
  have hstable : (prefixWord ++ tailWord_1245351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245351).length < 2 ^ (prefixWord ++ tailWord_1245351).sum := by decide
  have hdescent : baseEnd_1245351 < baseStart_1245351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245362 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_1245362 : Nat := 118140960795 + 1245362 * 2 ^ 59
def prefixEnd_1245362 : Nat := 4983230072969 + 3 ^ 40 * 1245362 * 2
def baseEnd_1245362 : Nat := 284208575486516332954529

theorem tailTrace_1245362 : CollatzResearch.WordTrace tailWord_1245362 prefixEnd_1245362 284208575486516332954529 := by
  unfold tailWord_1245362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11355520928568409935380585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30281389142849093161014893 11355520928568409935380585)
  ·
    refine ⟨8516640696426307451535439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11355520928568409935380585 8516640696426307451535439)
    ·
      refine ⟨12774961044639461177303159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516640696426307451535439 12774961044639461177303159)
      ·
        refine ⟨19162441566959191765954739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774961044639461177303159 19162441566959191765954739)
        ·
          refine ⟨28743662350438787648932109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19162441566959191765954739 28743662350438787648932109)
          ·
            refine ⟨10778873381414545368349541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28743662350438787648932109 10778873381414545368349541)
            ·
              refine ⟨2021038759015227256565539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10778873381414545368349541 2021038759015227256565539)
              ·
                refine ⟨3031558138522840884848309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021038759015227256565539 3031558138522840884848309)
                ·
                  refine ⟨284208575486516332954529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3031558138522840884848309 284208575486516332954529)
                  ·
                    rfl

theorem cell21_1245362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_1245362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245362 prefixEnd_1245362 := by exact prefixLift 1245362
  have htrace : WordTrace (prefixWord ++ tailWord_1245362) baseStart_1245362 baseEnd_1245362 := by
    simpa [prefixWord, tailWord_1245362, baseEnd_1245362] using wordTrace_append hprefix tailTrace_1245362
  have hstable : (prefixWord ++ tailWord_1245362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245362).length < 2 ^ (prefixWord ++ tailWord_1245362).sum := by decide
  have hdescent : baseEnd_1245362 < baseStart_1245362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245438 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1245438 : Nat := 118140960795 + 1245438 * 2 ^ 59
def prefixEnd_1245438 : Nat := 4983230072969 + 3 ^ 40 * 1245438 * 2
def baseEnd_1245438 : Nat := 284225919721957089687707

theorem tailTrace_1245438 : CollatzResearch.WordTrace tailWord_1245438 prefixEnd_1245438 284225919721957089687707 := by
  unfold tailWord_1245438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678106957749788090161121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30283237107998869814192645 5678106957749788090161121)
  ·
    refine ⟨4258580218312341067620841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5678106957749788090161121 4258580218312341067620841)
    ·
      refine ⟨3193935163734255800715631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4258580218312341067620841 3193935163734255800715631)
      ·
        refine ⟨4790902745601383701073447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3193935163734255800715631 4790902745601383701073447)
        ·
          refine ⟨7186354118402075551610171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4790902745601383701073447 7186354118402075551610171)
          ·
            refine ⟨10779531177603113327415257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7186354118402075551610171 10779531177603113327415257)
            ·
              refine ⟨8084648383202334995561443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10779531177603113327415257 8084648383202334995561443)
              ·
                refine ⟨12126972574803502493342165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8084648383202334995561443 12126972574803502493342165)
                ·
                  refine ⟨284225919721957089687707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12126972574803502493342165 284225919721957089687707)
                  ·
                    rfl

theorem cell21_1245438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1245438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245438 prefixEnd_1245438 := by exact prefixLift 1245438
  have htrace : WordTrace (prefixWord ++ tailWord_1245438) baseStart_1245438 baseEnd_1245438 := by
    simpa [prefixWord, tailWord_1245438, baseEnd_1245438] using wordTrace_append hprefix tailTrace_1245438
  have hstable : (prefixWord ++ tailWord_1245438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245438).length < 2 ^ (prefixWord ++ tailWord_1245438).sum := by decide
  have hdescent : baseEnd_1245438 < baseStart_1245438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245466 : List Nat := [3, 1, 1, 3, 13]
def baseStart_1245466 : Nat := 118140960795 + 1245466 * 2 ^ 59
def prefixEnd_1245466 : Nat := 4983230072969 + 3 ^ 40 * 1245466 * 2
def baseEnd_1245466 : Nat := 3509040860536237817543

theorem tailTrace_1245466 : CollatzResearch.WordTrace tailWord_1245466 prefixEnd_1245466 3509040860536237817543 := by
  unfold tailWord_1245466
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356469226474216375827063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30283917937264577002205501 11356469226474216375827063)
  ·
    refine ⟨17034703839711324563740595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356469226474216375827063 17034703839711324563740595)
    ·
      refine ⟨25552055759566986845610893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17034703839711324563740595 25552055759566986845610893)
      ·
        refine ⟨9582020909837620067104085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25552055759566986845610893 9582020909837620067104085)
        ·
          refine ⟨3509040860536237817543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9582020909837620067104085 3509040860536237817543)
          ·
            rfl

theorem cell21_1245466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 13].length) (baseStart_1245466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245466 prefixEnd_1245466 := by exact prefixLift 1245466
  have htrace : WordTrace (prefixWord ++ tailWord_1245466) baseStart_1245466 baseEnd_1245466 := by
    simpa [prefixWord, tailWord_1245466, baseEnd_1245466] using wordTrace_append hprefix tailTrace_1245466
  have hstable : (prefixWord ++ tailWord_1245466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245466).length < 2 ^ (prefixWord ++ tailWord_1245466).sum := by decide
  have hdescent : baseEnd_1245466 < baseStart_1245466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245472 : List Nat := [2, 1, 1, 5, 2, 1, 4, 2, 3]
def baseStart_1245472 : Nat := 118140960795 + 1245472 * 2 ^ 59
def prefixEnd_1245472 : Nat := 4983230072969 + 3 ^ 40 * 1245472 * 2
def baseEnd_1245472 : Nat := 284233678985180586120971

theorem tailTrace_1245472 : CollatzResearch.WordTrace tailWord_1245472 prefixEnd_1245472 284233678985180586120971 := by
  unfold tailWord_1245472
  simp only [CollatzResearch.WordTrace]
  refine ⟨22713047871937564264013335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30284063829250085685351113 22713047871937564264013335)
  ·
    refine ⟨34069571807906346396020003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22713047871937564264013335 34069571807906346396020003)
    ·
      refine ⟨51104357711859519594030005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34069571807906346396020003 51104357711859519594030005)
      ·
        refine ⟨4791033535486829961940313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51104357711859519594030005 4791033535486829961940313)
        ·
          refine ⟨3593275151615122471455235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4791033535486829961940313 3593275151615122471455235)
          ·
            refine ⟨5389912727422683707182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593275151615122471455235 5389912727422683707182853)
            ·
              refine ⟨1010608636391753195096785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5389912727422683707182853 1010608636391753195096785)
              ·
                refine ⟨757956477293814896322589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010608636391753195096785 757956477293814896322589)
                ·
                  refine ⟨284233678985180586120971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 757956477293814896322589 284233678985180586120971)
                  ·
                    rfl

theorem cell21_1245472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 2, 3].length) (baseStart_1245472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245472 prefixEnd_1245472 := by exact prefixLift 1245472
  have htrace : WordTrace (prefixWord ++ tailWord_1245472) baseStart_1245472 baseEnd_1245472 := by
    simpa [prefixWord, tailWord_1245472, baseEnd_1245472] using wordTrace_append hprefix tailTrace_1245472
  have hstable : (prefixWord ++ tailWord_1245472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245472).length < 2 ^ (prefixWord ++ tailWord_1245472).sum := by decide
  have hdescent : baseEnd_1245472 < baseStart_1245472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245528 : List Nat := [2, 1, 2, 2, 1, 1, 2, 6, 4]
def baseStart_1245528 : Nat := 118140960795 + 1245528 * 2 ^ 59
def prefixEnd_1245528 : Nat := 4983230072969 + 3 ^ 40 * 1245528 * 2
def baseEnd_1245528 : Nat := 284246458948136933187523

theorem tailTrace_1245528 : CollatzResearch.WordTrace tailWord_1245528 prefixEnd_1245528 284246458948136933187523 := by
  unfold tailWord_1245528
  simp only [CollatzResearch.WordTrace]
  refine ⟨22714069115836125046032619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30285425487781500061376825 22714069115836125046032619)
  ·
    refine ⟨34071103673754187569048929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22714069115836125046032619 34071103673754187569048929)
    ·
      refine ⟨25553327755315640676786697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34071103673754187569048929 25553327755315640676786697)
      ·
        refine ⟨19164995816486730507590023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25553327755315640676786697 19164995816486730507590023)
        ·
          refine ⟨28747493724730095761385035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19164995816486730507590023 28747493724730095761385035)
          ·
            refine ⟨43121240587095143642077553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28747493724730095761385035 43121240587095143642077553)
            ·
              refine ⟨32340930440321357731558165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43121240587095143642077553 32340930440321357731558165)
              ·
                refine ⟨1515981114390063643666789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32340930440321357731558165 1515981114390063643666789)
                ·
                  refine ⟨284246458948136933187523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1515981114390063643666789 284246458948136933187523)
                  ·
                    rfl

theorem cell21_1245528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 6, 4].length) (baseStart_1245528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245528 prefixEnd_1245528 := by exact prefixLift 1245528
  have htrace : WordTrace (prefixWord ++ tailWord_1245528) baseStart_1245528 baseEnd_1245528 := by
    simpa [prefixWord, tailWord_1245528, baseEnd_1245528] using wordTrace_append hprefix tailTrace_1245528
  have hstable : (prefixWord ++ tailWord_1245528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245528).length < 2 ^ (prefixWord ++ tailWord_1245528).sum := by decide
  have hdescent : baseEnd_1245528 < baseStart_1245528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245545 : List Nat := [1, 2, 1, 1, 1, 3, 7, 1, 4]
def baseStart_1245545 : Nat := 118140960795 + 1245545 * 2 ^ 59
def prefixEnd_1245545 : Nat := 4983230072969 + 3 ^ 40 * 1245545 * 2
def baseEnd_1245545 : Nat := 284250338579748681404155

theorem tailTrace_1245545 : CollatzResearch.WordTrace tailWord_1245545 prefixEnd_1245545 284250338579748681404155 := by
  unfold tailWord_1245545
  simp only [CollatzResearch.WordTrace]
  refine ⟨45428758272610661995434089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30285838848407107996956059 45428758272610661995434089)
  ·
    refine ⟨34071568704457996496575567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45428758272610661995434089 34071568704457996496575567)
    ·
      refine ⟨51107353056686994744863351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34071568704457996496575567 51107353056686994744863351)
      ·
        refine ⟨76661029585030492117295027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51107353056686994744863351 76661029585030492117295027)
        ·
          refine ⟨114991544377545738175942541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76661029585030492117295027 114991544377545738175942541)
          ·
            refine ⟨43121829141579651815978453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114991544377545738175942541 43121829141579651815978453)
            ·
              refine ⟨1010667870505773089436995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43121829141579651815978453 1010667870505773089436995)
              ·
                refine ⟨1516001805758659634155493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010667870505773089436995 1516001805758659634155493)
                ·
                  refine ⟨284250338579748681404155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516001805758659634155493 284250338579748681404155)
                  ·
                    rfl

theorem cell21_1245545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_1245545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245545 prefixEnd_1245545 := by exact prefixLift 1245545
  have htrace : WordTrace (prefixWord ++ tailWord_1245545) baseStart_1245545 baseEnd_1245545 := by
    simpa [prefixWord, tailWord_1245545, baseEnd_1245545] using wordTrace_append hprefix tailTrace_1245545
  have hstable : (prefixWord ++ tailWord_1245545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245545).length < 2 ^ (prefixWord ++ tailWord_1245545).sum := by decide
  have hdescent : baseEnd_1245545 < baseStart_1245545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245618 : List Nat := [3, 2, 1, 1, 1, 1, 3, 9]
def baseStart_1245618 : Nat := 118140960795 + 1245618 * 2 ^ 59
def prefixEnd_1245618 : Nat := 4983230072969 + 3 ^ 40 * 1245618 * 2
def baseEnd_1245618 : Nat := 94755666058105592229113

theorem tailTrace_1245618 : CollatzResearch.WordTrace tailWord_1245618 prefixEnd_1245618 94755666058105592229113 := by
  unfold tailWord_1245618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11357855200336548865710377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30287613867564130308561005 11357855200336548865710377)
  ·
    refine ⟨8518391400252411649282783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11357855200336548865710377 8518391400252411649282783)
    ·
      refine ⟨12777587100378617473924175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8518391400252411649282783 12777587100378617473924175)
      ·
        refine ⟨19166380650567926210886263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12777587100378617473924175 19166380650567926210886263)
        ·
          refine ⟨28749570975851889316329395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19166380650567926210886263 28749570975851889316329395)
          ·
            refine ⟨43124356463777833974494093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28749570975851889316329395 43124356463777833974494093)
            ·
              refine ⟨16171633673916687740435285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43124356463777833974494093 16171633673916687740435285)
              ·
                refine ⟨94755666058105592229113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16171633673916687740435285 94755666058105592229113)
                ·
                  rfl

theorem cell21_1245618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_1245618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245618 prefixEnd_1245618 := by exact prefixLift 1245618
  have htrace : WordTrace (prefixWord ++ tailWord_1245618) baseStart_1245618 baseEnd_1245618 := by
    simpa [prefixWord, tailWord_1245618, baseEnd_1245618] using wordTrace_append hprefix tailTrace_1245618
  have hstable : (prefixWord ++ tailWord_1245618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245618).length < 2 ^ (prefixWord ++ tailWord_1245618).sum := by decide
  have hdescent : baseEnd_1245618 < baseStart_1245618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245652 : List Nat := [2, 4, 1, 2, 2, 3, 1, 6]
def baseStart_1245652 : Nat := 118140960795 + 1245652 * 2 ^ 59
def prefixEnd_1245652 : Nat := 4983230072969 + 3 ^ 40 * 1245652 * 2
def baseEnd_1245652 : Nat := 94758252479180091040201

theorem tailTrace_1245652 : CollatzResearch.WordTrace tailWord_1245652 prefixEnd_1245652 94758252479180091040201 := by
  unfold tailWord_1245652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22716330441611509634789605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30288440588815346179719473 22716330441611509634789605)
  ·
    refine ⟨4259311957802158056523051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22716330441611509634789605 4259311957802158056523051)
    ·
      refine ⟨6388967936703237084784577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4259311957802158056523051 6388967936703237084784577)
      ·
        refine ⟨4791725952527427813588433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6388967936703237084784577 4791725952527427813588433)
        ·
          refine ⟨3593794464395570860191325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4791725952527427813588433 3593794464395570860191325)
          ·
            refine ⟨1347672924148339072571747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3593794464395570860191325 1347672924148339072571747)
            ·
              refine ⟨2021509386222508608857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347672924148339072571747 2021509386222508608857621)
              ·
                refine ⟨94758252479180091040201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2021509386222508608857621 94758252479180091040201)
                ·
                  rfl

theorem cell21_1245652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_1245652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245652 prefixEnd_1245652 := by exact prefixLift 1245652
  have htrace : WordTrace (prefixWord ++ tailWord_1245652) baseStart_1245652 baseEnd_1245652 := by
    simpa [prefixWord, tailWord_1245652, baseEnd_1245652] using wordTrace_append hprefix tailTrace_1245652
  have hstable : (prefixWord ++ tailWord_1245652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245652).length < 2 ^ (prefixWord ++ tailWord_1245652).sum := by decide
  have hdescent : baseEnd_1245652 < baseStart_1245652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245697 : List Nat := [1, 2, 4, 1, 3, 1, 3, 2, 4]
def baseStart_1245697 : Nat := 118140960795 + 1245697 * 2 ^ 59
def prefixEnd_1245697 : Nat := 4983230072969 + 3 ^ 40 * 1245697 * 2
def baseEnd_1245697 : Nat := 284285027050630194870511

theorem tailTrace_1245697 : CollatzResearch.WordTrace tailWord_1245697 prefixEnd_1245697 284285027050630194870511 := by
  unfold tailWord_1245697
  simp only [CollatzResearch.WordTrace]
  refine ⟨45434302168059991954967345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30289534778706661303311563 45434302168059991954967345)
  ·
    refine ⟨34075726626044993966225509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45434302168059991954967345 34075726626044993966225509)
    ·
      refine ⟨6389198742383436368667283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34075726626044993966225509 6389198742383436368667283)
      ·
        refine ⟨9583798113575154553000925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6389198742383436368667283 9583798113575154553000925)
        ·
          refine ⟨3593924292590682957375347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9583798113575154553000925 3593924292590682957375347)
          ·
            refine ⟨5390886438886024436063021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3593924292590682957375347 5390886438886024436063021)
            ·
              refine ⟨2021582414582259163523633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5390886438886024436063021 2021582414582259163523633)
              ·
                refine ⟨1516186810936694372642725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021582414582259163523633 1516186810936694372642725)
                ·
                  refine ⟨284285027050630194870511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516186810936694372642725 284285027050630194870511)
                  ·
                    rfl

theorem cell21_1245697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2, 4].length) (baseStart_1245697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245697 prefixEnd_1245697 := by exact prefixLift 1245697
  have htrace : WordTrace (prefixWord ++ tailWord_1245697) baseStart_1245697 baseEnd_1245697 := by
    simpa [prefixWord, tailWord_1245697, baseEnd_1245697] using wordTrace_append hprefix tailTrace_1245697
  have hstable : (prefixWord ++ tailWord_1245697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245697).length < 2 ^ (prefixWord ++ tailWord_1245697).sum := by decide
  have hdescent : baseEnd_1245697 < baseStart_1245697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245756 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 6]
def baseStart_1245756 : Nat := 118140960795 + 1245756 * 2 ^ 59
def prefixEnd_1245756 : Nat := 4983230072969 + 3 ^ 40 * 1245756 * 2
def baseEnd_1245756 : Nat := 284298491654459203387057

theorem tailTrace_1245756 : CollatzResearch.WordTrace tailWord_1245756 prefixEnd_1245756 284298491654459203387057 := by
  unfold tailWord_1245756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22718227037423122515682561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30290969383230830020910081 22718227037423122515682561)
  ·
    refine ⟨17038670278067341886761921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22718227037423122515682561 17038670278067341886761921)
    ·
      refine ⟨12779002708550506415071441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17038670278067341886761921 12779002708550506415071441)
      ·
        refine ⟨9584252031412879811303581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12779002708550506415071441 9584252031412879811303581)
        ·
          refine ⟨3594094511779829929238843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9584252031412879811303581 3594094511779829929238843)
          ·
            refine ⟨5391141767669744893858265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594094511779829929238843 5391141767669744893858265)
            ·
              refine ⟨4043356325752308670393699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5391141767669744893858265 4043356325752308670393699)
              ·
                refine ⟨6065034488628463005590549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043356325752308670393699 6065034488628463005590549)
                ·
                  refine ⟨284298491654459203387057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065034488628463005590549 284298491654459203387057)
                  ·
                    rfl

theorem cell21_1245756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 6].length) (baseStart_1245756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245756 prefixEnd_1245756 := by exact prefixLift 1245756
  have htrace : WordTrace (prefixWord ++ tailWord_1245756) baseStart_1245756 baseEnd_1245756 := by
    simpa [prefixWord, tailWord_1245756, baseEnd_1245756] using wordTrace_append hprefix tailTrace_1245756
  have hstable : (prefixWord ++ tailWord_1245756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245756).length < 2 ^ (prefixWord ++ tailWord_1245756).sum := by decide
  have hdescent : baseEnd_1245756 < baseStart_1245756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245759 : List Nat := [1, 1, 2, 2, 3, 2, 5, 2, 3]
def baseStart_1245759 : Nat := 118140960795 + 1245759 * 2 ^ 59
def prefixEnd_1245759 : Nat := 4983230072969 + 3 ^ 40 * 1245759 * 2
def baseEnd_1245759 : Nat := 284299176295331864837051

theorem tailTrace_1245759 : CollatzResearch.WordTrace tailWord_1245759 prefixEnd_1245759 284299176295331864837051 := by
  unfold tailWord_1245759
  simp only [CollatzResearch.WordTrace]
  refine ⟨45436563493835376543724331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30291042329223584362482887 45436563493835376543724331)
  ·
    refine ⟨68154845240753064815586497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45436563493835376543724331 68154845240753064815586497)
    ·
      refine ⟨51116133930564798611689873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68154845240753064815586497 51116133930564798611689873)
      ·
        refine ⟨38337100447923598958767405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51116133930564798611689873 38337100447923598958767405)
        ·
          refine ⟨14376412667971349609537777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38337100447923598958767405 14376412667971349609537777)
          ·
            refine ⟨10782309500978512207153333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14376412667971349609537777 10782309500978512207153333)
            ·
              refine ⟨1010841515716735519420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10782309500978512207153333 1010841515716735519420625)
              ·
                refine ⟨758131136787551639565469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010841515716735519420625 758131136787551639565469)
                ·
                  refine ⟨284299176295331864837051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758131136787551639565469 284299176295331864837051)
                  ·
                    rfl

theorem cell21_1245759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 2, 3].length) (baseStart_1245759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245759 prefixEnd_1245759 := by exact prefixLift 1245759
  have htrace : WordTrace (prefixWord ++ tailWord_1245759) baseStart_1245759 baseEnd_1245759 := by
    simpa [prefixWord, tailWord_1245759, baseEnd_1245759] using wordTrace_append hprefix tailTrace_1245759
  have hstable : (prefixWord ++ tailWord_1245759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245759).length < 2 ^ (prefixWord ++ tailWord_1245759).sum := by decide
  have hdescent : baseEnd_1245759 < baseStart_1245759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245770 : List Nat := [3, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1245770 : Nat := 118140960795 + 1245770 * 2 ^ 59
def prefixEnd_1245770 : Nat := 4983230072969 + 3 ^ 40 * 1245770 * 2
def baseEnd_1245770 : Nat := 94767228881732763384565

theorem tailTrace_1245770 : CollatzResearch.WordTrace tailWord_1245770 prefixEnd_1245770 94767228881732763384565 := by
  unfold tailWord_1245770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11359241174198881355593691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30291309797863683614916509 11359241174198881355593691)
  ·
    refine ⟨17038861761298322033390537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11359241174198881355593691 17038861761298322033390537)
    ·
      refine ⟨12779146320973741525042903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17038861761298322033390537 12779146320973741525042903)
      ·
        refine ⟨19168719481460612287564355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12779146320973741525042903 19168719481460612287564355)
        ·
          refine ⟨28753079222190918431346533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19168719481460612287564355 28753079222190918431346533)
          ·
            refine ⟨5391202354160797205877475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28753079222190918431346533 5391202354160797205877475)
            ·
              refine ⟨8086803531241195808816213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5391202354160797205877475 8086803531241195808816213)
              ·
                refine ⟨94767228881732763384565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8086803531241195808816213 94767228881732763384565)
                ·
                  rfl

theorem cell21_1245770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1245770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245770 prefixEnd_1245770 := by exact prefixLift 1245770
  have htrace : WordTrace (prefixWord ++ tailWord_1245770) baseStart_1245770 baseEnd_1245770 := by
    simpa [prefixWord, tailWord_1245770, baseEnd_1245770] using wordTrace_append hprefix tailTrace_1245770
  have hstable : (prefixWord ++ tailWord_1245770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245770).length < 2 ^ (prefixWord ++ tailWord_1245770).sum := by decide
  have hdescent : baseEnd_1245770 < baseStart_1245770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245815 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_1245815 : Nat := 118140960795 + 1245815 * 2 ^ 59
def prefixEnd_1245815 : Nat := 4983230072969 + 3 ^ 40 * 1245815 * 2
def baseEnd_1245815 : Nat := 284311956258288211903603

theorem tailTrace_1245815 : CollatzResearch.WordTrace tailWord_1245815 prefixEnd_1245815 284311956258288211903603 := by
  unfold tailWord_1245815
  simp only [CollatzResearch.WordTrace]
  refine ⟨45438605981632498107762899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30292403987754998738508599 45438605981632498107762899)
  ·
    refine ⟨68157908972448747161644349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45438605981632498107762899 68157908972448747161644349)
    ·
      refine ⟨25559215864668280185616631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68157908972448747161644349 25559215864668280185616631)
      ·
        refine ⟨38338823797002420278424947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25559215864668280185616631 38338823797002420278424947)
        ·
          refine ⟨57508235695503630417637421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38338823797002420278424947 57508235695503630417637421)
          ·
            refine ⟨21565588385813861406614033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57508235695503630417637421 21565588385813861406614033)
            ·
              refine ⟨16174191289360396054960525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21565588385813861406614033 16174191289360396054960525)
              ·
                refine ⟨6065321733510148520610197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16174191289360396054960525 6065321733510148520610197)
                ·
                  refine ⟨284311956258288211903603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065321733510148520610197 284311956258288211903603)
                  ·
                    rfl

theorem cell21_1245815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_1245815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245815 prefixEnd_1245815 := by exact prefixLift 1245815
  have htrace : WordTrace (prefixWord ++ tailWord_1245815) baseStart_1245815 baseEnd_1245815 := by
    simpa [prefixWord, tailWord_1245815, baseEnd_1245815] using wordTrace_append hprefix tailTrace_1245815
  have hstable : (prefixWord ++ tailWord_1245815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245815).length < 2 ^ (prefixWord ++ tailWord_1245815).sum := by decide
  have hdescent : baseEnd_1245815 < baseStart_1245815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245866 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_1245866 : Nat := 118140960795 + 1245866 * 2 ^ 59
def prefixEnd_1245866 : Nat := 4983230072969 + 3 ^ 40 * 1245866 * 2
def baseEnd_1245866 : Nat := 284323595153123456553499

theorem tailTrace_1245866 : CollatzResearch.WordTrace tailWord_1245866 prefixEnd_1245866 284323595153123456553499 := by
  unfold tailWord_1245866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11360116526111933454467363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30293644069631822545246301 11360116526111933454467363)
  ·
    refine ⟨17040174789167900181701045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11360116526111933454467363 17040174789167900181701045)
    ·
      refine ⟨1597516386484490642034473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17040174789167900181701045 1597516386484490642034473)
      ·
        refine ⟨1198137289863367981525855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1597516386484490642034473 1198137289863367981525855)
        ·
          refine ⟨1797205934795051972288783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198137289863367981525855 1797205934795051972288783)
          ·
            refine ⟨2695808902192577958433175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797205934795051972288783 2695808902192577958433175)
            ·
              refine ⟨4043713353288866937649763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2695808902192577958433175 4043713353288866937649763)
              ·
                refine ⟨6065570029933300406474645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4043713353288866937649763 6065570029933300406474645)
                ·
                  refine ⟨284323595153123456553499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6065570029933300406474645 284323595153123456553499)
                  ·
                    rfl

theorem cell21_1245866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_1245866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245866 prefixEnd_1245866 := by exact prefixLift 1245866
  have htrace : WordTrace (prefixWord ++ tailWord_1245866) baseStart_1245866 baseEnd_1245866 := by
    simpa [prefixWord, tailWord_1245866, baseEnd_1245866] using wordTrace_append hprefix tailTrace_1245866
  have hstable : (prefixWord ++ tailWord_1245866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245866).length < 2 ^ (prefixWord ++ tailWord_1245866).sum := by decide
  have hdescent : baseEnd_1245866 < baseStart_1245866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245911 : List Nat := [1, 1, 3, 2, 1, 6, 1, 3, 3]
def baseStart_1245911 : Nat := 118140960795 + 1245911 * 2 ^ 59
def prefixEnd_1245911 : Nat := 4983230072969 + 3 ^ 40 * 1245911 * 2
def baseEnd_1245911 : Nat := 284333864766213378303407

theorem tailTrace_1245911 : CollatzResearch.WordTrace tailWord_1245911 prefixEnd_1245911 284333864766213378303407 := by
  unfold tailWord_1245911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45442107389284706503257587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30294738259523137668838391 45442107389284706503257587)
  ·
    refine ⟨68163161083927059754886381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45442107389284706503257587 68163161083927059754886381)
    ·
      refine ⟨25561185406472647408082393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68163161083927059754886381 25561185406472647408082393)
      ·
        refine ⟨19170889054854485556061795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25561185406472647408082393 19170889054854485556061795)
        ·
          refine ⟨28756333582281728334092693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19170889054854485556061795 28756333582281728334092693)
          ·
            refine ⟨1347953136669456015660595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28756333582281728334092693 1347953136669456015660595)
            ·
              refine ⟨2021929705004184023490893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347953136669456015660595 2021929705004184023490893)
              ·
                refine ⟨758223639376569008809085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2021929705004184023490893 758223639376569008809085)
                ·
                  refine ⟨284333864766213378303407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758223639376569008809085 284333864766213378303407)
                  ·
                    rfl

theorem cell21_1245911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].length) (baseStart_1245911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245911 prefixEnd_1245911 := by exact prefixLift 1245911
  have htrace : WordTrace (prefixWord ++ tailWord_1245911) baseStart_1245911 baseEnd_1245911 := by
    simpa [prefixWord, tailWord_1245911, baseEnd_1245911] using wordTrace_append hprefix tailTrace_1245911
  have hstable : (prefixWord ++ tailWord_1245911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245911).length < 2 ^ (prefixWord ++ tailWord_1245911).sum := by decide
  have hdescent : baseEnd_1245911 < baseStart_1245911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245928 : List Nat := [2, 1, 4, 1, 4, 1, 3, 2, 3]
def baseStart_1245928 : Nat := 118140960795 + 1245928 * 2 ^ 59
def prefixEnd_1245928 : Nat := 4983230072969 + 3 ^ 40 * 1245928 * 2
def baseEnd_1245928 : Nat := 284337744397825126520039

theorem tailTrace_1245928 : CollatzResearch.WordTrace tailWord_1245928 prefixEnd_1245928 284337744397825126520039 := by
  unfold tailWord_1245928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721363715111559203313219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30295151620148745604417625 22721363715111559203313219)
  ·
    refine ⟨34082045572667338804969829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22721363715111559203313219 34082045572667338804969829)
    ·
      refine ⟨6390383544875126025931843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34082045572667338804969829 6390383544875126025931843)
      ·
        refine ⟨9585575317312689038897765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6390383544875126025931843 9585575317312689038897765)
        ·
          refine ⟨1797295371996129194793331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9585575317312689038897765 1797295371996129194793331)
          ·
            refine ⟨2695943057994193792189997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797295371996129194793331 2695943057994193792189997)
            ·
              refine ⟨1010978646747822672071249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2695943057994193792189997 1010978646747822672071249)
              ·
                refine ⟨758233985060867004053437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010978646747822672071249 758233985060867004053437)
                ·
                  refine ⟨284337744397825126520039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758233985060867004053437 284337744397825126520039)
                  ·
                    rfl

theorem cell21_1245928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 2, 3].length) (baseStart_1245928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245928 prefixEnd_1245928 := by exact prefixLift 1245928
  have htrace : WordTrace (prefixWord ++ tailWord_1245928) baseStart_1245928 baseEnd_1245928 := by
    simpa [prefixWord, tailWord_1245928, baseEnd_1245928] using wordTrace_append hprefix tailTrace_1245928
  have hstable : (prefixWord ++ tailWord_1245928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245928).length < 2 ^ (prefixWord ++ tailWord_1245928).sum := by decide
  have hdescent : baseEnd_1245928 < baseStart_1245928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1245984 : List Nat := [2, 1, 1, 5, 1, 2, 1, 4, 4]
def baseStart_1245984 : Nat := 118140960795 + 1245984 * 2 ^ 59
def prefixEnd_1245984 : Nat := 4983230072969 + 3 ^ 40 * 1245984 * 2
def baseEnd_1245984 : Nat := 284350524360781473586591

theorem tailTrace_1245984 : CollatzResearch.WordTrace tailWord_1245984 prefixEnd_1245984 284350524360781473586591 := by
  unfold tailWord_1245984
  simp only [CollatzResearch.WordTrace]
  refine ⟨22722384959010119985332503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30296513278680159980443337 22722384959010119985332503)
  ·
    refine ⟨34083577438515179977998755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22722384959010119985332503 34083577438515179977998755)
    ·
      refine ⟨51125366157772769966998133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34083577438515179977998755 51125366157772769966998133)
      ·
        refine ⟨4793003077291197184406075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51125366157772769966998133 4793003077291197184406075)
        ·
          refine ⟨7189504615936795776609113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793003077291197184406075 7189504615936795776609113)
          ·
            refine ⟨5392128461952596832456835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7189504615936795776609113 5392128461952596832456835)
            ·
              refine ⟨8088192692928895248685253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5392128461952596832456835 8088192692928895248685253)
              ·
                refine ⟨1516536129924167859128485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8088192692928895248685253 1516536129924167859128485)
                ·
                  refine ⟨284350524360781473586591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516536129924167859128485 284350524360781473586591)
                  ·
                    rfl

theorem cell21_1245984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 4, 4].length) (baseStart_1245984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1245984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1245984 prefixEnd_1245984 := by exact prefixLift 1245984
  have htrace : WordTrace (prefixWord ++ tailWord_1245984) baseStart_1245984 baseEnd_1245984 := by
    simpa [prefixWord, tailWord_1245984, baseEnd_1245984] using wordTrace_append hprefix tailTrace_1245984
  have hstable : (prefixWord ++ tailWord_1245984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1245984).length < 2 ^ (prefixWord ++ tailWord_1245984).sum := by decide
  have hdescent : baseEnd_1245984 < baseStart_1245984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1245984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246015 : List Nat := [1, 1, 2, 2, 5, 2, 3, 5]
def baseStart_1246015 : Nat := 118140960795 + 1246015 * 2 ^ 59
def prefixEnd_1246015 : Nat := 4983230072969 + 3 ^ 40 * 1246015 * 2
def baseEnd_1246015 : Nat := 94785866327710769523287

theorem tailTrace_1246015 : CollatzResearch.WordTrace tailWord_1246015 prefixEnd_1246015 94785866327710769523287 := by
  unfold tailWord_1246015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45445900580907932265043499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30297267053938621510028999 45445900580907932265043499)
  ·
    refine ⟨68168850871361898397565249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45445900580907932265043499 68168850871361898397565249)
    ·
      refine ⟨51126638153521423798173937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68168850871361898397565249 51126638153521423798173937)
      ·
        refine ⟨38344978615141067848630453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51126638153521423798173937 38344978615141067848630453)
        ·
          refine ⟨3594841745169475110809105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38344978615141067848630453 3594841745169475110809105)
          ·
            refine ⟨2696131308877106333106829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3594841745169475110809105 2696131308877106333106829)
            ·
              refine ⟨1011049240828914874915061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2696131308877106333106829 1011049240828914874915061)
              ·
                refine ⟨94785866327710769523287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011049240828914874915061 94785866327710769523287)
                ·
                  rfl

theorem cell21_1246015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 3, 5].length) (baseStart_1246015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246015 prefixEnd_1246015 := by exact prefixLift 1246015
  have htrace : WordTrace (prefixWord ++ tailWord_1246015) baseStart_1246015 baseEnd_1246015 := by
    simpa [prefixWord, tailWord_1246015, baseEnd_1246015] using wordTrace_append hprefix tailTrace_1246015
  have hstable : (prefixWord ++ tailWord_1246015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246015).length < 2 ^ (prefixWord ++ tailWord_1246015).sum := by decide
  have hdescent : baseEnd_1246015 < baseStart_1246015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246229 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 4]
def baseStart_1246229 : Nat := 118140960795 + 1246229 * 2 ^ 59
def prefixEnd_1246229 : Nat := 4983230072969 + 3 ^ 40 * 1246229 * 2
def baseEnd_1246229 : Nat := 284406436698715492002757

theorem tailTrace_1246229 : CollatzResearch.WordTrace tailWord_1246229 prefixEnd_1246229 284406436698715492002757 := by
  unfold tailWord_1246229
  simp only [CollatzResearch.WordTrace]
  refine ⟨45453705802132646813333741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30302470534755097875555827 45453705802132646813333741)
  ·
    refine ⟨17045139675799742555000153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45453705802132646813333741 17045139675799742555000153)
    ·
      refine ⟨12783854756849806916250115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17045139675799742555000153 12783854756849806916250115)
      ·
        refine ⟨19175782135274710374375173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12783854756849806916250115 19175782135274710374375173)
        ·
          refine ⟨3595459150364008195195345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19175782135274710374375173 3595459150364008195195345)
          ·
            refine ⟨2696594362773006146396509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3595459150364008195195345 2696594362773006146396509)
            ·
              refine ⟨1011222886039877304898691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2696594362773006146396509 1011222886039877304898691)
              ·
                refine ⟨1516834329059815957348037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011222886039877304898691 1516834329059815957348037)
                ·
                  refine ⟨284406436698715492002757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516834329059815957348037 284406436698715492002757)
                  ·
                    rfl

theorem cell21_1246229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_1246229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246229 prefixEnd_1246229 := by exact prefixLift 1246229
  have htrace : WordTrace (prefixWord ++ tailWord_1246229) baseStart_1246229 baseEnd_1246229 := by
    simpa [prefixWord, tailWord_1246229, baseEnd_1246229] using wordTrace_append hprefix tailTrace_1246229
  have hstable : (prefixWord ++ tailWord_1246229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246229).length < 2 ^ (prefixWord ++ tailWord_1246229).sum := by decide
  have hdescent : baseEnd_1246229 < baseStart_1246229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246243 : List Nat := [1, 1, 1, 4, 3, 4, 2, 5]
def baseStart_1246243 : Nat := 118140960795 + 1246243 * 2 ^ 59
def prefixEnd_1246243 : Nat := 4983230072969 + 3 ^ 40 * 1246243 * 2
def baseEnd_1246243 : Nat := 94803210563151526256465

theorem tailTrace_1246243 : CollatzResearch.WordTrace tailWord_1246243 prefixEnd_1246243 94803210563151526256465 := by
  unfold tailWord_1246243
  simp only [CollatzResearch.WordTrace]
  refine ⟨45454216424081927204343383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30302810949387951469562255 45454216424081927204343383)
  ·
    refine ⟨68181324636122890806515075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45454216424081927204343383 68181324636122890806515075)
    ·
      refine ⟨102271986954184336209772613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68181324636122890806515075 102271986954184336209772613)
      ·
        refine ⟨19175997553909563039332365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102271986954184336209772613 19175997553909563039332365)
        ·
          refine ⟨7190999082716086139749637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19175997553909563039332365 7190999082716086139749637)
          ·
            refine ⟨1348312328009266151203057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7190999082716086139749637 1348312328009266151203057)
            ·
              refine ⟨1011234246006949613402293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348312328009266151203057 1011234246006949613402293)
              ·
                refine ⟨94803210563151526256465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011234246006949613402293 94803210563151526256465)
                ·
                  rfl

theorem cell21_1246243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 2, 5].length) (baseStart_1246243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246243 prefixEnd_1246243 := by exact prefixLift 1246243
  have htrace : WordTrace (prefixWord ++ tailWord_1246243) baseStart_1246243 baseEnd_1246243 := by
    simpa [prefixWord, tailWord_1246243, baseEnd_1246243] using wordTrace_append hprefix tailTrace_1246243
  have hstable : (prefixWord ++ tailWord_1246243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246243).length < 2 ^ (prefixWord ++ tailWord_1246243).sum := by decide
  have hdescent : baseEnd_1246243 < baseStart_1246243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246271 : List Nat := [1, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_1246271 : Nat := 118140960795 + 1246271 * 2 ^ 59
def prefixEnd_1246271 : Nat := 4983230072969 + 3 ^ 40 * 1246271 * 2
def baseEnd_1246271 : Nat := 284416021670932752302671

theorem tailTrace_1246271 : CollatzResearch.WordTrace tailWord_1246271 prefixEnd_1246271 284416021670932752302671 := by
  unfold tailWord_1246271
  simp only [CollatzResearch.WordTrace]
  refine ⟨45455237667980487986362667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30303491778653658657575111 45455237667980487986362667)
  ·
    refine ⟨68182856501970731979544001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45455237667980487986362667 68182856501970731979544001)
    ·
      refine ⟨51137142376478048984658001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68182856501970731979544001 51137142376478048984658001)
      ·
        refine ⟨38352856782358536738493501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51137142376478048984658001 38352856782358536738493501)
        ·
          refine ⟨14382321293384451276935063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38352856782358536738493501 14382321293384451276935063)
          ·
            refine ⟨21573481940076676915402595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14382321293384451276935063 21573481940076676915402595)
            ·
              refine ⟨32360222910115015373103893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21573481940076676915402595 32360222910115015373103893)
              ·
                refine ⟨1516885448911641345614245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32360222910115015373103893 1516885448911641345614245)
                ·
                  refine ⟨284416021670932752302671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1516885448911641345614245 284416021670932752302671)
                  ·
                    rfl

theorem cell21_1246271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_1246271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246271 prefixEnd_1246271 := by exact prefixLift 1246271
  have htrace : WordTrace (prefixWord ++ tailWord_1246271) baseStart_1246271 baseEnd_1246271 := by
    simpa [prefixWord, tailWord_1246271, baseEnd_1246271] using wordTrace_append hprefix tailTrace_1246271
  have hstable : (prefixWord ++ tailWord_1246271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246271).length < 2 ^ (prefixWord ++ tailWord_1246271).sum := by decide
  have hdescent : baseEnd_1246271 < baseStart_1246271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246325 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 3]
def baseStart_1246325 : Nat := 118140960795 + 1246325 * 2 ^ 59
def prefixEnd_1246325 : Nat := 4983230072969 + 3 ^ 40 * 1246325 * 2
def baseEnd_1246325 : Nat := 284428345206640658402561

theorem tailTrace_1246325 : CollatzResearch.WordTrace tailWord_1246325 prefixEnd_1246325 284428345206640658402561 := by
  unfold tailWord_1246325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45457207209784855208828429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30304804806523236805885619 45457207209784855208828429)
  ·
    refine ⟨17046452703669320703310661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45457207209784855208828429 17046452703669320703310661)
    ·
      refine ⟨3196209881937997631870749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17046452703669320703310661 3196209881937997631870749)
      ·
        refine ⟨1198578705726749111951531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3196209881937997631870749 1198578705726749111951531)
        ·
          refine ⟨1797868058590123667927297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198578705726749111951531 1797868058590123667927297)
          ·
            refine ⟨1348401043942592750945473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797868058590123667927297 1348401043942592750945473)
            ·
              refine ⟨1011300782956944563209105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348401043942592750945473 1011300782956944563209105)
              ·
                refine ⟨758475587217708422406829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011300782956944563209105 758475587217708422406829)
                ·
                  refine ⟨284428345206640658402561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758475587217708422406829 284428345206640658402561)
                  ·
                    rfl

theorem cell21_1246325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_1246325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246325 prefixEnd_1246325 := by exact prefixLift 1246325
  have htrace : WordTrace (prefixWord ++ tailWord_1246325) baseStart_1246325 baseEnd_1246325 := by
    simpa [prefixWord, tailWord_1246325, baseEnd_1246325] using wordTrace_append hprefix tailTrace_1246325
  have hstable : (prefixWord ++ tailWord_1246325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246325).length < 2 ^ (prefixWord ++ tailWord_1246325).sum := by decide
  have hdescent : baseEnd_1246325 < baseStart_1246325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246367 : List Nat := [1, 1, 2, 6, 2, 1, 2, 3, 3]
def baseStart_1246367 : Nat := 118140960795 + 1246367 * 2 ^ 59
def prefixEnd_1246367 : Nat := 4983230072969 + 3 ^ 40 * 1246367 * 2
def baseEnd_1246367 : Nat := 284437930178857918702475

theorem tailTrace_1246367 : CollatzResearch.WordTrace tailWord_1246367 prefixEnd_1246367 284437930178857918702475 := by
  unfold tailWord_1246367
  simp only [CollatzResearch.WordTrace]
  refine ⟨45458739075632696381857355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30305826050421797587904903 45458739075632696381857355)
  ·
    refine ⟨68188108613449044572786033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45458739075632696381857355 68188108613449044572786033)
    ·
      refine ⟨51141081460086783429589525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68188108613449044572786033 51141081460086783429589525)
      ·
        refine ⟨2397238193441567973262009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 51141081460086783429589525 2397238193441567973262009)
        ·
          refine ⟨1797928645081175979946507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397238193441567973262009 1797928645081175979946507)
          ·
            refine ⟨2696892967621763969919761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797928645081175979946507 2696892967621763969919761)
            ·
              refine ⟨2022669725716322977439821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696892967621763969919761 2022669725716322977439821)
              ·
                refine ⟨758501147143621116539933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022669725716322977439821 758501147143621116539933)
                ·
                  refine ⟨284437930178857918702475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758501147143621116539933 284437930178857918702475)
                  ·
                    rfl

theorem cell21_1246367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].length) (baseStart_1246367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246367 prefixEnd_1246367 := by exact prefixLift 1246367
  have htrace : WordTrace (prefixWord ++ tailWord_1246367) baseStart_1246367 baseEnd_1246367 := by
    simpa [prefixWord, tailWord_1246367, baseEnd_1246367] using wordTrace_append hprefix tailTrace_1246367
  have hstable : (prefixWord ++ tailWord_1246367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246367).length < 2 ^ (prefixWord ++ tailWord_1246367).sum := by decide
  have hdescent : baseEnd_1246367 < baseStart_1246367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246485 : List Nat := [1, 3, 2, 1, 2, 1, 1, 7, 3]
def baseStart_1246485 : Nat := 118140960795 + 1246485 * 2 ^ 59
def prefixEnd_1246485 : Nat := 4983230072969 + 3 ^ 40 * 1246485 * 2
def baseEnd_1246485 : Nat := 284464859386515935735567

theorem tailTrace_1246485 : CollatzResearch.WordTrace tailWord_1246485 prefixEnd_1246485 284464859386515935735567 := by
  unfold tailWord_1246485
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463042889205202534652909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30308695259470135023101939 45463042889205202534652909)
  ·
    refine ⟨17048641083451950950494841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45463042889205202534652909 17048641083451950950494841)
    ·
      refine ⟨12786480812588963212871131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17048641083451950950494841 12786480812588963212871131)
      ·
        refine ⟨19179721218883444819306697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12786480812588963212871131 19179721218883444819306697)
        ·
          refine ⟨14384790914162583614480023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19179721218883444819306697 14384790914162583614480023)
          ·
            refine ⟨21577186371243875421720035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14384790914162583614480023 21577186371243875421720035)
            ·
              refine ⟨32365779556865813132580053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21577186371243875421720035 32365779556865813132580053)
              ·
                refine ⟨758572958364042495294845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 32365779556865813132580053 758572958364042495294845)
                ·
                  refine ⟨284464859386515935735567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758572958364042495294845 284464859386515935735567)
                  ·
                    rfl

theorem cell21_1246485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 7, 3].length) (baseStart_1246485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246485 prefixEnd_1246485 := by exact prefixLift 1246485
  have htrace : WordTrace (prefixWord ++ tailWord_1246485) baseStart_1246485 baseEnd_1246485 := by
    simpa [prefixWord, tailWord_1246485, baseEnd_1246485] using wordTrace_append hprefix tailTrace_1246485
  have hstable : (prefixWord ++ tailWord_1246485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246485).length < 2 ^ (prefixWord ++ tailWord_1246485).sum := by decide
  have hdescent : baseEnd_1246485 < baseStart_1246485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246494 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 3]
def baseStart_1246494 : Nat := 118140960795 + 1246494 * 2 ^ 59
def prefixEnd_1246494 : Nat := 4983230072969 + 3 ^ 40 * 1246494 * 2
def baseEnd_1246494 : Nat := 284466913309133920085549

theorem tailTrace_1246494 : CollatzResearch.WordTrace tailWord_1246494 prefixEnd_1246494 284466913309133920085549 := by
  unfold tailWord_1246494
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682921393271574633966317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30308914097448398047820357 5682921393271574633966317)
  ·
    refine ⟨2131095522476840487737369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5682921393271574633966317 2131095522476840487737369)
    ·
      refine ⟨1598321641857630365803027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131095522476840487737369 1598321641857630365803027)
      ·
        refine ⟨2397482462786445548704541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598321641857630365803027 2397482462786445548704541)
        ·
          refine ⟨899055923544917080764203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2397482462786445548704541 899055923544917080764203)
          ·
            refine ⟨1348583885317375621146305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899055923544917080764203 1348583885317375621146305)
            ·
              refine ⟨1011437913988031715859729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348583885317375621146305 1011437913988031715859729)
              ·
                refine ⟨758578435491023786894797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011437913988031715859729 758578435491023786894797)
                ·
                  refine ⟨284466913309133920085549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758578435491023786894797 284466913309133920085549)
                  ·
                    rfl

theorem cell21_1246494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_1246494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246494 prefixEnd_1246494 := by exact prefixLift 1246494
  have htrace : WordTrace (prefixWord ++ tailWord_1246494) baseStart_1246494 baseEnd_1246494 := by
    simpa [prefixWord, tailWord_1246494, baseEnd_1246494] using wordTrace_append hprefix tailTrace_1246494
  have hstable : (prefixWord ++ tailWord_1246494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246494).length < 2 ^ (prefixWord ++ tailWord_1246494).sum := by decide
  have hdescent : baseEnd_1246494 < baseStart_1246494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246499 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_1246499 : Nat := 118140960795 + 1246499 * 2 ^ 59
def prefixEnd_1246499 : Nat := 4983230072969 + 3 ^ 40 * 1246499 * 2
def baseEnd_1246499 : Nat := 284468054377255022502205

theorem tailTrace_1246499 : CollatzResearch.WordTrace tailWord_1246499 prefixEnd_1246499 284468054377255022502205 := by
  unfold tailWord_1246499
  simp only [CollatzResearch.WordTrace]
  refine ⟨45463553511154482925662551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30309035674102988617108367 45463553511154482925662551)
  ·
    refine ⟨68195330266731724388493827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45463553511154482925662551 68195330266731724388493827)
    ·
      refine ⟨102292995400097586582740741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68195330266731724388493827 102292995400097586582740741)
      ·
        refine ⟨19179936637518297484263889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102292995400097586582740741 19179936637518297484263889)
        ·
          refine ⟨14384952478138723113197917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19179936637518297484263889 14384952478138723113197917)
          ·
            refine ⟨5394357179302021167449219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14384952478138723113197917 5394357179302021167449219)
            ·
              refine ⟨8091535768953031751173829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5394357179302021167449219 8091535768953031751173829)
              ·
                refine ⟨1517162956678693453345093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8091535768953031751173829 1517162956678693453345093)
                ·
                  refine ⟨284468054377255022502205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517162956678693453345093 284468054377255022502205)
                  ·
                    rfl

theorem cell21_1246499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_1246499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246499 prefixEnd_1246499 := by exact prefixLift 1246499
  have htrace : WordTrace (prefixWord ++ tailWord_1246499) baseStart_1246499 baseEnd_1246499 := by
    simpa [prefixWord, tailWord_1246499, baseEnd_1246499] using wordTrace_append hprefix tailTrace_1246499
  have hstable : (prefixWord ++ tailWord_1246499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246499).length < 2 ^ (prefixWord ++ tailWord_1246499).sum := by decide
  have hdescent : baseEnd_1246499 < baseStart_1246499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246516 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1246516 : Nat := 118140960795 + 1246516 * 2 ^ 59
def prefixEnd_1246516 : Nat := 4983230072969 + 3 ^ 40 * 1246516 * 2
def baseEnd_1246516 : Nat := 284471934008866770718837

theorem tailTrace_1246516 : CollatzResearch.WordTrace tailWord_1246516 prefixEnd_1246516 284471934008866770718837 := by
  unfold tailWord_1246516
  simp only [CollatzResearch.WordTrace]
  refine ⟨22732086776046447414515701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30309449034728596552687601 22732086776046447414515701)
  ·
    refine ⟨2131133135254354445110847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22732086776046447414515701 2131133135254354445110847)
    ·
      refine ⟨3196699702881531667666271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131133135254354445110847 3196699702881531667666271)
      ·
        refine ⟨4795049554322297501499407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196699702881531667666271 4795049554322297501499407)
        ·
          refine ⟨7192574331483446252249111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4795049554322297501499407 7192574331483446252249111)
          ·
            refine ⟨10788861497225169378373667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7192574331483446252249111 10788861497225169378373667)
            ·
              refine ⟨16183292245837754067560501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10788861497225169378373667 16183292245837754067560501)
              ·
                refine ⟨1517183648047289443833797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16183292245837754067560501 1517183648047289443833797)
                ·
                  refine ⟨284471934008866770718837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517183648047289443833797 284471934008866770718837)
                  ·
                    rfl

theorem cell21_1246516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1246516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246516 prefixEnd_1246516 := by exact prefixLift 1246516
  have htrace : WordTrace (prefixWord ++ tailWord_1246516) baseStart_1246516 baseEnd_1246516 := by
    simpa [prefixWord, tailWord_1246516, baseEnd_1246516] using wordTrace_append hprefix tailTrace_1246516
  have hstable : (prefixWord ++ tailWord_1246516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246516).length < 2 ^ (prefixWord ++ tailWord_1246516).sum := by decide
  have hdescent : baseEnd_1246516 < baseStart_1246516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246589 : List Nat := [1, 4, 1, 1, 2, 2, 3, 7]
def baseStart_1246589 : Nat := 118140960795 + 1246589 * 2 ^ 59
def prefixEnd_1246589 : Nat := 4983230072969 + 3 ^ 40 * 1246589 * 2
def baseEnd_1246589 : Nat := 94829531201144955334007

theorem tailTrace_1246589 : CollatzResearch.WordTrace tailWord_1246589 prefixEnd_1246589 94829531201144955334007 := by
  unfold tailWord_1246589
  simp only [CollatzResearch.WordTrace]
  refine ⟨45466836080828428296438821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30311224053885618864292547 45466836080828428296438821)
  ·
    refine ⟨8525031765155330305582279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45466836080828428296438821 8525031765155330305582279)
    ·
      refine ⟨12787547647732995458373419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525031765155330305582279 12787547647732995458373419)
      ·
        refine ⟨19181321471599493187560129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12787547647732995458373419 19181321471599493187560129)
        ·
          refine ⟨14385991103699619890670097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19181321471599493187560129 14385991103699619890670097)
          ·
            refine ⟨10789493327774714918002573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14385991103699619890670097 10789493327774714918002573)
            ·
              refine ⟨4046059997915518094250965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10789493327774714918002573 4046059997915518094250965)
              ·
                refine ⟨94829531201144955334007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4046059997915518094250965 94829531201144955334007)
                ·
                  rfl

theorem cell21_1246589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_1246589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246589 prefixEnd_1246589 := by exact prefixLift 1246589
  have htrace : WordTrace (prefixWord ++ tailWord_1246589) baseStart_1246589 baseEnd_1246589 := by
    simpa [prefixWord, tailWord_1246589, baseEnd_1246589] using wordTrace_append hprefix tailTrace_1246589
  have hstable : (prefixWord ++ tailWord_1246589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246589).length < 2 ^ (prefixWord ++ tailWord_1246589).sum := by decide
  have hdescent : baseEnd_1246589 < baseStart_1246589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246668 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1246668 : Nat := 118140960795 + 1246668 * 2 ^ 59
def prefixEnd_1246668 : Nat := 4983230072969 + 3 ^ 40 * 1246668 * 2
def baseEnd_1246668 : Nat := 284506622479748284185193

theorem tailTrace_1246668 : CollatzResearch.WordTrace tailWord_1246668 prefixEnd_1246668 284506622479748284185193 := by
  unfold tailWord_1246668
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734858723771112394282329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30313144965028149859043105 22734858723771112394282329)
  ·
    refine ⟨17051144042828334295711747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22734858723771112394282329 17051144042828334295711747)
    ·
      refine ⟨25576716064242501443567621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17051144042828334295711747 25576716064242501443567621)
      ·
        refine ⟨4795634262045469020668929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25576716064242501443567621 4795634262045469020668929)
        ·
          refine ⟨3596725696534101765501697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795634262045469020668929 3596725696534101765501697)
          ·
            refine ⟨2697544272400576324126273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596725696534101765501697 2697544272400576324126273)
            ·
              refine ⟨2023158204300432243094705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697544272400576324126273 2023158204300432243094705)
              ·
                refine ⟨1517368653225324182321029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023158204300432243094705 1517368653225324182321029)
                ·
                  refine ⟨284506622479748284185193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517368653225324182321029 284506622479748284185193)
                  ·
                    rfl

theorem cell21_1246668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1246668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246668 prefixEnd_1246668 := by exact prefixLift 1246668
  have htrace : WordTrace (prefixWord ++ tailWord_1246668) baseStart_1246668 baseEnd_1246668 := by
    simpa [prefixWord, tailWord_1246668, baseEnd_1246668] using wordTrace_append hprefix tailTrace_1246668
  have hstable : (prefixWord ++ tailWord_1246668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246668).length < 2 ^ (prefixWord ++ tailWord_1246668).sum := by decide
  have hdescent : baseEnd_1246668 < baseStart_1246668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246679 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_1246679 : Nat := 118140960795 + 1246679 * 2 ^ 59
def prefixEnd_1246679 : Nat := 4983230072969 + 3 ^ 40 * 1246679 * 2
def baseEnd_1246679 : Nat := 284509132829614709501837

theorem tailTrace_1246679 : CollatzResearch.WordTrace tailWord_1246679 prefixEnd_1246679 284509132829614709501837 := by
  unfold tailWord_1246679
  simp only [CollatzResearch.WordTrace]
  refine ⟨45470118650502373667215091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30313412433668249111476727 45470118650502373667215091)
  ·
    refine ⟨68205177975753560500822637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45470118650502373667215091 68205177975753560500822637)
    ·
      refine ⟨25576941740907585187808489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68205177975753560500822637 25576941740907585187808489)
      ·
        refine ⟨19182706305680688890856367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25576941740907585187808489 19182706305680688890856367)
        ·
          refine ⟨28774059458521033336284551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19182706305680688890856367 28774059458521033336284551)
          ·
            refine ⟨43161089187781550004426827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28774059458521033336284551 43161089187781550004426827)
            ·
              refine ⟨64741633781672325006640241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43161089187781550004426827 64741633781672325006640241)
              ·
                refine ⟨48556225336254243754980181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64741633781672325006640241 48556225336254243754980181)
                ·
                  refine ⟨284509132829614709501837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48556225336254243754980181 284509132829614709501837)
                  ·
                    rfl

theorem cell21_1246679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_1246679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246679 prefixEnd_1246679 := by exact prefixLift 1246679
  have htrace : WordTrace (prefixWord ++ tailWord_1246679) baseStart_1246679 baseEnd_1246679 := by
    simpa [prefixWord, tailWord_1246679, baseEnd_1246679] using wordTrace_append hprefix tailTrace_1246679
  have hstable : (prefixWord ++ tailWord_1246679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246679).length < 2 ^ (prefixWord ++ tailWord_1246679).sum := by decide
  have hdescent : baseEnd_1246679 < baseStart_1246679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246682 : List Nat := [3, 1, 1, 2, 3, 4, 1, 6]
def baseStart_1246682 : Nat := 118140960795 + 1246682 * 2 ^ 59
def prefixEnd_1246682 : Nat := 4983230072969 + 3 ^ 40 * 1246682 * 2
def baseEnd_1246682 : Nat := 94836605823495790317277

theorem tailTrace_1246682 : CollatzResearch.WordTrace tailWord_1246682 prefixEnd_1246682 94836605823495790317277 := by
  unfold tailWord_1246682
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367557017372876294893575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30313485379661003453049533 11367557017372876294893575)
  ·
    refine ⟨17051335526059314442340363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11367557017372876294893575 17051335526059314442340363)
    ·
      refine ⟨25577003289088971663510545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17051335526059314442340363 25577003289088971663510545)
      ·
        refine ⟨19182752466816728747632909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25577003289088971663510545 19182752466816728747632909)
        ·
          refine ⟨7193532175056273280362341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19182752466816728747632909 7193532175056273280362341)
          ·
            refine ⟨1348787282823051240067939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7193532175056273280362341 1348787282823051240067939)
            ·
              refine ⟨2023180924234576860101909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348787282823051240067939 2023180924234576860101909)
              ·
                refine ⟨94836605823495790317277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2023180924234576860101909 94836605823495790317277)
                ·
                  rfl

theorem cell21_1246682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 6].length) (baseStart_1246682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246682 prefixEnd_1246682 := by exact prefixLift 1246682
  have htrace : WordTrace (prefixWord ++ tailWord_1246682) baseStart_1246682 baseEnd_1246682 := by
    simpa [prefixWord, tailWord_1246682, baseEnd_1246682] using wordTrace_append hprefix tailTrace_1246682
  have hstable : (prefixWord ++ tailWord_1246682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246682).length < 2 ^ (prefixWord ++ tailWord_1246682).sum := by decide
  have hdescent : baseEnd_1246682 < baseStart_1246682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246696 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 5]
def baseStart_1246696 : Nat := 118140960795 + 1246696 * 2 ^ 59
def prefixEnd_1246696 : Nat := 4983230072969 + 3 ^ 40 * 1246696 * 2
def baseEnd_1246696 : Nat := 284513012461226457718469

theorem tailTrace_1246696 : CollatzResearch.WordTrace tailWord_1246696 prefixEnd_1246696 284513012461226457718469 := by
  unfold tailWord_1246696
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735369345720392785291971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30313825794293857047055961 22735369345720392785291971)
  ·
    refine ⟨34103054018580589177937957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22735369345720392785291971 34103054018580589177937957)
    ·
      refine ⟨6394322628483860470863367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34103054018580589177937957 6394322628483860470863367)
      ·
        refine ⟨9591483942725790706295051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394322628483860470863367 9591483942725790706295051)
        ·
          refine ⟨14387225914088686059442577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9591483942725790706295051 14387225914088686059442577)
          ·
            refine ⟨10790419435566514544581933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14387225914088686059442577 10790419435566514544581933)
            ·
              refine ⟨4046407288337442954218225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10790419435566514544581933 4046407288337442954218225)
              ·
                refine ⟨3034805466253082215663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4046407288337442954218225 3034805466253082215663669)
                ·
                  refine ⟨284513012461226457718469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3034805466253082215663669 284513012461226457718469)
                  ·
                    rfl

theorem cell21_1246696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 5].length) (baseStart_1246696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246696 prefixEnd_1246696 := by exact prefixLift 1246696
  have htrace : WordTrace (prefixWord ++ tailWord_1246696) baseStart_1246696 baseEnd_1246696 := by
    simpa [prefixWord, tailWord_1246696, baseEnd_1246696] using wordTrace_append hprefix tailTrace_1246696
  have hstable : (prefixWord ++ tailWord_1246696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246696).length < 2 ^ (prefixWord ++ tailWord_1246696).sum := by decide
  have hdescent : baseEnd_1246696 < baseStart_1246696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246727 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 6]
def baseStart_1246727 : Nat := 118140960795 + 1246727 * 2 ^ 59
def prefixEnd_1246727 : Nat := 4983230072969 + 3 ^ 40 * 1246727 * 2
def baseEnd_1246727 : Nat := 284520087083577292701739

theorem tailTrace_1246727 : CollatzResearch.WordTrace tailWord_1246727 prefixEnd_1246727 284520087083577292701739 := by
  unfold tailWord_1246727
  simp only [CollatzResearch.WordTrace]
  refine ⟨45471869354328477864962435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30314579569552318576641623 45471869354328477864962435)
  ·
    refine ⟨68207804031492716797443653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45471869354328477864962435 68207804031492716797443653)
    ·
      refine ⟨12788963255904884399520685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68207804031492716797443653 12788963255904884399520685)
      ·
        refine ⟨4795861220964331649820257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12788963255904884399520685 4795861220964331649820257)
        ·
          refine ⟨3596895915723248737365193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795861220964331649820257 3596895915723248737365193)
          ·
            refine ⟨2697671936792436553023895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596895915723248737365193 2697671936792436553023895)
            ·
              refine ⟨4046507905188654829535843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2697671936792436553023895 4046507905188654829535843)
              ·
                refine ⟨6069761857782982244303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4046507905188654829535843 6069761857782982244303765)
                ·
                  refine ⟨284520087083577292701739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6069761857782982244303765 284520087083577292701739)
                  ·
                    rfl

theorem cell21_1246727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 6].length) (baseStart_1246727 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246727 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246727 prefixEnd_1246727 := by exact prefixLift 1246727
  have htrace : WordTrace (prefixWord ++ tailWord_1246727) baseStart_1246727 baseEnd_1246727 := by
    simpa [prefixWord, tailWord_1246727, baseEnd_1246727] using wordTrace_append hprefix tailTrace_1246727
  have hstable : (prefixWord ++ tailWord_1246727).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246727).length < 2 ^ (prefixWord ++ tailWord_1246727).sum := by decide
  have hdescent : baseEnd_1246727 < baseStart_1246727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246750 : List Nat := [4, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1246750 : Nat := 118140960795 + 1246750 * 2 ^ 59
def prefixEnd_1246750 : Nat := 4983230072969 + 3 ^ 40 * 1246750 * 2
def baseEnd_1246750 : Nat := 94841778665644787939453

theorem tailTrace_1246750 : CollatzResearch.WordTrace tailWord_1246750 prefixEnd_1246750 94841778665644787939453 := by
  unfold tailWord_1246750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5684088529155644099131213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30315138822163435195366469 5684088529155644099131213)
  ·
    refine ⟨2131533198433366537174205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5684088529155644099131213 2131533198433366537174205)
    ·
      refine ⟨799324949412512451440327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2131533198433366537174205 799324949412512451440327)
      ·
        refine ⟨1198987424118768677160491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799324949412512451440327 1198987424118768677160491)
        ·
          refine ⟨1798481136178153015740737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198987424118768677160491 1798481136178153015740737)
          ·
            refine ⟨1348860852133614761805553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798481136178153015740737 1348860852133614761805553)
            ·
              refine ⟨1011645639100211071354165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348860852133614761805553 1011645639100211071354165)
              ·
                refine ⟨94841778665644787939453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011645639100211071354165 94841778665644787939453)
                ·
                  rfl

theorem cell21_1246750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1246750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246750 prefixEnd_1246750 := by exact prefixLift 1246750
  have htrace : WordTrace (prefixWord ++ tailWord_1246750) baseStart_1246750 baseEnd_1246750 := by
    simpa [prefixWord, tailWord_1246750, baseEnd_1246750] using wordTrace_append hprefix tailTrace_1246750
  have hstable : (prefixWord ++ tailWord_1246750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246750).length < 2 ^ (prefixWord ++ tailWord_1246750).sum := by decide
  have hdescent : baseEnd_1246750 < baseStart_1246750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246893 : List Nat := [1, 5, 2, 1, 1, 1, 10]
def baseStart_1246893 : Nat := 118140960795 + 1246893 * 2 ^ 59
def prefixEnd_1246893 : Nat := 4983230072969 + 3 ^ 40 * 1246893 * 2
def baseEnd_1246893 : Nat := 31617552282799765881637

theorem tailTrace_1246893 : CollatzResearch.WordTrace tailWord_1246893 prefixEnd_1246893 31617552282799765881637 := by
  unfold tailWord_1246893
  simp only [CollatzResearch.WordTrace]
  refine ⟨45477923871727088215505333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30318615914484725477003555 45477923871727088215505333)
  ·
    refine ⟨4263555362974414520203625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45477923871727088215505333 4263555362974414520203625)
    ·
      refine ⟨3197666522230810890152719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4263555362974414520203625 3197666522230810890152719)
      ·
        refine ⟨4796499783346216335229079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3197666522230810890152719 4796499783346216335229079)
        ·
          refine ⟨7194749675019324502843619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796499783346216335229079 7194749675019324502843619)
          ·
            refine ⟨10792124512528986754265429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194749675019324502843619 10792124512528986754265429)
            ·
              refine ⟨31617552282799765881637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10792124512528986754265429 31617552282799765881637)
              ·
                rfl

theorem cell21_1246893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 10].length) (baseStart_1246893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246893 prefixEnd_1246893 := by exact prefixLift 1246893
  have htrace : WordTrace (prefixWord ++ tailWord_1246893) baseStart_1246893 baseEnd_1246893 := by
    simpa [prefixWord, tailWord_1246893, baseEnd_1246893] using wordTrace_append hprefix tailTrace_1246893
  have hstable : (prefixWord ++ tailWord_1246893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246893).length < 2 ^ (prefixWord ++ tailWord_1246893).sum := by decide
  have hdescent : baseEnd_1246893 < baseStart_1246893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246938 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1246938 : Nat := 118140960795 + 1246938 * 2 ^ 59
def prefixEnd_1246938 : Nat := 4983230072969 + 3 ^ 40 * 1246938 * 2
def baseEnd_1246938 : Nat := 284568240158287814684641

theorem tailTrace_1246938 : CollatzResearch.WordTrace tailWord_1246938 prefixEnd_1246938 284568240158287814684641 := by
  unfold tailWord_1246938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11369891289141015225223367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30319710104376040600595645 11369891289141015225223367)
  ·
    refine ⟨17054836933711522837835051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11369891289141015225223367 17054836933711522837835051)
    ·
      refine ⟨25582255400567284256752577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17054836933711522837835051 25582255400567284256752577)
      ·
        refine ⟨19186691550425463192564433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25582255400567284256752577 19186691550425463192564433)
        ·
          refine ⟨14390018662819097394423325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19186691550425463192564433 14390018662819097394423325)
          ·
            refine ⟨5396256998557161522908747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14390018662819097394423325 5396256998557161522908747)
            ·
              refine ⟨8094385497835742284363121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5396256998557161522908747 8094385497835742284363121)
              ·
                refine ⟨6070789123376806713272341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8094385497835742284363121 6070789123376806713272341)
                ·
                  refine ⟨284568240158287814684641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6070789123376806713272341 284568240158287814684641)
                  ·
                    rfl

theorem cell21_1246938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1246938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246938 prefixEnd_1246938 := by exact prefixLift 1246938
  have htrace : WordTrace (prefixWord ++ tailWord_1246938) baseStart_1246938 baseEnd_1246938 := by
    simpa [prefixWord, tailWord_1246938, baseEnd_1246938] using wordTrace_append hprefix tailTrace_1246938
  have hstable : (prefixWord ++ tailWord_1246938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246938).length < 2 ^ (prefixWord ++ tailWord_1246938).sum := by decide
  have hdescent : baseEnd_1246938 < baseStart_1246938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1246958 : List Nat := [4, 1, 2, 1, 1, 2, 5, 2, 3]
def baseStart_1246958 : Nat := 118140960795 + 1246958 * 2 ^ 59
def prefixEnd_1246958 : Nat := 4983230072969 + 3 ^ 40 * 1246958 * 2
def baseEnd_1246958 : Nat := 284572804430772224351267

theorem tailTrace_1246958 : CollatzResearch.WordTrace tailWord_1246958 prefixEnd_1246958 284572804430772224351267 := by
  unfold tailWord_1246958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685036827061450539577691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30320196410994402877747685 5685036827061450539577691)
  ·
    refine ⟨8527555240592175809366537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685036827061450539577691 8527555240592175809366537)
    ·
      refine ⟨6395666430444131857024903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527555240592175809366537 6395666430444131857024903)
      ·
        refine ⟨9593499645666197785537355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6395666430444131857024903 9593499645666197785537355)
        ·
          refine ⟨14390249468499296678306033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9593499645666197785537355 14390249468499296678306033)
          ·
            refine ⟨10792687101374472508729525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14390249468499296678306033 10792687101374472508729525)
            ·
              refine ⟨1011814415753856797693393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10792687101374472508729525 1011814415753856797693393)
              ·
                refine ⟨758860811815392598270045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011814415753856797693393 758860811815392598270045)
                ·
                  refine ⟨284572804430772224351267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758860811815392598270045 284572804430772224351267)
                  ·
                    rfl

theorem cell21_1246958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 2, 3].length) (baseStart_1246958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1246958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1246958 prefixEnd_1246958 := by exact prefixLift 1246958
  have htrace : WordTrace (prefixWord ++ tailWord_1246958) baseStart_1246958 baseEnd_1246958 := by
    simpa [prefixWord, tailWord_1246958, baseEnd_1246958] using wordTrace_append hprefix tailTrace_1246958
  have hstable : (prefixWord ++ tailWord_1246958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1246958).length < 2 ^ (prefixWord ++ tailWord_1246958).sum := by decide
  have hdescent : baseEnd_1246958 < baseStart_1246958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1246958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247006 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1247006 : Nat := 118140960795 + 1247006 * 2 ^ 59
def prefixEnd_1247006 : Nat := 4983230072969 + 3 ^ 40 * 1247006 * 2
def baseEnd_1247006 : Nat := 284583758684734807551169

theorem tailTrace_1247006 : CollatzResearch.WordTrace tailWord_1247006 prefixEnd_1247006 284583758684734807551169 := by
  unfold tailWord_1247006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685255665039713564296109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30321363546878472342912581 5685255665039713564296109)
  ·
    refine ⟨2131970874389892586611041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5685255665039713564296109 2131970874389892586611041)
    ·
      refine ⟨1598978155792419439958281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2131970874389892586611041 1598978155792419439958281)
      ·
        refine ⟨1199233616844314579968711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1598978155792419439958281 1199233616844314579968711)
        ·
          refine ⟨1798850425266471869953067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199233616844314579968711 1798850425266471869953067)
          ·
            refine ⟨2698275637899707804929601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798850425266471869953067 2698275637899707804929601)
            ·
              refine ⟨2023706728424780853697201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698275637899707804929601 2023706728424780853697201)
              ·
                refine ⟨1517780046318585640272901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023706728424780853697201 1517780046318585640272901)
                ·
                  refine ⟨284583758684734807551169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1517780046318585640272901 284583758684734807551169)
                  ·
                    rfl

theorem cell21_1247006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1247006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247006 prefixEnd_1247006 := by exact prefixLift 1247006
  have htrace : WordTrace (prefixWord ++ tailWord_1247006) baseStart_1247006 baseEnd_1247006 := by
    simpa [prefixWord, tailWord_1247006, baseEnd_1247006] using wordTrace_append hprefix tailTrace_1247006
  have hstable : (prefixWord ++ tailWord_1247006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247006).length < 2 ^ (prefixWord ++ tailWord_1247006).sum := by decide
  have hdescent : baseEnd_1247006 < baseStart_1247006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247045 : List Nat := [1, 3, 1, 1, 1, 2, 7, 5]
def baseStart_1247045 : Nat := 118140960795 + 1247045 * 2 ^ 59
def prefixEnd_1247045 : Nat := 4983230072969 + 3 ^ 40 * 1247045 * 2
def baseEnd_1247045 : Nat := 94864219672026468800363

theorem tailTrace_1247045 : CollatzResearch.WordTrace tailWord_1247045 prefixEnd_1247045 94864219672026468800363 := by
  unfold tailWord_1247045
  simp only [CollatzResearch.WordTrace]
  refine ⟨45483467767176418175038589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30322311844784278783359059 45483467767176418175038589)
  ·
    refine ⟨17056300412691156815639471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45483467767176418175038589 17056300412691156815639471)
    ·
      refine ⟨25584450619036735223459207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17056300412691156815639471 25584450619036735223459207)
      ·
        refine ⟨38376675928555102835188811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25584450619036735223459207 38376675928555102835188811)
        ·
          refine ⟨57565013892832654252783217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38376675928555102835188811 57565013892832654252783217)
          ·
            refine ⟨43173760419624490689587413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57565013892832654252783217 43173760419624490689587413)
            ·
              refine ⟨1011885009834949000537205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 43173760419624490689587413 1011885009834949000537205)
              ·
                refine ⟨94864219672026468800363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1011885009834949000537205 94864219672026468800363)
                ·
                  rfl

theorem cell21_1247045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 5].length) (baseStart_1247045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247045 prefixEnd_1247045 := by exact prefixLift 1247045
  have htrace : WordTrace (prefixWord ++ tailWord_1247045) baseStart_1247045 baseEnd_1247045 := by
    simpa [prefixWord, tailWord_1247045, baseEnd_1247045] using wordTrace_append hprefix tailTrace_1247045
  have hstable : (prefixWord ++ tailWord_1247045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247045).length < 2 ^ (prefixWord ++ tailWord_1247045).sum := by decide
  have hdescent : baseEnd_1247045 < baseStart_1247045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247104 : List Nat := [2, 1, 1, 2, 1, 2, 5, 7]
def baseStart_1247104 : Nat := 118140960795 + 1247104 * 2 ^ 59
def prefixEnd_1247104 : Nat := 4983230072969 + 3 ^ 40 * 1247104 * 2
def baseEnd_1247104 : Nat := 94868707873302804972545

theorem tailTrace_1247104 : CollatzResearch.WordTrace tailWord_1247104 prefixEnd_1247104 94868707873302804972545 := by
  unfold tailWord_1247104
  simp only [CollatzResearch.WordTrace]
  refine ⟨22742809836981335625718183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30323746449308447500957577 22742809836981335625718183)
  ·
    refine ⟨34114214755472003438577275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22742809836981335625718183 34114214755472003438577275)
    ·
      refine ⟨51171322133208005157865913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34114214755472003438577275 51171322133208005157865913)
      ·
        refine ⟨38378491599906003868399435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51171322133208005157865913 38378491599906003868399435)
        ·
          refine ⟨57567737399859005802599153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38378491599906003868399435 57567737399859005802599153)
          ·
            refine ⟨43175803049894254351949365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57567737399859005802599153 43175803049894254351949365)
            ·
              refine ⟨4047731535927586345495253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43175803049894254351949365 4047731535927586345495253)
              ·
                refine ⟨94868707873302804972545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4047731535927586345495253 94868707873302804972545)
                ·
                  rfl

theorem cell21_1247104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 7].length) (baseStart_1247104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247104 prefixEnd_1247104 := by exact prefixLift 1247104
  have htrace : WordTrace (prefixWord ++ tailWord_1247104) baseStart_1247104 baseEnd_1247104 := by
    simpa [prefixWord, tailWord_1247104, baseEnd_1247104] using wordTrace_append hprefix tailTrace_1247104
  have hstable : (prefixWord ++ tailWord_1247104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247104).length < 2 ^ (prefixWord ++ tailWord_1247104).sum := by decide
  have hdescent : baseEnd_1247104 < baseStart_1247104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247138 : List Nat := [3, 3, 1, 2, 3, 1, 2, 6]
def baseStart_1247138 : Nat := 118140960795 + 1247138 * 2 ^ 59
def prefixEnd_1247138 : Nat := 4983230072969 + 3 ^ 40 * 1247138 * 2
def baseEnd_1247138 : Nat := 94871294294377303783633

theorem tailTrace_1247138 : CollatzResearch.WordTrace tailWord_1247138 prefixEnd_1247138 94871294294377303783633 := by
  unfold tailWord_1247138
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371714938959873764543517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30324573170559663372116045 11371714938959873764543517)
  ·
    refine ⟨4264393102109952661703819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11371714938959873764543517 4264393102109952661703819)
    ·
      refine ⟨6396589653164928992555729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264393102109952661703819 6396589653164928992555729)
      ·
        refine ⟨4797442239873696744416797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6396589653164928992555729 4797442239873696744416797)
        ·
          refine ⟨1799040839952636279156299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4797442239873696744416797 1799040839952636279156299)
          ·
            refine ⟨2698561259928954418734449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799040839952636279156299 2698561259928954418734449)
            ·
              refine ⟨2023920944946715814050837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698561259928954418734449 2023920944946715814050837)
              ·
                refine ⟨94871294294377303783633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2023920944946715814050837 94871294294377303783633)
                ·
                  rfl

theorem cell21_1247138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_1247138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247138 prefixEnd_1247138 := by exact prefixLift 1247138
  have htrace : WordTrace (prefixWord ++ tailWord_1247138) baseStart_1247138 baseEnd_1247138 := by
    simpa [prefixWord, tailWord_1247138, baseEnd_1247138] using wordTrace_append hprefix tailTrace_1247138
  have hstable : (prefixWord ++ tailWord_1247138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247138).length < 2 ^ (prefixWord ++ tailWord_1247138).sum := by decide
  have hdescent : baseEnd_1247138 < baseStart_1247138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247180 : List Nat := [2, 2, 1, 4, 1, 11]
def baseStart_1247180 : Nat := 118140960795 + 1247180 * 2 ^ 59
def prefixEnd_1247180 : Nat := 4983230072969 + 3 ^ 40 * 1247180 * 2
def baseEnd_1247180 : Nat := 10541609920568487838919

theorem tailTrace_1247180 : CollatzResearch.WordTrace tailWord_1247180 prefixEnd_1247180 10541609920568487838919 := by
  unfold tailWord_1247180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22744195810843668115601497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30325594414458224154135329 22744195810843668115601497)
  ·
    refine ⟨17058146858132751086701123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22744195810843668115601497 17058146858132751086701123)
    ·
      refine ⟨25587220287199126630051685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17058146858132751086701123 25587220287199126630051685)
      ·
        refine ⟨4797603803849836243134691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25587220287199126630051685 4797603803849836243134691)
        ·
          refine ⟨7196405705774754364702037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4797603803849836243134691 7196405705774754364702037)
          ·
            refine ⟨10541609920568487838919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7196405705774754364702037 10541609920568487838919)
            ·
              rfl

theorem cell21_1247180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 11].length) (baseStart_1247180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247180 prefixEnd_1247180 := by exact prefixLift 1247180
  have htrace : WordTrace (prefixWord ++ tailWord_1247180) baseStart_1247180 baseEnd_1247180 := by
    simpa [prefixWord, tailWord_1247180, baseEnd_1247180] using wordTrace_append hprefix tailTrace_1247180
  have hstable : (prefixWord ++ tailWord_1247180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247180).length < 2 ^ (prefixWord ++ tailWord_1247180).sum := by decide
  have hdescent : baseEnd_1247180 < baseStart_1247180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247186 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 3]
def baseStart_1247186 : Nat := 118140960795 + 1247186 * 2 ^ 59
def prefixEnd_1247186 : Nat := 4983230072969 + 3 ^ 40 * 1247186 * 2
def baseEnd_1247186 : Nat := 284624837137094494550801

theorem tailTrace_1247186 : CollatzResearch.WordTrace tailWord_1247186 prefixEnd_1247186 284624837137094494550801 := by
  unfold tailWord_1247186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11372152614916399813980353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30325740306443732837280941 11372152614916399813980353)
  ·
    refine ⟨8529114461187299860485265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11372152614916399813980353 8529114461187299860485265)
    ·
      refine ⟨6396835845890474895363949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8529114461187299860485265 6396835845890474895363949)
      ·
        refine ⟨2398813442208928085761481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6396835845890474895363949 2398813442208928085761481)
        ·
          refine ⟨1799110081656696064321111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398813442208928085761481 1799110081656696064321111)
          ·
            refine ⟨2698665122485044096481667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799110081656696064321111 2698665122485044096481667)
            ·
              refine ⟨4047997683727566144722501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698665122485044096481667 4047997683727566144722501)
              ·
                refine ⟨758999565698918652135469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4047997683727566144722501 758999565698918652135469)
                ·
                  refine ⟨284624837137094494550801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758999565698918652135469 284624837137094494550801)
                  ·
                    rfl

theorem cell21_1247186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_1247186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247186 prefixEnd_1247186 := by exact prefixLift 1247186
  have htrace : WordTrace (prefixWord ++ tailWord_1247186) baseStart_1247186 baseEnd_1247186 := by
    simpa [prefixWord, tailWord_1247186, baseEnd_1247186] using wordTrace_append hprefix tailTrace_1247186
  have hstable : (prefixWord ++ tailWord_1247186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247186).length < 2 ^ (prefixWord ++ tailWord_1247186).sum := by decide
  have hdescent : baseEnd_1247186 < baseStart_1247186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247214 : List Nat := [4, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1247214 : Nat := 118140960795 + 1247214 * 2 ^ 59
def prefixEnd_1247214 : Nat := 4983230072969 + 3 ^ 40 * 1247214 * 2
def baseEnd_1247214 : Nat := 94877075706190889361359

theorem tailTrace_1247214 : CollatzResearch.WordTrace tailWord_1247214 prefixEnd_1247214 94877075706190889361359 := by
  unfold tailWord_1247214
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686203962945520004742587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30326421135709440025293797 5686203962945520004742587)
  ·
    refine ⟨8529305944418280007113881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5686203962945520004742587 8529305944418280007113881)
    ·
      refine ⟨6396979458313710005335411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8529305944418280007113881 6396979458313710005335411)
      ·
        refine ⟨9595469187470565008003117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6396979458313710005335411 9595469187470565008003117)
        ·
          refine ⟨3598300945301461878001169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9595469187470565008003117 3598300945301461878001169)
          ·
            refine ⟨2698725708976096408500877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598300945301461878001169 2698725708976096408500877)
            ·
              refine ⟨1012022140866036153187829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2698725708976096408500877 1012022140866036153187829)
              ·
                refine ⟨94877075706190889361359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1012022140866036153187829 94877075706190889361359)
                ·
                  rfl

theorem cell21_1247214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1247214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247214 prefixEnd_1247214 := by exact prefixLift 1247214
  have htrace : WordTrace (prefixWord ++ tailWord_1247214) baseStart_1247214 baseEnd_1247214 := by
    simpa [prefixWord, tailWord_1247214, baseEnd_1247214] using wordTrace_append hprefix tailTrace_1247214
  have hstable : (prefixWord ++ tailWord_1247214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247214).length < 2 ^ (prefixWord ++ tailWord_1247214).sum := by decide
  have hdescent : baseEnd_1247214 < baseStart_1247214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247256 : List Nat := [2, 1, 2, 3, 2, 1, 2, 8]
def baseStart_1247256 : Nat := 118140960795 + 1247256 * 2 ^ 59
def prefixEnd_1247256 : Nat := 4983230072969 + 3 ^ 40 * 1247256 * 2
def baseEnd_1247256 : Nat := 94880270696929976127997

theorem tailTrace_1247256 : CollatzResearch.WordTrace tailWord_1247256 prefixEnd_1247256 94880270696929976127997 := by
  unfold tailWord_1247256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22745581784706000605484811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30327442379608000807313081 22745581784706000605484811)
  ·
    refine ⟨34118372677059000908227217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22745581784706000605484811 34118372677059000908227217)
    ·
      refine ⟨25588779507794250681170413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34118372677059000908227217 25588779507794250681170413)
      ·
        refine ⟨9595792315422844005438905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25588779507794250681170413 9595792315422844005438905)
        ·
          refine ⟨7196844236567133004079179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9595792315422844005438905 7196844236567133004079179)
          ·
            refine ⟨10795266354850699506118769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7196844236567133004079179 10795266354850699506118769)
            ·
              refine ⟨8096449766138024629589077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10795266354850699506118769 8096449766138024629589077)
              ·
                refine ⟨94880270696929976127997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8096449766138024629589077 94880270696929976127997)
                ·
                  rfl

theorem cell21_1247256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_1247256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247256 prefixEnd_1247256 := by exact prefixLift 1247256
  have htrace : WordTrace (prefixWord ++ tailWord_1247256) baseStart_1247256 baseEnd_1247256 := by
    simpa [prefixWord, tailWord_1247256, baseEnd_1247256] using wordTrace_append hprefix tailTrace_1247256
  have hstable : (prefixWord ++ tailWord_1247256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247256).length < 2 ^ (prefixWord ++ tailWord_1247256).sum := by decide
  have hdescent : baseEnd_1247256 < baseStart_1247256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247332 : List Nat := [2, 3, 1, 1, 2, 1, 4, 7]
def baseStart_1247332 : Nat := 118140960795 + 1247332 * 2 ^ 59
def prefixEnd_1247332 : Nat := 4983230072969 + 3 ^ 40 * 1247332 * 2
def baseEnd_1247332 : Nat := 94886052108743561705723

theorem tailTrace_1247332 : CollatzResearch.WordTrace tailWord_1247332 prefixEnd_1247332 94886052108743561705723 := by
  unfold tailWord_1247332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22746967758568333095368125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30329290344757777460490833 22746967758568333095368125)
  ·
    refine ⟨8530112909463124910763047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22746967758568333095368125 8530112909463124910763047)
    ·
      refine ⟨12795169364194687366144571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8530112909463124910763047 12795169364194687366144571)
      ·
        refine ⟨19192754046292031049216857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795169364194687366144571 19192754046292031049216857)
        ·
          refine ⟨14394565534719023286912643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19192754046292031049216857 14394565534719023286912643)
          ·
            refine ⟨21591848302078534930368965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14394565534719023286912643 21591848302078534930368965)
            ·
              refine ⟨4048471556639725299444181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21591848302078534930368965 4048471556639725299444181)
              ·
                refine ⟨94886052108743561705723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4048471556639725299444181 94886052108743561705723)
                ·
                  rfl

theorem cell21_1247332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 7].length) (baseStart_1247332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247332 prefixEnd_1247332 := by exact prefixLift 1247332
  have htrace : WordTrace (prefixWord ++ tailWord_1247332) baseStart_1247332 baseEnd_1247332 := by
    simpa [prefixWord, tailWord_1247332, baseEnd_1247332] using wordTrace_append hprefix tailTrace_1247332
  have hstable : (prefixWord ++ tailWord_1247332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247332).length < 2 ^ (prefixWord ++ tailWord_1247332).sum := by decide
  have hdescent : baseEnd_1247332 < baseStart_1247332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247428 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 4]
def baseStart_1247428 : Nat := 118140960795 + 1247428 * 2 ^ 59
def prefixEnd_1247428 : Nat := 4983230072969 + 3 ^ 40 * 1247428 * 2
def baseEnd_1247428 : Nat := 284680064834155851516973

theorem tailTrace_1247428 : CollatzResearch.WordTrace tailWord_1247428 prefixEnd_1247428 284680064834155851516973 := by
  unfold tailWord_1247428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22748718462394437293115469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30331624616525916390820625 22748718462394437293115469)
  ·
    refine ⟨8530769423397913984918301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22748718462394437293115469 8530769423397913984918301)
    ·
      refine ⟨3199038533774217744344363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8530769423397913984918301 3199038533774217744344363)
      ·
        refine ⟨4798557800661326616516545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199038533774217744344363 4798557800661326616516545)
        ·
          refine ⟨3598918350495994962387409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4798557800661326616516545 3598918350495994962387409)
          ·
            refine ⟨2699188762871996221790557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3598918350495994962387409 2699188762871996221790557)
            ·
              refine ⟨1012195786076998583171459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2699188762871996221790557 1012195786076998583171459)
              ·
                refine ⟨1518293679115497874757189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012195786076998583171459 1518293679115497874757189)
                ·
                  refine ⟨284680064834155851516973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518293679115497874757189 284680064834155851516973)
                  ·
                    rfl

theorem cell21_1247428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_1247428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247428 prefixEnd_1247428 := by exact prefixLift 1247428
  have htrace : WordTrace (prefixWord ++ tailWord_1247428) baseStart_1247428 baseEnd_1247428 := by
    simpa [prefixWord, tailWord_1247428, baseEnd_1247428] using wordTrace_append hprefix tailTrace_1247428
  have hstable : (prefixWord ++ tailWord_1247428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247428).length < 2 ^ (prefixWord ++ tailWord_1247428).sum := by decide
  have hdescent : baseEnd_1247428 < baseStart_1247428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247442 : List Nat := [3, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1247442 : Nat := 118140960795 + 1247442 * 2 ^ 59
def prefixEnd_1247442 : Nat := 4983230072969 + 3 ^ 40 * 1247442 * 2
def baseEnd_1247442 : Nat := 94894419941631646094537

theorem tailTrace_1247442 : CollatzResearch.WordTrace tailWord_1247442 prefixEnd_1247442 94894419941631646094537 := by
  unfold tailWord_1247442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11374486886684538744310145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30331965031158769984827053 11374486886684538744310145)
  ·
    refine ⟨8530865165013404058232609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11374486886684538744310145 8530865165013404058232609)
    ·
      refine ⟨6398148873760053043674457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8530865165013404058232609 6398148873760053043674457)
      ·
        refine ⟨4798611655320039782755843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6398148873760053043674457 4798611655320039782755843)
        ·
          refine ⟨7197917482980059674133765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798611655320039782755843 7197917482980059674133765)
          ·
            refine ⟨1349609528058761188900081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7197917482980059674133765 1349609528058761188900081)
            ·
              refine ⟨1012207146044070891675061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349609528058761188900081 1012207146044070891675061)
              ·
                refine ⟨94894419941631646094537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1012207146044070891675061 94894419941631646094537)
                ·
                  rfl

theorem cell21_1247442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1247442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247442 prefixEnd_1247442 := by exact prefixLift 1247442
  have htrace : WordTrace (prefixWord ++ tailWord_1247442) baseStart_1247442 baseEnd_1247442 := by
    simpa [prefixWord, tailWord_1247442, baseEnd_1247442] using wordTrace_append hprefix tailTrace_1247442
  have hstable : (prefixWord ++ tailWord_1247442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247442).length < 2 ^ (prefixWord ++ tailWord_1247442).sum := by decide
  have hdescent : baseEnd_1247442 < baseStart_1247442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247470 : List Nat := [4, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_1247470 : Nat := 118140960795 + 1247470 * 2 ^ 59
def prefixEnd_1247470 : Nat := 4983230072969 + 3 ^ 40 * 1247470 * 2
def baseEnd_1247470 : Nat := 284689649806373111816887

theorem tailTrace_1247470 : CollatzResearch.WordTrace tailWord_1247470 prefixEnd_1247470 284689649806373111816887 := by
  unfold tailWord_1247470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5687371098829589469907483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30332645860424477172839909 5687371098829589469907483)
  ·
    refine ⟨8531056648244384204861225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5687371098829589469907483 8531056648244384204861225)
    ·
      refine ⟨6398292486183288153645919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8531056648244384204861225 6398292486183288153645919)
      ·
        refine ⟨9597438729274932230468879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398292486183288153645919 9597438729274932230468879)
        ·
          refine ⟨14396158093912398345703319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9597438729274932230468879 14396158093912398345703319)
          ·
            refine ⟨21594237140868597518554979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14396158093912398345703319 21594237140868597518554979)
            ·
              refine ⟨32391355711302896277832469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21594237140868597518554979 32391355711302896277832469)
              ·
                refine ⟨1518344798967323263023397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32391355711302896277832469 1518344798967323263023397)
                ·
                  refine ⟨284689649806373111816887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518344798967323263023397 284689649806373111816887)
                  ·
                    rfl

theorem cell21_1247470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_1247470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247470 prefixEnd_1247470 := by exact prefixLift 1247470
  have htrace : WordTrace (prefixWord ++ tailWord_1247470) baseStart_1247470 baseEnd_1247470 := by
    simpa [prefixWord, tailWord_1247470, baseEnd_1247470] using wordTrace_append hprefix tailTrace_1247470
  have hstable : (prefixWord ++ tailWord_1247470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247470).length < 2 ^ (prefixWord ++ tailWord_1247470).sum := by decide
  have hdescent : baseEnd_1247470 < baseStart_1247470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247484 : List Nat := [2, 2, 2, 1, 4, 1, 1, 8]
def baseStart_1247484 : Nat := 118140960795 + 1247484 * 2 ^ 59
def prefixEnd_1247484 : Nat := 4983230072969 + 3 ^ 40 * 1247484 * 2
def baseEnd_1247484 : Nat := 94897614932370732861175

theorem tailTrace_1247484 : CollatzResearch.WordTrace tailWord_1247484 prefixEnd_1247484 94897614932370732861175 := by
  unfold tailWord_1247484
  simp only [CollatzResearch.WordTrace]
  refine ⟨22749739706292998075134753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30332986275057330766846337 22749739706292998075134753)
  ·
    refine ⟨17062304779719748556351065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22749739706292998075134753 17062304779719748556351065)
    ·
      refine ⟨12796728584789811417263299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17062304779719748556351065 12796728584789811417263299)
      ·
        refine ⟨19195092877184717125894949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12796728584789811417263299 19195092877184717125894949)
        ·
          refine ⟨3599079914472134461105303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19195092877184717125894949 3599079914472134461105303)
          ·
            refine ⟨5398619871708201691657955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599079914472134461105303 5398619871708201691657955)
            ·
              refine ⟨8097929807562302537486933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5398619871708201691657955 8097929807562302537486933)
              ·
                refine ⟨94897614932370732861175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8097929807562302537486933 94897614932370732861175)
                ·
                  rfl

theorem cell21_1247484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_1247484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247484 prefixEnd_1247484 := by exact prefixLift 1247484
  have htrace : WordTrace (prefixWord ++ tailWord_1247484) baseStart_1247484 baseEnd_1247484 := by
    simpa [prefixWord, tailWord_1247484, baseEnd_1247484] using wordTrace_append hprefix tailTrace_1247484
  have hstable : (prefixWord ++ tailWord_1247484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247484).length < 2 ^ (prefixWord ++ tailWord_1247484).sum := by decide
  have hdescent : baseEnd_1247484 < baseStart_1247484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247546 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 4]
def baseStart_1247546 : Nat := 118140960795 + 1247546 * 2 ^ 59
def prefixEnd_1247546 : Nat := 4983230072969 + 3 ^ 40 * 1247546 * 2
def baseEnd_1247546 : Nat := 284706994041813868550065

theorem tailTrace_1247546 : CollatzResearch.WordTrace tailWord_1247546 prefixEnd_1247546 284706994041813868550065 := by
  unfold tailWord_1247546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11375435184590345184756623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30334493825574253826017661 11375435184590345184756623)
  ·
    refine ⟨17063152776885517777134935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11375435184590345184756623 17063152776885517777134935)
    ·
      refine ⟨25594729165328276665702403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17063152776885517777134935 25594729165328276665702403)
      ·
        refine ⟨38392093747992414998553605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25594729165328276665702403 38392093747992414998553605)
        ·
          refine ⟨7198517577748577812228801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38392093747992414998553605 7198517577748577812228801)
          ·
            refine ⟨5398888183311433359171601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7198517577748577812228801 5398888183311433359171601)
            ·
              refine ⟨4049166137483575019378701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5398888183311433359171601 4049166137483575019378701)
              ·
                refine ⟨1518437301556340632267013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4049166137483575019378701 1518437301556340632267013)
                ·
                  refine ⟨284706994041813868550065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518437301556340632267013 284706994041813868550065)
                  ·
                    rfl

theorem cell21_1247546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 4].length) (baseStart_1247546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247546 prefixEnd_1247546 := by exact prefixLift 1247546
  have htrace : WordTrace (prefixWord ++ tailWord_1247546) baseStart_1247546 baseEnd_1247546 := by
    simpa [prefixWord, tailWord_1247546, baseEnd_1247546] using wordTrace_append hprefix tailTrace_1247546
  have hstable : (prefixWord ++ tailWord_1247546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247546).length < 2 ^ (prefixWord ++ tailWord_1247546).sum := by decide
  have hdescent : baseEnd_1247546 < baseStart_1247546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247591 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 5]
def baseStart_1247591 : Nat := 118140960795 + 1247591 * 2 ^ 59
def prefixEnd_1247591 : Nat := 4983230072969 + 3 ^ 40 * 1247591 * 2
def baseEnd_1247591 : Nat := 284717263654903790299973

theorem tailTrace_1247591 : CollatzResearch.WordTrace tailWord_1247591 prefixEnd_1247591 284717263654903790299973 := by
  unfold tailWord_1247591
  simp only [CollatzResearch.WordTrace]
  refine ⟨45503382023198353424414627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30335588015465568949609751 45503382023198353424414627)
  ·
    refine ⟨68255073034797530136621941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45503382023198353424414627 68255073034797530136621941)
    ·
      refine ⟨6398913097012268450308307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68255073034797530136621941 6398913097012268450308307)
      ·
        refine ⟨9598369645518402675462461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6398913097012268450308307 9598369645518402675462461)
        ·
          refine ⟨3599388617069401003298423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9598369645518402675462461 3599388617069401003298423)
          ·
            refine ⟨5399082925604101504947635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599388617069401003298423 5399082925604101504947635)
            ·
              refine ⟨8098624388406152257421453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399082925604101504947635 8098624388406152257421453)
              ·
                refine ⟨3036984145652307096533045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8098624388406152257421453 3036984145652307096533045)
                ·
                  refine ⟨284717263654903790299973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3036984145652307096533045 284717263654903790299973)
                  ·
                    rfl

theorem cell21_1247591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 5].length) (baseStart_1247591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247591 prefixEnd_1247591 := by exact prefixLift 1247591
  have htrace : WordTrace (prefixWord ++ tailWord_1247591) baseStart_1247591 baseEnd_1247591 := by
    simpa [prefixWord, tailWord_1247591, baseEnd_1247591] using wordTrace_append hprefix tailTrace_1247591
  have hstable : (prefixWord ++ tailWord_1247591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247591).length < 2 ^ (prefixWord ++ tailWord_1247591).sum := by decide
  have hdescent : baseEnd_1247591 < baseStart_1247591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247625 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 3]
def baseStart_1247625 : Nat := 118140960795 + 1247625 * 2 ^ 59
def prefixEnd_1247625 : Nat := 4983230072969 + 3 ^ 40 * 1247625 * 2
def baseEnd_1247625 : Nat := 284725022918127286733237

theorem tailTrace_1247625 : CollatzResearch.WordTrace tailWord_1247625 prefixEnd_1247625 284725022918127286733237 := by
  unfold tailWord_1247625
  simp only [CollatzResearch.WordTrace]
  refine ⟨45504622105075177231152329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30336414736716784820768219 45504622105075177231152329)
  ·
    refine ⟨34128466578806382923364247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45504622105075177231152329 34128466578806382923364247)
    ·
      refine ⟨51192699868209574385046371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34128466578806382923364247 51192699868209574385046371)
      ·
        refine ⟨76789049802314361577569557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51192699868209574385046371 76789049802314361577569557)
        ·
          refine ⟨3599486709483485698948573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76789049802314361577569557 3599486709483485698948573)
          ·
            refine ⟨1349807516056307137105715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3599486709483485698948573 1349807516056307137105715)
            ·
              refine ⟨2024711274084460705658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349807516056307137105715 2024711274084460705658573)
              ·
                refine ⟨759266727781672764621965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2024711274084460705658573 759266727781672764621965)
                ·
                  refine ⟨284725022918127286733237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759266727781672764621965 284725022918127286733237)
                  ·
                    rfl

theorem cell21_1247625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 3].length) (baseStart_1247625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247625 prefixEnd_1247625 := by exact prefixLift 1247625
  have htrace : WordTrace (prefixWord ++ tailWord_1247625) baseStart_1247625 baseEnd_1247625 := by
    simpa [prefixWord, tailWord_1247625, baseEnd_1247625] using wordTrace_append hprefix tailTrace_1247625
  have hstable : (prefixWord ++ tailWord_1247625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247625).length < 2 ^ (prefixWord ++ tailWord_1247625).sum := by decide
  have hdescent : baseEnd_1247625 < baseStart_1247625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247656 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 4]
def baseStart_1247656 : Nat := 118140960795 + 1247656 * 2 ^ 59
def prefixEnd_1247656 : Nat := 4983230072969 + 3 ^ 40 * 1247656 * 2
def baseEnd_1247656 : Nat := 284732097540478121716507

theorem tailTrace_1247656 : CollatzResearch.WordTrace tailWord_1247656 prefixEnd_1247656 284732097540478121716507 := by
  unfold tailWord_1247656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752876383981434762765411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30337168511975246350353881 22752876383981434762765411)
  ·
    refine ⟨34129314575972152144148117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22752876383981434762765411 34129314575972152144148117)
    ·
      refine ⟨1599811620748694631756943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34129314575972152144148117 1599811620748694631756943)
      ·
        refine ⟨2399717431123041947635415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599811620748694631756943 2399717431123041947635415)
        ·
          refine ⟨3599576146684562921453123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2399717431123041947635415 3599576146684562921453123)
          ·
            refine ⟨5399364220026844382179685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599576146684562921453123 5399364220026844382179685)
            ·
              refine ⟨1012380791255033321658691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5399364220026844382179685 1012380791255033321658691)
              ·
                refine ⟨1518571186882549982488037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012380791255033321658691 1518571186882549982488037)
                ·
                  refine ⟨284732097540478121716507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518571186882549982488037 284732097540478121716507)
                  ·
                    rfl

theorem cell21_1247656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 4].length) (baseStart_1247656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247656 prefixEnd_1247656 := by exact prefixLift 1247656
  have htrace : WordTrace (prefixWord ++ tailWord_1247656) baseStart_1247656 baseEnd_1247656 := by
    simpa [prefixWord, tailWord_1247656, baseEnd_1247656] using wordTrace_append hprefix tailTrace_1247656
  have hstable : (prefixWord ++ tailWord_1247656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247656).length < 2 ^ (prefixWord ++ tailWord_1247656).sum := by decide
  have hdescent : baseEnd_1247656 < baseStart_1247656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247701 : List Nat := [1, 3, 2, 3, 1, 2, 4, 2, 3]
def baseStart_1247701 : Nat := 118140960795 + 1247701 * 2 ^ 59
def prefixEnd_1247701 : Nat := 4983230072969 + 3 ^ 40 * 1247701 * 2
def baseEnd_1247701 : Nat := 284742367153568043466415

theorem tailTrace_1247701 : CollatzResearch.WordTrace tailWord_1247701 prefixEnd_1247701 284742367153568043466415 := by
  unfold tailWord_1247701
  simp only [CollatzResearch.WordTrace]
  refine ⟨45507394052799842210918957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30338262701866561473945971 45507394052799842210918957)
  ·
    refine ⟨17065272769799940829094609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45507394052799842210918957 17065272769799940829094609)
    ·
      refine ⟨12798954577349955621820957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17065272769799940829094609 12798954577349955621820957)
      ·
        refine ⟨4799607966506233358182859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12798954577349955621820957 4799607966506233358182859)
        ·
          refine ⟨7199411949759350037274289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799607966506233358182859 7199411949759350037274289)
          ·
            refine ⟨5399558962319512527955717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7199411949759350037274289 5399558962319512527955717)
            ·
              refine ⟨1012417305434908598991697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5399558962319512527955717 1012417305434908598991697)
              ·
                refine ⟨759312979076181449243773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012417305434908598991697 759312979076181449243773)
                ·
                  refine ⟨284742367153568043466415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759312979076181449243773 284742367153568043466415)
                  ·
                    rfl

theorem cell21_1247701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_1247701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247701 prefixEnd_1247701 := by exact prefixLift 1247701
  have htrace : WordTrace (prefixWord ++ tailWord_1247701) baseStart_1247701 baseEnd_1247701 := by
    simpa [prefixWord, tailWord_1247701, baseEnd_1247701] using wordTrace_append hprefix tailTrace_1247701
  have hstable : (prefixWord ++ tailWord_1247701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247701).length < 2 ^ (prefixWord ++ tailWord_1247701).sum := by decide
  have hdescent : baseEnd_1247701 < baseStart_1247701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247819 : List Nat := [1, 1, 1, 1, 3, 1, 4, 6, 3]
def baseStart_1247819 : Nat := 118140960795 + 1247819 * 2 ^ 59
def prefixEnd_1247819 : Nat := 4983230072969 + 3 ^ 40 * 1247819 * 2
def baseEnd_1247819 : Nat := 284769296361226060499507

theorem tailTrace_1247819 : CollatzResearch.WordTrace tailWord_1247819 prefixEnd_1247819 284769296361226060499507 := by
  unfold tailWord_1247819
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511697866372348363714511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30341131910914898909143007 45511697866372348363714511)
  ·
    refine ⟨68267546799558522545571767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45511697866372348363714511 68267546799558522545571767)
    ·
      refine ⟨102401320199337783818357651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68267546799558522545571767 102401320199337783818357651)
      ·
        refine ⟨153601980299006675727536477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102401320199337783818357651 153601980299006675727536477)
        ·
          refine ⟨57600742612127503397826179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153601980299006675727536477 57600742612127503397826179)
          ·
            refine ⟨86401113918191255096739269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57600742612127503397826179 86401113918191255096739269)
            ·
              refine ⟨16200208859660860330638613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86401113918191255096739269 16200208859660860330638613)
              ·
                refine ⟨759384790296602827998685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16200208859660860330638613 759384790296602827998685)
                ·
                  refine ⟨284769296361226060499507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759384790296602827998685 284769296361226060499507)
                  ·
                    rfl

theorem cell21_1247819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 6, 3].length) (baseStart_1247819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247819 prefixEnd_1247819 := by exact prefixLift 1247819
  have htrace : WordTrace (prefixWord ++ tailWord_1247819) baseStart_1247819 baseEnd_1247819 := by
    simpa [prefixWord, tailWord_1247819, baseEnd_1247819] using wordTrace_append hprefix tailTrace_1247819
  have hstable : (prefixWord ++ tailWord_1247819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247819).length < 2 ^ (prefixWord ++ tailWord_1247819).sum := by decide
  have hdescent : baseEnd_1247819 < baseStart_1247819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247898 : List Nat := [3, 1, 1, 6, 1, 1, 3, 5]
def baseStart_1247898 : Nat := 118140960795 + 1247898 * 2 ^ 59
def prefixEnd_1247898 : Nat := 4983230072969 + 3 ^ 40 * 1247898 * 2
def baseEnd_1247898 : Nat := 94929108412513159560893

theorem tailTrace_1247898 : CollatzResearch.WordTrace tailWord_1247898 prefixEnd_1247898 94929108412513159560893 := by
  unfold tailWord_1247898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11378644808271536213960087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30343052822057429903893565 11378644808271536213960087)
  ·
    refine ⟨17067967212407304320940131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11378644808271536213960087 17067967212407304320940131)
    ·
      refine ⟨25601950818610956481410197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17067967212407304320940131 25601950818610956481410197)
      ·
        refine ⟨1200091444622388585066103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25601950818610956481410197 1200091444622388585066103)
        ·
          refine ⟨1800137166933582877599155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200091444622388585066103 1800137166933582877599155)
          ·
            refine ⟨2700205750400374316398733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800137166933582877599155 2700205750400374316398733)
            ·
              refine ⟨1012577156400140368649525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2700205750400374316398733 1012577156400140368649525)
              ·
                refine ⟨94929108412513159560893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1012577156400140368649525 94929108412513159560893)
                ·
                  rfl

theorem cell21_1247898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_1247898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247898 prefixEnd_1247898 := by exact prefixLift 1247898
  have htrace : WordTrace (prefixWord ++ tailWord_1247898) baseStart_1247898 baseEnd_1247898 := by
    simpa [prefixWord, tailWord_1247898, baseEnd_1247898] using wordTrace_append hprefix tailTrace_1247898
  have hstable : (prefixWord ++ tailWord_1247898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247898).length < 2 ^ (prefixWord ++ tailWord_1247898).sum := by decide
  have hdescent : baseEnd_1247898 < baseStart_1247898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247923 : List Nat := [1, 1, 1, 2, 3, 5, 8]
def baseStart_1247923 : Nat := 118140960795 + 1247923 * 2 ^ 59
def prefixEnd_1247923 : Nat := 4983230072969 + 3 ^ 40 * 1247923 * 2
def baseEnd_1247923 : Nat := 31643670064238332307329

theorem tailTrace_1247923 : CollatzResearch.WordTrace tailWord_1247923 prefixEnd_1247923 31643670064238332307329 := by
  unfold tailWord_1247923
  simp only [CollatzResearch.WordTrace]
  refine ⟨45515491057995574125500423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30343660705330382750333615 45515491057995574125500423)
  ·
    refine ⟨68273236586993361188250635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45515491057995574125500423 68273236586993361188250635)
    ·
      refine ⟨102409854880490041782375953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68273236586993361188250635 102409854880490041782375953)
      ·
        refine ⟨76807391160367531336781965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102409854880490041782375953 76807391160367531336781965)
        ·
          refine ⟨28802771685137824251293237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76807391160367531336781965 28802771685137824251293237)
          ·
            refine ⟨2700259845481671023558741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28802771685137824251293237 2700259845481671023558741)
            ·
              refine ⟨31643670064238332307329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2700259845481671023558741 31643670064238332307329)
              ·
                rfl

theorem cell21_1247923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 8].length) (baseStart_1247923 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247923 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247923 prefixEnd_1247923 := by exact prefixLift 1247923
  have htrace : WordTrace (prefixWord ++ tailWord_1247923) baseStart_1247923 baseEnd_1247923 := by
    simpa [prefixWord, tailWord_1247923, baseEnd_1247923] using wordTrace_append hprefix tailTrace_1247923
  have hstable : (prefixWord ++ tailWord_1247923).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247923).length < 2 ^ (prefixWord ++ tailWord_1247923).sum := by decide
  have hdescent : baseEnd_1247923 < baseStart_1247923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247957 : List Nat := [1, 3, 2, 5, 1, 1, 1, 7]
def baseStart_1247957 : Nat := 118140960795 + 1247957 * 2 ^ 59
def prefixEnd_1247957 : Nat := 4983230072969 + 3 ^ 40 * 1247957 * 2
def baseEnd_1247957 : Nat := 94933596613789495733075

theorem tailTrace_1247957 : CollatzResearch.WordTrace tailWord_1247957 prefixEnd_1247957 94933596613789495733075 := by
  unfold tailWord_1247957
  simp only [CollatzResearch.WordTrace]
  refine ⟨45516731139872397932238125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30344487426581598621492083 45516731139872397932238125)
  ·
    refine ⟨17068774177452149224589297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45516731139872397932238125 17068774177452149224589297)
    ·
      refine ⟨12801580633089111918441973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17068774177452149224589297 12801580633089111918441973)
      ·
        refine ⟨1200148184352104242353935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12801580633089111918441973 1200148184352104242353935)
        ·
          refine ⟨1800222276528156363530903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200148184352104242353935 1800222276528156363530903)
          ·
            refine ⟨2700333414792234545296355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800222276528156363530903 2700333414792234545296355)
            ·
              refine ⟨4050500122188351817944533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700333414792234545296355 4050500122188351817944533)
              ·
                refine ⟨94933596613789495733075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4050500122188351817944533 94933596613789495733075)
                ·
                  rfl

theorem cell21_1247957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 7].length) (baseStart_1247957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247957 prefixEnd_1247957 := by exact prefixLift 1247957
  have htrace : WordTrace (prefixWord ++ tailWord_1247957) baseStart_1247957 baseEnd_1247957 := by
    simpa [prefixWord, tailWord_1247957, baseEnd_1247957] using wordTrace_append hprefix tailTrace_1247957
  have hstable : (prefixWord ++ tailWord_1247957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247957).length < 2 ^ (prefixWord ++ tailWord_1247957).sum := by decide
  have hdescent : baseEnd_1247957 < baseStart_1247957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247985 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1247985 : Nat := 118140960795 + 1247985 * 2 ^ 59
def prefixEnd_1247985 : Nat := 4983230072969 + 3 ^ 40 * 1247985 * 2
def baseEnd_1247985 : Nat := 284807179822846660732501

theorem tailTrace_1247985 : CollatzResearch.WordTrace tailWord_1247985 prefixEnd_1247985 284807179822846660732501 := by
  unfold tailWord_1247985
  simp only [CollatzResearch.WordTrace]
  refine ⟨45517752383770958714257409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30345168255847305809504939 45517752383770958714257409)
  ·
    refine ⟨34138314287828219035693057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45517752383770958714257409 34138314287828219035693057)
    ·
      refine ⟨25603735715871164276769793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34138314287828219035693057 25603735715871164276769793)
      ·
        refine ⟨19202801786903373207577345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25603735715871164276769793 19202801786903373207577345)
        ·
          refine ⟨14402101340177529905683009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19202801786903373207577345 14402101340177529905683009)
          ·
            refine ⟨10801576005133147429262257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14402101340177529905683009 10801576005133147429262257)
            ·
              refine ⟨8101182003849860571946693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10801576005133147429262257 8101182003849860571946693)
              ·
                refine ⟨1518971625721848857240005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8101182003849860571946693 1518971625721848857240005)
                ·
                  refine ⟨284807179822846660732501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1518971625721848857240005 284807179822846660732501)
                  ·
                    rfl

theorem cell21_1247985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1247985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1247985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1247985 prefixEnd_1247985 := by exact prefixLift 1247985
  have htrace : WordTrace (prefixWord ++ tailWord_1247985) baseStart_1247985 baseEnd_1247985 := by
    simpa [prefixWord, tailWord_1247985, baseEnd_1247985] using wordTrace_append hprefix tailTrace_1247985
  have hstable : (prefixWord ++ tailWord_1247985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247985).length < 2 ^ (prefixWord ++ tailWord_1247985).sum := by decide
  have hdescent : baseEnd_1247985 < baseStart_1247985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248092 : List Nat := [2, 2, 4, 2, 1, 2, 8]
def baseStart_1248092 : Nat := 118140960795 + 1248092 * 2 ^ 59
def prefixEnd_1248092 : Nat := 4983230072969 + 3 ^ 40 * 1248092 * 2
def baseEnd_1248092 : Nat := 31647955408959805827661

theorem tailTrace_1248092 : CollatzResearch.WordTrace tailWord_1248092 prefixEnd_1248092 31647955408959805827661 := by
  unfold tailWord_1248092
  simp only [CollatzResearch.WordTrace]
  refine ⟨22760827497191657994201265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30347769996255543992268353 22760827497191657994201265)
  ·
    refine ⟨17070620622893743495650949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22760827497191657994201265 17070620622893743495650949)
    ·
      refine ⟨3200741366792576905434553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17070620622893743495650949 3200741366792576905434553)
      ·
        refine ⟨2400556025094432679075915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3200741366792576905434553 2400556025094432679075915)
        ·
          refine ⟨3600834037641649018613873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400556025094432679075915 3600834037641649018613873)
          ·
            refine ⟨2700625528231236763960405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600834037641649018613873 2700625528231236763960405)
            ·
              refine ⟨31647955408959805827661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2700625528231236763960405 31647955408959805827661)
              ·
                rfl

theorem cell21_1248092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 8].length) (baseStart_1248092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248092 prefixEnd_1248092 := by exact prefixLift 1248092
  have htrace : WordTrace (prefixWord ++ tailWord_1248092) baseStart_1248092 baseEnd_1248092 := by
    simpa [prefixWord, tailWord_1248092, baseEnd_1248092] using wordTrace_append hprefix tailTrace_1248092
  have hstable : (prefixWord ++ tailWord_1248092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248092).length < 2 ^ (prefixWord ++ tailWord_1248092).sum := by decide
  have hdescent : baseEnd_1248092 < baseStart_1248092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248205 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 4]
def baseStart_1248205 : Nat := 118140960795 + 1248205 * 2 ^ 59
def prefixEnd_1248205 : Nat := 4983230072969 + 3 ^ 40 * 1248205 * 2
def baseEnd_1248205 : Nat := 284857386820175167065385

theorem tailTrace_1248205 : CollatzResearch.WordTrace tailWord_1248205 prefixEnd_1248205 284857386820175167065385 := by
  unfold tailWord_1248205
  simp only [CollatzResearch.WordTrace]
  refine ⟨45525776442973936287266069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30350517628649290858177379 45525776442973936287266069)
  ·
    refine ⟨2134020770764403263465597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45525776442973936287266069 2134020770764403263465597)
    ·
      refine ⟨800257789036651223799599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2134020770764403263465597 800257789036651223799599)
      ·
        refine ⟨1200386683554976835699399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800257789036651223799599 1200386683554976835699399)
        ·
          refine ⟨1800580025332465253549099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200386683554976835699399 1800580025332465253549099)
          ·
            refine ⟨2700870037998697880323649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800580025332465253549099 2700870037998697880323649)
            ·
              refine ⟨2025652528499023410242737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700870037998697880323649 2025652528499023410242737)
              ·
                refine ⟨1519239396374267557682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025652528499023410242737 1519239396374267557682053)
                ·
                  refine ⟨284857386820175167065385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519239396374267557682053 284857386820175167065385)
                  ·
                    rfl

theorem cell21_1248205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_1248205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248205 prefixEnd_1248205 := by exact prefixLift 1248205
  have htrace : WordTrace (prefixWord ++ tailWord_1248205) baseStart_1248205 baseEnd_1248205 := by
    simpa [prefixWord, tailWord_1248205, baseEnd_1248205] using wordTrace_append hprefix tailTrace_1248205
  have hstable : (prefixWord ++ tailWord_1248205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248205).length < 2 ^ (prefixWord ++ tailWord_1248205).sum := by decide
  have hdescent : baseEnd_1248205 < baseStart_1248205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248216 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 3]
def baseStart_1248216 : Nat := 118140960795 + 1248216 * 2 ^ 59
def prefixEnd_1248216 : Nat := 4983230072969 + 3 ^ 40 * 1248216 * 2
def baseEnd_1248216 : Nat := 284859897170041592382029

theorem tailTrace_1248216 : CollatzResearch.WordTrace tailWord_1248216 prefixEnd_1248216 284859897170041592382029 := by
  unfold tailWord_1248216
  simp only [CollatzResearch.WordTrace]
  refine ⟨22763088822967042582958251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30350785097289390110611001 22763088822967042582958251)
  ·
    refine ⟨34144633234450563874437377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22763088822967042582958251 34144633234450563874437377)
    ·
      refine ⟨25608474925837922905828033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34144633234450563874437377 25608474925837922905828033)
      ·
        refine ⟨19206356194378442179371025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25608474925837922905828033 19206356194378442179371025)
        ·
          refine ⟨14404767145783831634528269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19206356194378442179371025 14404767145783831634528269)
          ·
            refine ⟨5401787679668936862948101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14404767145783831634528269 5401787679668936862948101)
            ·
              refine ⟨1012835189937925661802769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5401787679668936862948101 1012835189937925661802769)
              ·
                refine ⟨759626392453444246352077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012835189937925661802769 759626392453444246352077)
                ·
                  refine ⟨284859897170041592382029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759626392453444246352077 284859897170041592382029)
                  ·
                    rfl

theorem cell21_1248216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 3].length) (baseStart_1248216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248216 prefixEnd_1248216 := by exact prefixLift 1248216
  have htrace : WordTrace (prefixWord ++ tailWord_1248216) baseStart_1248216 baseEnd_1248216 := by
    simpa [prefixWord, tailWord_1248216, baseEnd_1248216] using wordTrace_append hprefix tailTrace_1248216
  have hstable : (prefixWord ++ tailWord_1248216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248216).length < 2 ^ (prefixWord ++ tailWord_1248216).sum := by decide
  have hdescent : baseEnd_1248216 < baseStart_1248216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248326 : List Nat := [6, 1, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1248326 : Nat := 118140960795 + 1248326 * 2 ^ 59
def prefixEnd_1248326 : Nat := 4983230072969 + 3 ^ 40 * 1248326 * 2
def baseEnd_1248326 : Nat := 284885000668705845548471

theorem tailTrace_1248326 : CollatzResearch.WordTrace tailWord_1248326 prefixEnd_1248326 284885000668705845548471 := by
  unfold tailWord_1248326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422818427360486686013151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30353459783690382634947221 1422818427360486686013151)
  ·
    refine ⟨2134227641040730029019727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1422818427360486686013151 2134227641040730029019727)
    ·
      refine ⟨3201341461561095043529591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134227641040730029019727 3201341461561095043529591)
      ·
        refine ⟨4802012192341642565294387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201341461561095043529591 4802012192341642565294387)
        ·
          refine ⟨7203018288512463847941581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802012192341642565294387 7203018288512463847941581)
          ·
            refine ⟨2701131858192173942978093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7203018288512463847941581 2701131858192173942978093)
            ·
              refine ⟨1012924446822065228616785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2701131858192173942978093 1012924446822065228616785)
              ·
                refine ⟨759693335116548921462589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012924446822065228616785 759693335116548921462589)
                ·
                  refine ⟨284885000668705845548471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759693335116548921462589 284885000668705845548471)
                  ·
                    rfl

theorem cell21_1248326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1248326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248326 prefixEnd_1248326 := by exact prefixLift 1248326
  have htrace : WordTrace (prefixWord ++ tailWord_1248326) baseStart_1248326 baseEnd_1248326 := by
    simpa [prefixWord, tailWord_1248326, baseEnd_1248326] using wordTrace_append hprefix tailTrace_1248326
  have hstable : (prefixWord ++ tailWord_1248326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248326).length < 2 ^ (prefixWord ++ tailWord_1248326).sum := by decide
  have hdescent : baseEnd_1248326 < baseStart_1248326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248385 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 3]
def baseStart_1248385 : Nat := 118140960795 + 1248385 * 2 ^ 59
def prefixEnd_1248385 : Nat := 4983230072969 + 3 ^ 40 * 1248385 * 2
def baseEnd_1248385 : Nat := 284898465272534854065017

theorem tailTrace_1248385 : CollatzResearch.WordTrace tailWord_1248385 prefixEnd_1248385 284898465272534854065017 := by
  unfold tailWord_1248385
  simp only [CollatzResearch.WordTrace]
  refine ⟨45532341582321827028818609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30354894388214551352545739 45532341582321827028818609)
  ·
    refine ⟨34149256186741370271613957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45532341582321827028818609 34149256186741370271613957)
    ·
      refine ⟨6402985535014006925927617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34149256186741370271613957 6402985535014006925927617)
      ·
        refine ⟨4802239151260505194445713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6402985535014006925927617 4802239151260505194445713)
        ·
          refine ⟨3601679363445378895834285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4802239151260505194445713 3601679363445378895834285)
          ·
            refine ⟨1350629761292017085937857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3601679363445378895834285 1350629761292017085937857)
            ·
              refine ⟨1012972320969012814453393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350629761292017085937857 1012972320969012814453393)
              ·
                refine ⟨759729240726759610840045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012972320969012814453393 759729240726759610840045)
                ·
                  refine ⟨284898465272534854065017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 759729240726759610840045 284898465272534854065017)
                  ·
                    rfl

theorem cell21_1248385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_1248385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248385 prefixEnd_1248385 := by exact prefixLift 1248385
  have htrace : WordTrace (prefixWord ++ tailWord_1248385) baseStart_1248385 baseEnd_1248385 := by
    simpa [prefixWord, tailWord_1248385, baseEnd_1248385] using wordTrace_append hprefix tailTrace_1248385
  have hstable : (prefixWord ++ tailWord_1248385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248385).length < 2 ^ (prefixWord ++ tailWord_1248385).sum := by decide
  have hdescent : baseEnd_1248385 < baseStart_1248385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248410 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 7]
def baseStart_1248410 : Nat := 118140960795 + 1248410 * 2 ^ 59
def prefixEnd_1248410 : Nat := 4983230072969 + 3 ^ 40 * 1248410 * 2
def baseEnd_1248410 : Nat := 284904170613140366148299

theorem tailTrace_1248410 : CollatzResearch.WordTrace tailWord_1248410 prefixEnd_1248410 284904170613140366148299 := by
  unfold tailWord_1248410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11383313351807814074619671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30355502271487504198985789 11383313351807814074619671)
  ·
    refine ⟨17074970027711721111929507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11383313351807814074619671 17074970027711721111929507)
    ·
      refine ⟨25612455041567581667894261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17074970027711721111929507 25612455041567581667894261)
      ·
        refine ⟨2401167660146960781365087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25612455041567581667894261 2401167660146960781365087)
        ·
          refine ⟨3601751490220441172047631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401167660146960781365087 3601751490220441172047631)
          ·
            refine ⟨5402627235330661758071447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601751490220441172047631 5402627235330661758071447)
            ·
              refine ⟨8103940852995992637107171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402627235330661758071447 8103940852995992637107171)
              ·
                refine ⟨12155911279493988955660757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8103940852995992637107171 12155911279493988955660757)
                ·
                  refine ⟨284904170613140366148299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12155911279493988955660757 284904170613140366148299)
                  ·
                    rfl

theorem cell21_1248410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_1248410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248410 prefixEnd_1248410 := by exact prefixLift 1248410
  have htrace : WordTrace (prefixWord ++ tailWord_1248410) baseStart_1248410 baseEnd_1248410 := by
    simpa [prefixWord, tailWord_1248410, baseEnd_1248410] using wordTrace_append hprefix tailTrace_1248410
  have hstable : (prefixWord ++ tailWord_1248410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248410).length < 2 ^ (prefixWord ++ tailWord_1248410).sum := by decide
  have hdescent : baseEnd_1248410 < baseStart_1248410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248441 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1248441 : Nat := 118140960795 + 1248441 * 2 ^ 59
def prefixEnd_1248441 : Nat := 4983230072969 + 3 ^ 40 * 1248441 * 2
def baseEnd_1248441 : Nat := 284911245235491201131569

theorem tailTrace_1248441 : CollatzResearch.WordTrace tailWord_1248441 prefixEnd_1248441 284911245235491201131569 := by
  unfold tailWord_1248441
  simp only [CollatzResearch.WordTrace]
  refine ⟨45534384070118948592857177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30356256046745965728571451 45534384070118948592857177)
  ·
    refine ⟨34150788052589211444642883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45534384070118948592857177 34150788052589211444642883)
    ·
      refine ⟨51226182078883817166964325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34150788052589211444642883 51226182078883817166964325)
      ·
        refine ⟨9604909139790715718805811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51226182078883817166964325 9604909139790715718805811)
        ·
          refine ⟨14407363709686073578208717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9604909139790715718805811 14407363709686073578208717)
          ·
            refine ⟨5402761391132277591828269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14407363709686073578208717 5402761391132277591828269)
            ·
              refine ⟨2026035521674604096935601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5402761391132277591828269 2026035521674604096935601)
              ·
                refine ⟨1519526641255953072701701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026035521674604096935601 1519526641255953072701701)
                ·
                  refine ⟨284911245235491201131569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519526641255953072701701 284911245235491201131569)
                  ·
                    rfl

theorem cell21_1248441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1248441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248441 prefixEnd_1248441 := by exact prefixLift 1248441
  have htrace : WordTrace (prefixWord ++ tailWord_1248441) baseStart_1248441 baseEnd_1248441 := by
    simpa [prefixWord, tailWord_1248441, baseEnd_1248441] using wordTrace_append hprefix tailTrace_1248441
  have hstable : (prefixWord ++ tailWord_1248441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248441).length < 2 ^ (prefixWord ++ tailWord_1248441).sum := by decide
  have hdescent : baseEnd_1248441 < baseStart_1248441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248458 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 4]
def baseStart_1248458 : Nat := 118140960795 + 1248458 * 2 ^ 59
def prefixEnd_1248458 : Nat := 4983230072969 + 3 ^ 40 * 1248458 * 2
def baseEnd_1248458 : Nat := 284915124867102949348201

theorem tailTrace_1248458 : CollatzResearch.WordTrace tailWord_1248458 prefixEnd_1248458 284915124867102949348201 := by
  unfold tailWord_1248458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11383751027764340124056507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30356669407371573664150685 11383751027764340124056507)
  ·
    refine ⟨17075626541646510186084761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11383751027764340124056507 17075626541646510186084761)
    ·
      refine ⟨12806719906234882639563571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17075626541646510186084761 12806719906234882639563571)
      ·
        refine ⟨19210079859352323959345357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12806719906234882639563571 19210079859352323959345357)
        ·
          refine ⟨7203779947257121484754509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19210079859352323959345357 7203779947257121484754509)
          ·
            refine ⟨2701417480221420556782941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7203779947257121484754509 2701417480221420556782941)
            ·
              refine ⟨1013031555083032708793603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2701417480221420556782941 1013031555083032708793603)
              ·
                refine ⟨1519547332624549063190405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013031555083032708793603 1519547332624549063190405)
                ·
                  refine ⟨284915124867102949348201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519547332624549063190405 284915124867102949348201)
                  ·
                    rfl

theorem cell21_1248458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 4].length) (baseStart_1248458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248458 prefixEnd_1248458 := by exact prefixLift 1248458
  have htrace : WordTrace (prefixWord ++ tailWord_1248458) baseStart_1248458 baseEnd_1248458 := by
    simpa [prefixWord, tailWord_1248458, baseEnd_1248458] using wordTrace_append hprefix tailTrace_1248458
  have hstable : (prefixWord ++ tailWord_1248458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248458).length < 2 ^ (prefixWord ++ tailWord_1248458).sum := by decide
  have hdescent : baseEnd_1248458 < baseStart_1248458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248576 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1248576 : Nat := 118140960795 + 1248576 * 2 ^ 59
def prefixEnd_1248576 : Nat := 4983230072969 + 3 ^ 40 * 1248576 * 2
def baseEnd_1248576 : Nat := 284942054074760966381293

theorem tailTrace_1248576 : CollatzResearch.WordTrace tailWord_1248576 prefixEnd_1248576 284942054074760966381293 := by
  unfold tailWord_1248576
  simp only [CollatzResearch.WordTrace]
  refine ⟨22769653962314933324510791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30359538616419911099347721 22769653962314933324510791)
  ·
    refine ⟨34154480943472399986766187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22769653962314933324510791 34154480943472399986766187)
    ·
      refine ⟨51231721415208599980149281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34154480943472399986766187 51231721415208599980149281)
      ·
        refine ⟨38423791061406449985111961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51231721415208599980149281 38423791061406449985111961)
        ·
          refine ⟨28817843296054837488833971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38423791061406449985111961 28817843296054837488833971)
          ·
            refine ⟨43226764944082256233250957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28817843296054837488833971 43226764944082256233250957)
            ·
              refine ⟨16210036854030846087469109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43226764944082256233250957 16210036854030846087469109)
              ·
                refine ⟨1519690955065391820700229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16210036854030846087469109 1519690955065391820700229)
                ·
                  refine ⟨284942054074760966381293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519690955065391820700229 284942054074760966381293)
                  ·
                    rfl

theorem cell21_1248576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1248576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248576 prefixEnd_1248576 := by exact prefixLift 1248576
  have htrace : WordTrace (prefixWord ++ tailWord_1248576) baseStart_1248576 baseEnd_1248576 := by
    simpa [prefixWord, tailWord_1248576, baseEnd_1248576] using wordTrace_append hprefix tailTrace_1248576
  have hstable : (prefixWord ++ tailWord_1248576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248576).length < 2 ^ (prefixWord ++ tailWord_1248576).sum := by decide
  have hdescent : baseEnd_1248576 < baseStart_1248576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248641 : List Nat := [1, 2, 4, 3, 2, 2, 2, 5]
def baseStart_1248641 : Nat := 118140960795 + 1248641 * 2 ^ 59
def prefixEnd_1248641 : Nat := 4983230072969 + 3 ^ 40 * 1248641 * 2
def baseEnd_1248641 : Nat := 94985629320111765932609

theorem tailTrace_1248641 : CollatzResearch.WordTrace tailWord_1248641 prefixEnd_1248641 94985629320111765932609 := by
  unfold tailWord_1248641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541678669394382750137777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30361119112929588500091851 45541678669394382750137777)
  ·
    refine ⟨34156259002045787062603333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45541678669394382750137777 34156259002045787062603333)
    ·
      refine ⟨6404298562883585074238125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34156259002045787062603333 6404298562883585074238125)
      ·
        refine ⟨2401611961081344402839297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6404298562883585074238125 2401611961081344402839297)
        ·
          refine ⟨1801208970811008302129473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2401611961081344402839297 1801208970811008302129473)
          ·
            refine ⟨1350906728108256226597105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801208970811008302129473 1350906728108256226597105)
            ·
              refine ⟨1013180046081192169947829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350906728108256226597105 1013180046081192169947829)
              ·
                refine ⟨94985629320111765932609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1013180046081192169947829 94985629320111765932609)
                ·
                  rfl

theorem cell21_1248641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 2, 5].length) (baseStart_1248641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248641 prefixEnd_1248641 := by exact prefixLift 1248641
  have htrace : WordTrace (prefixWord ++ tailWord_1248641) baseStart_1248641 baseEnd_1248641 := by
    simpa [prefixWord, tailWord_1248641, baseEnd_1248641] using wordTrace_append hprefix tailTrace_1248641
  have hstable : (prefixWord ++ tailWord_1248641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248641).length < 2 ^ (prefixWord ++ tailWord_1248641).sum := by decide
  have hdescent : baseEnd_1248641 < baseStart_1248641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248728 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 4]
def baseStart_1248728 : Nat := 118140960795 + 1248728 * 2 ^ 59
def prefixEnd_1248728 : Nat := 4983230072969 + 3 ^ 40 * 1248728 * 2
def baseEnd_1248728 : Nat := 284976742545642479847649

theorem tailTrace_1248728 : CollatzResearch.WordTrace tailWord_1248728 prefixEnd_1248728 284976742545642479847649 := by
  unfold tailWord_1248728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772425910039598304277419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30363234546719464405703225 22772425910039598304277419)
  ·
    refine ⟨34158638865059397456416129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22772425910039598304277419 34158638865059397456416129)
    ·
      refine ⟨25618979148794548092312097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34158638865059397456416129 25618979148794548092312097)
      ·
        refine ⟨19214234361595911069234073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25618979148794548092312097 19214234361595911069234073)
        ·
          refine ⟨14410675771196933301925555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19214234361595911069234073 14410675771196933301925555)
          ·
            refine ⟨21616013656795399952888333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14410675771196933301925555 21616013656795399952888333)
            ·
              refine ⟨8106005121298274982333125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21616013656795399952888333 8106005121298274982333125)
              ·
                refine ⟨1519875960243426559187461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8106005121298274982333125 1519875960243426559187461)
                ·
                  refine ⟨284976742545642479847649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1519875960243426559187461 284976742545642479847649)
                  ·
                    rfl

theorem cell21_1248728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 4].length) (baseStart_1248728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248728 prefixEnd_1248728 := by exact prefixLift 1248728
  have htrace : WordTrace (prefixWord ++ tailWord_1248728) baseStart_1248728 baseEnd_1248728 := by
    simpa [prefixWord, tailWord_1248728, baseEnd_1248728] using wordTrace_append hprefix tailTrace_1248728
  have hstable : (prefixWord ++ tailWord_1248728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248728).length < 2 ^ (prefixWord ++ tailWord_1248728).sum := by decide
  have hdescent : baseEnd_1248728 < baseStart_1248728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248897 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1248897 : Nat := 118140960795 + 1248897 * 2 ^ 59
def prefixEnd_1248897 : Nat := 4983230072969 + 3 ^ 40 * 1248897 * 2
def baseEnd_1248897 : Nat := 285015310648135741530637

theorem tailTrace_1248897 : CollatzResearch.WordTrace tailWord_1248897 prefixEnd_1248897 285015310648135741530637 := by
  unfold tailWord_1248897
  simp only [CollatzResearch.WordTrace]
  refine ⟨45551015756466938471456945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30367343837644625647637963 45551015756466938471456945)
  ·
    refine ⟨34163261817350203853592709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45551015756466938471456945 34163261817350203853592709)
    ·
      refine ⟨6405611590753163222548633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34163261817350203853592709 6405611590753163222548633)
      ·
        refine ⟨4804208693064872416911475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6405611590753163222548633 4804208693064872416911475)
        ·
          refine ⟨7206313039597308625367213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804208693064872416911475 7206313039597308625367213)
          ·
            refine ⟨2702367389848990734512705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7206313039597308625367213 2702367389848990734512705)
            ·
              refine ⟨2026775542386743050884529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702367389848990734512705 2026775542386743050884529)
              ·
                refine ⟨1520081656790057288163397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026775542386743050884529 1520081656790057288163397)
                ·
                  refine ⟨285015310648135741530637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520081656790057288163397 285015310648135741530637)
                  ·
                    rfl

theorem cell21_1248897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1248897 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248897 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248897 prefixEnd_1248897 := by exact prefixLift 1248897
  have htrace : WordTrace (prefixWord ++ tailWord_1248897) baseStart_1248897 baseEnd_1248897 := by
    simpa [prefixWord, tailWord_1248897, baseEnd_1248897] using wordTrace_append hprefix tailTrace_1248897
  have hstable : (prefixWord ++ tailWord_1248897).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248897).length < 2 ^ (prefixWord ++ tailWord_1248897).sum := by decide
  have hdescent : baseEnd_1248897 < baseStart_1248897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248956 : List Nat := [2, 2, 2, 3, 1, 3, 1, 1, 6]
def baseStart_1248956 : Nat := 118140960795 + 1248956 * 2 ^ 59
def prefixEnd_1248956 : Nat := 4983230072969 + 3 ^ 40 * 1248956 * 2
def baseEnd_1248956 : Nat := 285028775251964750047183

theorem tailTrace_1248956 : CollatzResearch.WordTrace tailWord_1248956 prefixEnd_1248956 285028775251964750047183 := by
  unfold tailWord_1248956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776583831626595773927361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30368778442168794365236481 22776583831626595773927361)
  ·
    refine ⟨17082437873719946830445521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22776583831626595773927361 17082437873719946830445521)
    ·
      refine ⟨12811828405289960122834141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17082437873719946830445521 12811828405289960122834141)
      ·
        refine ⟨4804435651983735046062803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12811828405289960122834141 4804435651983735046062803)
        ·
          refine ⟨7206653477975602569094205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804435651983735046062803 7206653477975602569094205)
          ·
            refine ⟨2702495054240850963410327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7206653477975602569094205 2702495054240850963410327)
            ·
              refine ⟨4053742581361276445115491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2702495054240850963410327 4053742581361276445115491)
              ·
                refine ⟨6080613872041914667673237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053742581361276445115491 6080613872041914667673237)
                ·
                  refine ⟨285028775251964750047183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6080613872041914667673237 285028775251964750047183)
                  ·
                    rfl

theorem cell21_1248956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_1248956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1248956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1248956 prefixEnd_1248956 := by exact prefixLift 1248956
  have htrace : WordTrace (prefixWord ++ tailWord_1248956) baseStart_1248956 baseEnd_1248956 := by
    simpa [prefixWord, tailWord_1248956, baseEnd_1248956] using wordTrace_append hprefix tailTrace_1248956
  have hstable : (prefixWord ++ tailWord_1248956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248956).length < 2 ^ (prefixWord ++ tailWord_1248956).sum := by decide
  have hdescent : baseEnd_1248956 < baseStart_1248956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249015 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_1249015 : Nat := 118140960795 + 1249015 * 2 ^ 59
def prefixEnd_1249015 : Nat := 4983230072969 + 3 ^ 40 * 1249015 * 2
def baseEnd_1249015 : Nat := 285042239855793758563729

theorem tailTrace_1249015 : CollatzResearch.WordTrace tailWord_1249015 prefixEnd_1249015 285042239855793758563729 := by
  unfold tailWord_1249015
  simp only [CollatzResearch.WordTrace]
  refine ⟨45555319570039444624252499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30370213046692963082834999 45555319570039444624252499)
  ·
    refine ⟨68332979355059166936378749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45555319570039444624252499 68332979355059166936378749)
    ·
      refine ⟨25624867258147187601142031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68332979355059166936378749 25624867258147187601142031)
      ·
        refine ⟨38437300887220781401713047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25624867258147187601142031 38437300887220781401713047)
        ·
          refine ⟨57655951330831172102569571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38437300887220781401713047 57655951330831172102569571)
          ·
            refine ⟨86483926996246758153854357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57655951330831172102569571 86483926996246758153854357)
            ·
              refine ⟨4053934077949066788461923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86483926996246758153854357 4053934077949066788461923)
              ·
                refine ⟨6080901116923600182692885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4053934077949066788461923 6080901116923600182692885)
                ·
                  refine ⟨285042239855793758563729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6080901116923600182692885 285042239855793758563729)
                  ·
                    rfl

theorem cell21_1249015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_1249015 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249015 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249015 prefixEnd_1249015 := by exact prefixLift 1249015
  have htrace : WordTrace (prefixWord ++ tailWord_1249015) baseStart_1249015 baseEnd_1249015 := by
    simpa [prefixWord, tailWord_1249015, baseEnd_1249015] using wordTrace_append hprefix tailTrace_1249015
  have hstable : (prefixWord ++ tailWord_1249015).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249015).length < 2 ^ (prefixWord ++ tailWord_1249015).sum := by decide
  have hdescent : baseEnd_1249015 < baseStart_1249015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249032 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1249032 : Nat := 118140960795 + 1249032 * 2 ^ 59
def prefixEnd_1249032 : Nat := 4983230072969 + 3 ^ 40 * 1249032 * 2
def baseEnd_1249032 : Nat := 285046119487405506780361

theorem tailTrace_1249032 : CollatzResearch.WordTrace tailWord_1249032 prefixEnd_1249032 285046119487405506780361 := by
  unfold tailWord_1249032
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777969805488928263810675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30370626407318571018414233 22777969805488928263810675)
  ·
    refine ⟨34166954708233392395716013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22777969805488928263810675 34166954708233392395716013)
    ·
      refine ⟨12812608015587522148393505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34166954708233392395716013 12812608015587522148393505)
      ·
        refine ⟨9609456011690641611295129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12812608015587522148393505 9609456011690641611295129)
        ·
          refine ⟨7207092008767981208471347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9609456011690641611295129 7207092008767981208471347)
          ·
            refine ⟨10810638013151971812707021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207092008767981208471347 10810638013151971812707021)
            ·
              refine ⟨4053989254931989429765133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10810638013151971812707021 4053989254931989429765133)
              ·
                refine ⟨1520245970599496036161925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4053989254931989429765133 1520245970599496036161925)
                ·
                  refine ⟨285046119487405506780361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520245970599496036161925 285046119487405506780361)
                  ·
                    rfl

theorem cell21_1249032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1249032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249032 prefixEnd_1249032 := by exact prefixLift 1249032
  have htrace : WordTrace (prefixWord ++ tailWord_1249032) baseStart_1249032 baseEnd_1249032 := by
    simpa [prefixWord, tailWord_1249032, baseEnd_1249032] using wordTrace_append hprefix tailTrace_1249032
  have hstable : (prefixWord ++ tailWord_1249032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249032).length < 2 ^ (prefixWord ++ tailWord_1249032).sum := by decide
  have hdescent : baseEnd_1249032 < baseStart_1249032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249111 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 3]
def baseStart_1249111 : Nat := 118140960795 + 1249111 * 2 ^ 59
def prefixEnd_1249111 : Nat := 4983230072969 + 3 ^ 40 * 1249111 * 2
def baseEnd_1249111 : Nat := 285064148363718924963533

theorem tailTrace_1249111 : CollatzResearch.WordTrace tailWord_1249111 prefixEnd_1249111 285064148363718924963533 := by
  unfold tailWord_1249111
  simp only [CollatzResearch.WordTrace]
  refine ⟨45558820977691653019747187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30372547318461102013164791 45558820977691653019747187)
  ·
    refine ⟨68338231466537479529620781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45558820977691653019747187 68338231466537479529620781)
    ·
      refine ⟨25626836799951554823607793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68338231466537479529620781 25626836799951554823607793)
      ·
        refine ⟨19220127599963666117705845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25626836799951554823607793 19220127599963666117705845)
        ·
          refine ⟨1801886962496593698534923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19220127599963666117705845 1801886962496593698534923)
          ·
            refine ⟨2702830443744890547802385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801886962496593698534923 2702830443744890547802385)
            ·
              refine ⟨2027122832808667910851789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702830443744890547802385 2027122832808667910851789)
              ·
                refine ⟨760171062303250466569421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2027122832808667910851789 760171062303250466569421)
                ·
                  refine ⟨285064148363718924963533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760171062303250466569421 285064148363718924963533)
                  ·
                    rfl

theorem cell21_1249111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 3].length) (baseStart_1249111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249111 prefixEnd_1249111 := by exact prefixLift 1249111
  have htrace : WordTrace (prefixWord ++ tailWord_1249111) baseStart_1249111 baseEnd_1249111 := by
    simpa [prefixWord, tailWord_1249111, baseEnd_1249111] using wordTrace_append hprefix tailTrace_1249111
  have hstable : (prefixWord ++ tailWord_1249111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249111).length < 2 ^ (prefixWord ++ tailWord_1249111).sum := by decide
  have hdescent : baseEnd_1249111 < baseStart_1249111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249201 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 4]
def baseStart_1249201 : Nat := 118140960795 + 1249201 * 2 ^ 59
def prefixEnd_1249201 : Nat := 4983230072969 + 3 ^ 40 * 1249201 * 2
def baseEnd_1249201 : Nat := 285084687589898768463349

theorem tailTrace_1249201 : CollatzResearch.WordTrace tailWord_1249201 prefixEnd_1249201 285084687589898768463349 := by
  unfold tailWord_1249201
  simp only [CollatzResearch.WordTrace]
  refine ⟨45562103547365598390523457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30374735698243732260348971 45562103547365598390523457)
  ·
    refine ⟨34171577660524198792892593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45562103547365598390523457 34171577660524198792892593)
    ·
      refine ⟨25628683245393149094669445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34171577660524198792892593 25628683245393149094669445)
      ·
        refine ⟨4805378108511215455250521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25628683245393149094669445 4805378108511215455250521)
        ·
          refine ⟨3604033581383411591437891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805378108511215455250521 3604033581383411591437891)
          ·
            refine ⟨5406050372075117387156837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604033581383411591437891 5406050372075117387156837)
            ·
              refine ⟨1013634444764084510091907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5406050372075117387156837 1013634444764084510091907)
              ·
                refine ⟨1520451667146126765137861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013634444764084510091907 1520451667146126765137861)
                ·
                  refine ⟨285084687589898768463349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520451667146126765137861 285084687589898768463349)
                  ·
                    rfl

theorem cell21_1249201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 4].length) (baseStart_1249201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249201 prefixEnd_1249201 := by exact prefixLift 1249201
  have htrace : WordTrace (prefixWord ++ tailWord_1249201) baseStart_1249201 baseEnd_1249201 := by
    simpa [prefixWord, tailWord_1249201, baseEnd_1249201] using wordTrace_append hprefix tailTrace_1249201
  have hstable : (prefixWord ++ tailWord_1249201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249201).length < 2 ^ (prefixWord ++ tailWord_1249201).sum := by decide
  have hdescent : baseEnd_1249201 < baseStart_1249201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249238 : List Nat := [5, 2, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1249238 : Nat := 118140960795 + 1249238 * 2 ^ 59
def prefixEnd_1249238 : Nat := 4983230072969 + 3 ^ 40 * 1249238 * 2
def baseEnd_1249238 : Nat := 285093131493994926346607

theorem tailTrace_1249238 : CollatzResearch.WordTrace tailWord_1249238 prefixEnd_1249238 285093131493994926346607 := by
  unfold tailWord_1249238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847715815514472106851273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30375635365487702473080245 2847715815514472106851273)
  ·
    refine ⟨2135786861635854080138455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2847715815514472106851273 2135786861635854080138455)
    ·
      refine ⟨3203680292453781120207683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135786861635854080138455 3203680292453781120207683)
      ·
        refine ⟨4805520438680671680311525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203680292453781120207683 4805520438680671680311525)
        ·
          refine ⟨901035082252625940058411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4805520438680671680311525 901035082252625940058411)
          ·
            refine ⟨1351552623378938910087617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901035082252625940058411 1351552623378938910087617)
            ·
              refine ⟨1013664467534204182565713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351552623378938910087617 1013664467534204182565713)
              ·
                refine ⟨760248350650653136924285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013664467534204182565713 760248350650653136924285)
                ·
                  refine ⟨285093131493994926346607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760248350650653136924285 285093131493994926346607)
                  ·
                    rfl

theorem cell21_1249238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1249238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249238 prefixEnd_1249238 := by exact prefixLift 1249238
  have htrace : WordTrace (prefixWord ++ tailWord_1249238) baseStart_1249238 baseEnd_1249238 := by
    simpa [prefixWord, tailWord_1249238, baseEnd_1249238] using wordTrace_append hprefix tailTrace_1249238
  have hstable : (prefixWord ++ tailWord_1249238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249238).length < 2 ^ (prefixWord ++ tailWord_1249238).sum := by decide
  have hdescent : baseEnd_1249238 < baseStart_1249238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249288 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_1249288 : Nat := 118140960795 + 1249288 * 2 ^ 59
def prefixEnd_1249288 : Nat := 4983230072969 + 3 ^ 40 * 1249288 * 2
def baseEnd_1249288 : Nat := 285104542175205950513171

theorem tailTrace_1249288 : CollatzResearch.WordTrace tailWord_1249288 prefixEnd_1249288 285104542175205950513171 := by
  unfold tailWord_1249288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22782638349025206124470259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30376851132033608165960345 22782638349025206124470259)
  ·
    refine ⟨34173957523537809186705389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22782638349025206124470259 34173957523537809186705389)
    ·
      refine ⟨12815234071326678445014521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34173957523537809186705389 12815234071326678445014521)
      ·
        refine ⟨9611425553495008833760891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12815234071326678445014521 9611425553495008833760891)
        ·
          refine ⟨14417138330242513250641337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9611425553495008833760891 14417138330242513250641337)
          ·
            refine ⟨10812853747681884937981003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14417138330242513250641337 10812853747681884937981003)
            ·
              refine ⟨16219280621522827406971505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812853747681884937981003 16219280621522827406971505)
              ·
                refine ⟨12164460466142120555228629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16219280621522827406971505 12164460466142120555228629)
                ·
                  refine ⟨285104542175205950513171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12164460466142120555228629 285104542175205950513171)
                  ·
                    rfl

theorem cell21_1249288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_1249288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249288 prefixEnd_1249288 := by exact prefixLift 1249288
  have htrace : WordTrace (prefixWord ++ tailWord_1249288) baseStart_1249288 baseEnd_1249288 := by
    simpa [prefixWord, tailWord_1249288, baseEnd_1249288] using wordTrace_append hprefix tailTrace_1249288
  have hstable : (prefixWord ++ tailWord_1249288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249288).length < 2 ^ (prefixWord ++ tailWord_1249288).sum := by decide
  have hdescent : baseEnd_1249288 < baseStart_1249288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249409 : List Nat := [1, 2, 4, 2, 12]
def baseStart_1249409 : Nat := 118140960795 + 1249409 * 2 ^ 59
def prefixEnd_1249409 : Nat := 4983230072969 + 3 ^ 40 * 1249409 * 2
def baseEnd_1249409 : Nat := 3520150074367118876497

theorem tailTrace_1249409 : CollatzResearch.WordTrace tailWord_1249409 prefixEnd_1249409 3520150074367118876497 := by
  unfold tailWord_1249409
  simp only [CollatzResearch.WordTrace]
  refine ⟨45569689930612049914095281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30379793287074699942730187 45569689930612049914095281)
  ·
    refine ⟨34177267447959037435571461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45569689930612049914095281 34177267447959037435571461)
    ·
      refine ⟨6408237646492319519169649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34177267447959037435571461 6408237646492319519169649)
      ·
        refine ⟨4806178234869239639377237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6408237646492319519169649 4806178234869239639377237)
        ·
          refine ⟨3520150074367118876497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 4806178234869239639377237 3520150074367118876497)
          ·
            rfl

theorem cell21_1249409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 12].length) (baseStart_1249409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249409 prefixEnd_1249409 := by exact prefixLift 1249409
  have htrace : WordTrace (prefixWord ++ tailWord_1249409) baseStart_1249409 baseEnd_1249409 := by
    simpa [prefixWord, tailWord_1249409, baseEnd_1249409] using wordTrace_append hprefix tailTrace_1249409
  have hstable : (prefixWord ++ tailWord_1249409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249409).length < 2 ^ (prefixWord ++ tailWord_1249409).sum := by decide
  have hdescent : baseEnd_1249409 < baseStart_1249409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249412 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 4]
def baseStart_1249412 : Nat := 118140960795 + 1249412 * 2 ^ 59
def prefixEnd_1249412 : Nat := 4983230072969 + 3 ^ 40 * 1249412 * 2
def baseEnd_1249412 : Nat := 285132840664609290446251

theorem tailTrace_1249412 : CollatzResearch.WordTrace tailWord_1249412 prefixEnd_1249412 285132840664609290446251 := by
  unfold tailWord_1249412
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784899674800590713227245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30379866233067454284302993 22784899674800590713227245)
  ·
    refine ⟨8544337378050221517460217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22784899674800590713227245 8544337378050221517460217)
    ·
      refine ⟨6408253033537666138095163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8544337378050221517460217 6408253033537666138095163)
      ·
        refine ⟨9612379550306499207142745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408253033537666138095163 9612379550306499207142745)
        ·
          refine ⟨7209284662729874405357059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9612379550306499207142745 7209284662729874405357059)
          ·
            refine ⟨10813926994094811608035589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7209284662729874405357059 10813926994094811608035589)
            ·
              refine ⟨2027611311392777176506673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10813926994094811608035589 2027611311392777176506673)
              ·
                refine ⟨1520708483544582882380005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027611311392777176506673 1520708483544582882380005)
                ·
                  refine ⟨285132840664609290446251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520708483544582882380005 285132840664609290446251)
                  ·
                    rfl

theorem cell21_1249412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_1249412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249412 prefixEnd_1249412 := by exact prefixLift 1249412
  have htrace : WordTrace (prefixWord ++ tailWord_1249412) baseStart_1249412 baseEnd_1249412 := by
    simpa [prefixWord, tailWord_1249412, baseEnd_1249412] using wordTrace_append hprefix tailTrace_1249412
  have hstable : (prefixWord ++ tailWord_1249412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249412).length < 2 ^ (prefixWord ++ tailWord_1249412).sum := by decide
  have hdescent : baseEnd_1249412 < baseStart_1249412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249440 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1249440 : Nat := 118140960795 + 1249440 * 2 ^ 59
def prefixEnd_1249440 : Nat := 4983230072969 + 3 ^ 40 * 1249440 * 2
def baseEnd_1249440 : Nat := 285139230646087463979527

theorem tailTrace_1249440 : CollatzResearch.WordTrace tailWord_1249440 prefixEnd_1249440 285139230646087463979527 := by
  unfold tailWord_1249440
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785410296749871104236887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30380547062333161472315849 22785410296749871104236887)
  ·
    refine ⟨34178115445124806656355331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22785410296749871104236887 34178115445124806656355331)
    ·
      refine ⟨51267173167687209984532997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34178115445124806656355331 51267173167687209984532997)
      ·
        refine ⟨9612594968941351872099937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51267173167687209984532997 9612594968941351872099937)
        ·
          refine ⟨7209446226706013904074953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9612594968941351872099937 7209446226706013904074953)
          ·
            refine ⟨5407084670029510428056215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7209446226706013904074953 5407084670029510428056215)
            ·
              refine ⟨8110627005044265642084323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407084670029510428056215 8110627005044265642084323)
              ·
                refine ⟨12165940507566398463126485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8110627005044265642084323 12165940507566398463126485)
                ·
                  refine ⟨285139230646087463979527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12165940507566398463126485 285139230646087463979527)
                  ·
                    rfl

theorem cell21_1249440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1249440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249440 prefixEnd_1249440 := by exact prefixLift 1249440
  have htrace : WordTrace (prefixWord ++ tailWord_1249440) baseStart_1249440 baseEnd_1249440 := by
    simpa [prefixWord, tailWord_1249440, baseEnd_1249440] using wordTrace_append hprefix tailTrace_1249440
  have hstable : (prefixWord ++ tailWord_1249440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249440).length < 2 ^ (prefixWord ++ tailWord_1249440).sum := by decide
  have hdescent : baseEnd_1249440 < baseStart_1249440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249533 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 3]
def baseStart_1249533 : Nat := 118140960795 + 1249533 * 2 ^ 59
def prefixEnd_1249533 : Nat := 4983230072969 + 3 ^ 40 * 1249533 * 2
def baseEnd_1249533 : Nat := 285160454513139968929337

theorem tailTrace_1249533 : CollatzResearch.WordTrace tailWord_1249533 prefixEnd_1249533 285160454513139968929337 := by
  unfold tailWord_1249533
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574212582162819091609253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30382808388108546061072835 45574212582162819091609253)
  ·
    refine ⟨8545164859155528579676735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45574212582162819091609253 8545164859155528579676735)
    ·
      refine ⟨12817747288733292869515103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8545164859155528579676735 12817747288733292869515103)
      ·
        refine ⟨19226620933099939304272655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12817747288733292869515103 19226620933099939304272655)
        ·
          refine ⟨28839931399649908956408983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19226620933099939304272655 28839931399649908956408983)
          ·
            refine ⟨43259897099474863434613475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28839931399649908956408983 43259897099474863434613475)
            ·
              refine ⟨64889845649212295151920213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43259897099474863434613475 64889845649212295151920213)
              ·
                refine ⟨760427878701706583811565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 64889845649212295151920213 760427878701706583811565)
                ·
                  refine ⟨285160454513139968929337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760427878701706583811565 285160454513139968929337)
                  ·
                    rfl

theorem cell21_1249533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_1249533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249533 prefixEnd_1249533 := by exact prefixLift 1249533
  have htrace : WordTrace (prefixWord ++ tailWord_1249533) baseStart_1249533 baseEnd_1249533 := by
    simpa [prefixWord, tailWord_1249533, baseEnd_1249533] using wordTrace_append hprefix tailTrace_1249533
  have hstable : (prefixWord ++ tailWord_1249533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249533).length < 2 ^ (prefixWord ++ tailWord_1249533).sum := by decide
  have hdescent : baseEnd_1249533 < baseStart_1249533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249547 : List Nat := [1, 1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_1249547 : Nat := 118140960795 + 1249547 * 2 ^ 59
def prefixEnd_1249547 : Nat := 4983230072969 + 3 ^ 40 * 1249547 * 2
def baseEnd_1249547 : Nat := 285163649503879055695975

theorem tailTrace_1249547 : CollatzResearch.WordTrace tailWord_1249547 prefixEnd_1249547 285163649503879055695975 := by
  unfold tailWord_1249547
  simp only [CollatzResearch.WordTrace]
  refine ⟨45574723204112099482618895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383148802741399655079263 45574723204112099482618895)
  ·
    refine ⟨68362084806168149223928343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45574723204112099482618895 68362084806168149223928343)
    ·
      refine ⟨102543127209252223835892515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68362084806168149223928343 102543127209252223835892515)
      ·
        refine ⟨153814690813878335753838773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102543127209252223835892515 153814690813878335753838773)
        ·
          refine ⟨14420127263801093976922385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153814690813878335753838773 14420127263801093976922385)
          ·
            refine ⟨10815095447850820482691789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14420127263801093976922385 10815095447850820482691789)
            ·
              refine ⟨4055660792944057681009421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10815095447850820482691789 4055660792944057681009421)
              ·
                refine ⟨1520872797354021630378533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4055660792944057681009421 1520872797354021630378533)
                ·
                  refine ⟨285163649503879055695975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520872797354021630378533 285163649503879055695975)
                  ·
                    rfl

theorem cell21_1249547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_1249547 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249547 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249547 prefixEnd_1249547 := by exact prefixLift 1249547
  have htrace : WordTrace (prefixWord ++ tailWord_1249547) baseStart_1249547 baseEnd_1249547 := by
    simpa [prefixWord, tailWord_1249547, baseEnd_1249547] using wordTrace_append hprefix tailTrace_1249547
  have hstable : (prefixWord ++ tailWord_1249547).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249547).length < 2 ^ (prefixWord ++ tailWord_1249547).sum := by decide
  have hdescent : baseEnd_1249547 < baseStart_1249547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249578 : List Nat := [3, 1, 4, 2, 2, 9]
def baseStart_1249578 : Nat := 118140960795 + 1249578 * 2 ^ 59
def prefixEnd_1249578 : Nat := 4983230072969 + 3 ^ 40 * 1249578 * 2
def baseEnd_1249578 : Nat := 10561878671341847802935

theorem tailTrace_1249578 : CollatzResearch.WordTrace tailWord_1249578 prefixEnd_1249578 10561878671341847802935 := by
  unfold tailWord_1249578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393963466749947944249347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30383902577999861184664925 11393963466749947944249347)
  ·
    refine ⟨17090945200124921916374021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11393963466749947944249347 17090945200124921916374021)
    ·
      refine ⟨3204552225023422859320129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17090945200124921916374021 3204552225023422859320129)
      ·
        refine ⟨2403414168767567144490097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204552225023422859320129 2403414168767567144490097)
        ·
          refine ⟨1802560626575675358367573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403414168767567144490097 1802560626575675358367573)
          ·
            refine ⟨10561878671341847802935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1802560626575675358367573 10561878671341847802935)
            ·
              rfl

theorem cell21_1249578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 9].length) (baseStart_1249578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249578 prefixEnd_1249578 := by exact prefixLift 1249578
  have htrace : WordTrace (prefixWord ++ tailWord_1249578) baseStart_1249578 baseEnd_1249578 := by
    simpa [prefixWord, tailWord_1249578, baseEnd_1249578] using wordTrace_append hprefix tailTrace_1249578
  have hstable : (prefixWord ++ tailWord_1249578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249578).length < 2 ^ (prefixWord ++ tailWord_1249578).sum := by decide
  have hdescent : baseEnd_1249578 < baseStart_1249578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249637 : List Nat := [1, 3, 1, 3, 1, 4, 8]
def baseStart_1249637 : Nat := 118140960795 + 1249637 * 2 ^ 59
def prefixEnd_1249637 : Nat := 4983230072969 + 3 ^ 40 * 1249637 * 2
def baseEnd_1249637 : Nat := 31687132081117655466199

theorem tailTrace_1249637 : CollatzResearch.WordTrace tailWord_1249637 prefixEnd_1249637 31687132081117655466199 := by
  unfold tailWord_1249637
  simp only [CollatzResearch.WordTrace]
  refine ⟨45578005773786044853395165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30385337182524029902263443 45578005773786044853395165)
  ·
    refine ⟨17091752165169766820023187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45578005773786044853395165 17091752165169766820023187)
    ·
      refine ⟨25637628247754650230034781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17091752165169766820023187 25637628247754650230034781)
      ·
        refine ⟨9614110592907993836263043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25637628247754650230034781 9614110592907993836263043)
        ·
          refine ⟨14421165889361990754394565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9614110592907993836263043 14421165889361990754394565)
          ·
            refine ⟨2703968604255373266448981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14421165889361990754394565 2703968604255373266448981)
            ·
              refine ⟨31687132081117655466199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2703968604255373266448981 31687132081117655466199)
              ·
                rfl

theorem cell21_1249637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 8].length) (baseStart_1249637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249637 prefixEnd_1249637 := by exact prefixLift 1249637
  have htrace : WordTrace (prefixWord ++ tailWord_1249637) baseStart_1249637 baseEnd_1249637 := by
    simpa [prefixWord, tailWord_1249637, baseEnd_1249637] using wordTrace_append hprefix tailTrace_1249637
  have hstable : (prefixWord ++ tailWord_1249637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249637).length < 2 ^ (prefixWord ++ tailWord_1249637).sum := by decide
  have hdescent : baseEnd_1249637 < baseStart_1249637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249640 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 4]
def baseStart_1249640 : Nat := 118140960795 + 1249640 * 2 ^ 59
def prefixEnd_1249640 : Nat := 4983230072969 + 3 ^ 40 * 1249640 * 2
def baseEnd_1249640 : Nat := 285184873370931560645785

theorem tailTrace_1249640 : CollatzResearch.WordTrace tailWord_1249640 prefixEnd_1249640 285184873370931560645785 := by
  unfold tailWord_1249640
  simp only [CollatzResearch.WordTrace]
  refine ⟨22789057596387588182877187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30385410128516784243836249 22789057596387588182877187)
  ·
    refine ⟨34183586394581382274315781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22789057596387588182877187 34183586394581382274315781)
    ·
      refine ⟨6409422448984009176434209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34183586394581382274315781 6409422448984009176434209)
      ·
        refine ⟨4807066836738006882325657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6409422448984009176434209 4807066836738006882325657)
        ·
          refine ⟨3605300127553505161744243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4807066836738006882325657 3605300127553505161744243)
          ·
            refine ⟨5407950191330257742616365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3605300127553505161744243 5407950191330257742616365)
            ·
              refine ⟨2027981321748846653481137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5407950191330257742616365 2027981321748846653481137)
              ·
                refine ⟨1520985991311634990110853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027981321748846653481137 1520985991311634990110853)
                ·
                  refine ⟨285184873370931560645785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1520985991311634990110853 285184873370931560645785)
                  ·
                    rfl

theorem cell21_1249640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 4].length) (baseStart_1249640 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249640 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249640 prefixEnd_1249640 := by exact prefixLift 1249640
  have htrace : WordTrace (prefixWord ++ tailWord_1249640) baseStart_1249640 baseEnd_1249640 := by
    simpa [prefixWord, tailWord_1249640, baseEnd_1249640] using wordTrace_append hprefix tailTrace_1249640
  have hstable : (prefixWord ++ tailWord_1249640).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249640).length < 2 ^ (prefixWord ++ tailWord_1249640).sum := by decide
  have hdescent : baseEnd_1249640 < baseStart_1249640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249651 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_1249651 : Nat := 118140960795 + 1249651 * 2 ^ 59
def prefixEnd_1249651 : Nat := 4983230072969 + 3 ^ 40 * 1249651 * 2
def baseEnd_1249651 : Nat := 285187383720797985962429

theorem tailTrace_1249651 : CollatzResearch.WordTrace tailWord_1249651 prefixEnd_1249651 285187383720797985962429 := by
  unfold tailWord_1249651
  simp only [CollatzResearch.WordTrace]
  refine ⟨45578516395735325244404807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30385677597156883496269871 45578516395735325244404807)
  ·
    refine ⟨68367774593602987866607211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45578516395735325244404807 68367774593602987866607211)
    ·
      refine ⟨102551661890404481799910817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68367774593602987866607211 102551661890404481799910817)
      ·
        refine ⟨76913746417803361349933113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102551661890404481799910817 76913746417803361349933113)
        ·
          refine ⟨57685309813352521012449835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76913746417803361349933113 57685309813352521012449835)
          ·
            refine ⟨86527964720028781518674753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57685309813352521012449835 86527964720028781518674753)
            ·
              refine ⟨64895973540021586139006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86527964720028781518674753 64895973540021586139006065)
              ·
                refine ⟨48671980155016189604254549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64895973540021586139006065 48671980155016189604254549)
                ·
                  refine ⟨285187383720797985962429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 48671980155016189604254549 285187383720797985962429)
                  ·
                    rfl

theorem cell21_1249651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_1249651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249651 prefixEnd_1249651 := by exact prefixLift 1249651
  have htrace : WordTrace (prefixWord ++ tailWord_1249651) baseStart_1249651 baseEnd_1249651 := by
    simpa [prefixWord, tailWord_1249651, baseEnd_1249651] using wordTrace_append hprefix tailTrace_1249651
  have hstable : (prefixWord ++ tailWord_1249651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249651).length < 2 ^ (prefixWord ++ tailWord_1249651).sum := by decide
  have hdescent : baseEnd_1249651 < baseStart_1249651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249668 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1249668 : Nat := 118140960795 + 1249668 * 2 ^ 59
def prefixEnd_1249668 : Nat := 4983230072969 + 3 ^ 40 * 1249668 * 2
def baseEnd_1249668 : Nat := 285191263352409734179061

theorem tailTrace_1249668 : CollatzResearch.WordTrace tailWord_1249668 prefixEnd_1249668 285191263352409734179061 := by
  unfold tailWord_1249668
  simp only [CollatzResearch.WordTrace]
  refine ⟨22789568218336868573886829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30386090957782491431849105 22789568218336868573886829)
  ·
    refine ⟨8546088081876325715207561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22789568218336868573886829 8546088081876325715207561)
    ·
      refine ⟨6409566061407244286405671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8546088081876325715207561 6409566061407244286405671)
      ·
        refine ⟨9614349092110866429608507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409566061407244286405671 9614349092110866429608507)
        ·
          refine ⟨14421523638166299644412761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9614349092110866429608507 14421523638166299644412761)
          ·
            refine ⟨10816142728624724733309571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14421523638166299644412761 10816142728624724733309571)
            ·
              refine ⟨16224214092937087099964357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10816142728624724733309571 16224214092937087099964357)
              ·
                refine ⟨3042040142425703831243317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16224214092937087099964357 3042040142425703831243317)
                ·
                  refine ⟨285191263352409734179061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042040142425703831243317 285191263352409734179061)
                  ·
                    rfl

theorem cell21_1249668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1249668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249668 prefixEnd_1249668 := by exact prefixLift 1249668
  have htrace : WordTrace (prefixWord ++ tailWord_1249668) baseStart_1249668 baseEnd_1249668 := by
    simpa [prefixWord, tailWord_1249668, baseEnd_1249668] using wordTrace_append hprefix tailTrace_1249668
  have hstable : (prefixWord ++ tailWord_1249668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249668).length < 2 ^ (prefixWord ++ tailWord_1249668).sum := by decide
  have hdescent : baseEnd_1249668 < baseStart_1249668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249713 : List Nat := [1, 2, 2, 4, 1, 2, 1, 8]
def baseStart_1249713 : Nat := 118140960795 + 1249713 * 2 ^ 59
def prefixEnd_1249713 : Nat := 4983230072969 + 3 ^ 40 * 1249713 * 2
def baseEnd_1249713 : Nat := 95067177655166551976323

theorem tailTrace_1249713 : CollatzResearch.WordTrace tailWord_1249713 prefixEnd_1249713 95067177655166551976323 := by
  unfold tailWord_1249713
  simp only [CollatzResearch.WordTrace]
  refine ⟨45580777721510709833161793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30387185147673806555441195 45580777721510709833161793)
  ·
    refine ⟨34185583291133032374871345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45580777721510709833161793 34185583291133032374871345)
    ·
      refine ⟨25639187468349774281153509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34185583291133032374871345 25639187468349774281153509)
      ·
        refine ⟨4807347650315582677716283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25639187468349774281153509 4807347650315582677716283)
        ·
          refine ⟨7211021475473374016574425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807347650315582677716283 7211021475473374016574425)
          ·
            refine ⟨5408266106605030512430819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7211021475473374016574425 5408266106605030512430819)
            ·
              refine ⟨8112399159907545768646229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408266106605030512430819 8112399159907545768646229)
              ·
                refine ⟨95067177655166551976323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8112399159907545768646229 95067177655166551976323)
                ·
                  rfl

theorem cell21_1249713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_1249713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249713 prefixEnd_1249713 := by exact prefixLift 1249713
  have htrace : WordTrace (prefixWord ++ tailWord_1249713) baseStart_1249713 baseEnd_1249713 := by
    simpa [prefixWord, tailWord_1249713, baseEnd_1249713] using wordTrace_append hprefix tailTrace_1249713
  have hstable : (prefixWord ++ tailWord_1249713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249713).length < 2 ^ (prefixWord ++ tailWord_1249713).sum := by decide
  have hdescent : baseEnd_1249713 < baseStart_1249713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249761 : List Nat := [1, 2, 3, 1, 2, 2, 3, 4, 3]
def baseStart_1249761 : Nat := 118140960795 + 1249761 * 2 ^ 59
def prefixEnd_1249761 : Nat := 4983230072969 + 3 ^ 40 * 1249761 * 2
def baseEnd_1249761 : Nat := 285212487219462239128871

theorem tailTrace_1249761 : CollatzResearch.WordTrace tailWord_1249761 prefixEnd_1249761 285212487219462239128871 := by
  unfold tailWord_1249761
  simp only [CollatzResearch.WordTrace]
  refine ⟨45582528425336814030909137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30388352283557876020606091 45582528425336814030909137)
  ·
    refine ⟨34186896319002610523181853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45582528425336814030909137 34186896319002610523181853)
    ·
      refine ⟨12820086119625978946193195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34186896319002610523181853 12820086119625978946193195)
      ·
        refine ⟨19230129179438968419289793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12820086119625978946193195 19230129179438968419289793)
        ·
          refine ⟨14422596884579226314467345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19230129179438968419289793 14422596884579226314467345)
          ·
            refine ⟨10816947663434419735850509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14422596884579226314467345 10816947663434419735850509)
            ·
              refine ⟨4056355373787907400943941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10816947663434419735850509 4056355373787907400943941)
              ·
                refine ⟨760566632585232637676989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4056355373787907400943941 760566632585232637676989)
                ·
                  refine ⟨285212487219462239128871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760566632585232637676989 285212487219462239128871)
                  ·
                    rfl

theorem cell21_1249761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 4, 3].length) (baseStart_1249761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249761 prefixEnd_1249761 := by exact prefixLift 1249761
  have htrace : WordTrace (prefixWord ++ tailWord_1249761) baseStart_1249761 baseEnd_1249761 := by
    simpa [prefixWord, tailWord_1249761, baseEnd_1249761] using wordTrace_append hprefix tailTrace_1249761
  have hstable : (prefixWord ++ tailWord_1249761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249761).length < 2 ^ (prefixWord ++ tailWord_1249761).sum := by decide
  have hdescent : baseEnd_1249761 < baseStart_1249761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249820 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 5]
def baseStart_1249820 : Nat := 118140960795 + 1249820 * 2 ^ 59
def prefixEnd_1249820 : Nat := 4983230072969 + 3 ^ 40 * 1249820 * 2
def baseEnd_1249820 : Nat := 285225951823291247645417

theorem tailTrace_1249820 : CollatzResearch.WordTrace tailWord_1249820 prefixEnd_1249820 285225951823291247645417 := by
  unfold tailWord_1249820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22792340166061533553653457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30389786888082044738204609 22792340166061533553653457)
  ·
    refine ⟨17094255124546150165240093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22792340166061533553653457 17094255124546150165240093)
    ·
      refine ⟨6410345671704806311965035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17094255124546150165240093 6410345671704806311965035)
      ·
        refine ⟨9615518507557209467947553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410345671704806311965035 9615518507557209467947553)
        ·
          refine ⟨7211638880667907100960665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9615518507557209467947553 7211638880667907100960665)
          ·
            refine ⟨5408729160500930325720499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7211638880667907100960665 5408729160500930325720499)
            ·
              refine ⟨8113093740751395488580749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5408729160500930325720499 8113093740751395488580749)
              ·
                refine ⟨3042410152781773308217781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8113093740751395488580749 3042410152781773308217781)
                ·
                  refine ⟨285225951823291247645417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3042410152781773308217781 285225951823291247645417)
                  ·
                    rfl

theorem cell21_1249820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_1249820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249820 prefixEnd_1249820 := by exact prefixLift 1249820
  have htrace : WordTrace (prefixWord ++ tailWord_1249820) baseStart_1249820 baseEnd_1249820 := by
    simpa [prefixWord, tailWord_1249820, baseEnd_1249820] using wordTrace_append hprefix tailTrace_1249820
  have hstable : (prefixWord ++ tailWord_1249820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249820).length < 2 ^ (prefixWord ++ tailWord_1249820).sum := by decide
  have hdescent : baseEnd_1249820 < baseStart_1249820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249922 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1249922 : Nat := 118140960795 + 1249922 * 2 ^ 59
def prefixEnd_1249922 : Nat := 4983230072969 + 3 ^ 40 * 1249922 * 2
def baseEnd_1249922 : Nat := 285249229612961736945209

theorem tailTrace_1249922 : CollatzResearch.WordTrace tailWord_1249922 prefixEnd_1249922 285249229612961736945209 := by
  unfold tailWord_1249922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397100144438384631880005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30392267051835692351680013 11397100144438384631880005)
  ·
    refine ⟨2136956277082197118477501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11397100144438384631880005 2136956277082197118477501)
    ·
      refine ⟨801358603905823919429063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2136956277082197118477501 801358603905823919429063)
      ·
        refine ⟨1202037905858735879143595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801358603905823919429063 1202037905858735879143595)
        ·
          refine ⟨1803056858788103818715393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202037905858735879143595 1803056858788103818715393)
          ·
            refine ⟨1352292644091077864036545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803056858788103818715393 1352292644091077864036545)
            ·
              refine ⟨1014219483068308398027409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352292644091077864036545 1014219483068308398027409)
              ·
                refine ⟨760664612301231298520557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014219483068308398027409 760664612301231298520557)
                ·
                  refine ⟨285249229612961736945209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760664612301231298520557 285249229612961736945209)
                  ·
                    rfl

theorem cell21_1249922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1249922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249922 prefixEnd_1249922 := by exact prefixLift 1249922
  have htrace : WordTrace (prefixWord ++ tailWord_1249922) baseStart_1249922 baseEnd_1249922 := by
    simpa [prefixWord, tailWord_1249922, baseEnd_1249922] using wordTrace_append hprefix tailTrace_1249922
  have hstable : (prefixWord ++ tailWord_1249922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249922).length < 2 ^ (prefixWord ++ tailWord_1249922).sum := by decide
  have hdescent : baseEnd_1249922 < baseStart_1249922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249927 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_1249927 : Nat := 118140960795 + 1249927 * 2 ^ 59
def prefixEnd_1249927 : Nat := 4983230072969 + 3 ^ 40 * 1249927 * 2
def baseEnd_1249927 : Nat := 285250370681082839361865

theorem tailTrace_1249927 : CollatzResearch.WordTrace tailWord_1249927 prefixEnd_1249927 285250370681082839361865 := by
  unfold tailWord_1249927
  simp only [CollatzResearch.WordTrace]
  refine ⟨45588582942735424381452035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30392388628490282920968023 45588582942735424381452035)
  ·
    refine ⟨68382874414103136572178053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45588582942735424381452035 68382874414103136572178053)
    ·
      refine ⟨12821788952644338107283385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68382874414103136572178053 12821788952644338107283385)
      ·
        refine ⟨9616341714483253580462539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12821788952644338107283385 9616341714483253580462539)
        ·
          refine ⟨14424512571724880370693809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616341714483253580462539 14424512571724880370693809)
          ·
            refine ⟨10818384428793660278020357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14424512571724880370693809 10818384428793660278020357)
            ·
              refine ⟨2028447080398811302128817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10818384428793660278020357 2028447080398811302128817)
              ·
                refine ⟨1521335310299108476596613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028447080398811302128817 1521335310299108476596613)
                ·
                  refine ⟨285250370681082839361865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1521335310299108476596613 285250370681082839361865)
                  ·
                    rfl

theorem cell21_1249927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_1249927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249927 prefixEnd_1249927 := by exact prefixLift 1249927
  have htrace : WordTrace (prefixWord ++ tailWord_1249927) baseStart_1249927 baseEnd_1249927 := by
    simpa [prefixWord, tailWord_1249927, baseEnd_1249927] using wordTrace_append hprefix tailTrace_1249927
  have hstable : (prefixWord ++ tailWord_1249927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249927).length < 2 ^ (prefixWord ++ tailWord_1249927).sum := by decide
  have hdescent : baseEnd_1249927 < baseStart_1249927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249930 : List Nat := [3, 1, 2, 3, 3, 1, 1, 4, 3]
def baseStart_1249930 : Nat := 118140960795 + 1249930 * 2 ^ 59
def prefixEnd_1249930 : Nat := 4983230072969 + 3 ^ 40 * 1249930 * 2
def baseEnd_1249930 : Nat := 285251055321955500811859

theorem tailTrace_1249930 : CollatzResearch.WordTrace tailWord_1249930 prefixEnd_1249930 285251055321955500811859 := by
  unfold tailWord_1249930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11397173090431138973452811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30392461574483037262540829 11397173090431138973452811)
  ·
    refine ⟨17095759635646708460179217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11397173090431138973452811 17095759635646708460179217)
    ·
      refine ⟨12821819726735031345134413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17095759635646708460179217 12821819726735031345134413)
      ·
        refine ⟨4808182397525636754425405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12821819726735031345134413 4808182397525636754425405)
        ·
          refine ⟨1803068399072113782909527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4808182397525636754425405 1803068399072113782909527)
          ·
            refine ⟨2704602598608170674364291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1803068399072113782909527 2704602598608170674364291)
            ·
              refine ⟨4056903897912256011546437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704602598608170674364291 4056903897912256011546437)
              ·
                refine ⟨760669480858548002164957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4056903897912256011546437 760669480858548002164957)
                ·
                  refine ⟨285251055321955500811859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760669480858548002164957 285251055321955500811859)
                  ·
                    rfl

theorem cell21_1249930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_1249930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1249930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1249930 prefixEnd_1249930 := by exact prefixLift 1249930
  have htrace : WordTrace (prefixWord ++ tailWord_1249930) baseStart_1249930 baseEnd_1249930 := by
    simpa [prefixWord, tailWord_1249930, baseEnd_1249930] using wordTrace_append hprefix tailTrace_1249930
  have hstable : (prefixWord ++ tailWord_1249930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249930).length < 2 ^ (prefixWord ++ tailWord_1249930).sum := by decide
  have hdescent : baseEnd_1249930 < baseStart_1249930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250017 : List Nat := [1, 2, 3, 1, 4, 2, 1, 7]
def baseStart_1250017 : Nat := 118140960795 + 1250017 * 2 ^ 59
def prefixEnd_1250017 : Nat := 4983230072969 + 3 ^ 40 * 1250017 * 2
def baseEnd_1250017 : Nat := 95090303302420894287227

theorem tailTrace_1250017 : CollatzResearch.WordTrace tailWord_1250017 prefixEnd_1250017 95090303302420894287227 := by
  unfold tailWord_1250017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45591865512409369752228305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30394577008272913168152203 45591865512409369752228305)
  ·
    refine ⟨34193899134307027314171229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45591865512409369752228305 34193899134307027314171229)
    ·
      refine ⟨12822712175365135242814211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34193899134307027314171229 12822712175365135242814211)
      ·
        refine ⟨19234068263047702864221317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12822712175365135242814211 19234068263047702864221317)
        ·
          refine ⟨3606387799321444287041497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19234068263047702864221317 3606387799321444287041497)
          ·
            refine ⟨2704790849491083215281123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606387799321444287041497 2704790849491083215281123)
            ·
              refine ⟨4057186274236624822921685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704790849491083215281123 4057186274236624822921685)
              ·
                refine ⟨95090303302420894287227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4057186274236624822921685 95090303302420894287227)
                ·
                  rfl

theorem cell21_1250017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_1250017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250017 prefixEnd_1250017 := by exact prefixLift 1250017
  have htrace : WordTrace (prefixWord ++ tailWord_1250017) baseStart_1250017 baseEnd_1250017 := by
    simpa [prefixWord, tailWord_1250017, baseEnd_1250017] using wordTrace_append hprefix tailTrace_1250017
  have hstable : (prefixWord ++ tailWord_1250017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250017).length < 2 ^ (prefixWord ++ tailWord_1250017).sum := by decide
  have hdescent : baseEnd_1250017 < baseStart_1250017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250124 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1250124 : Nat := 118140960795 + 1250124 * 2 ^ 59
def prefixEnd_1250124 : Nat := 4983230072969 + 3 ^ 40 * 1250124 * 2
def baseEnd_1250124 : Nat := 285295328765054274578129

theorem tailTrace_1250124 : CollatzResearch.WordTrace tailWord_1250124 prefixEnd_1250124 285295328765054274578129 := by
  unfold tailWord_1250124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22797884061510863513186713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30397178748681151350915617 22797884061510863513186713)
  ·
    refine ⟨17098413046133147634890035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22797884061510863513186713 17098413046133147634890035)
    ·
      refine ⟨25647619569199721452335053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17098413046133147634890035 25647619569199721452335053)
      ·
        refine ⟨9617857338449895544625645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25647619569199721452335053 9617857338449895544625645)
        ·
          refine ⟨3606696501918710829234617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9617857338449895544625645 3606696501918710829234617)
          ·
            refine ⟨2705022376439033121925963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606696501918710829234617 2705022376439033121925963)
            ·
              refine ⟨4057533564658549682888945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705022376439033121925963 4057533564658549682888945)
              ·
                refine ⟨3043150173493912262166709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4057533564658549682888945 3043150173493912262166709)
                ·
                  refine ⟨285295328765054274578129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043150173493912262166709 285295328765054274578129)
                  ·
                    rfl

theorem cell21_1250124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1250124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250124 prefixEnd_1250124 := by exact prefixLift 1250124
  have htrace : WordTrace (prefixWord ++ tailWord_1250124) baseStart_1250124 baseEnd_1250124 := by
    simpa [prefixWord, tailWord_1250124, baseEnd_1250124] using wordTrace_append hprefix tailTrace_1250124
  have hstable : (prefixWord ++ tailWord_1250124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250124).length < 2 ^ (prefixWord ++ tailWord_1250124).sum := by decide
  have hdescent : baseEnd_1250124 < baseStart_1250124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250186 : List Nat := [3, 1, 2, 4, 1, 1, 4, 5]
def baseStart_1250186 : Nat := 118140960795 + 1250186 * 2 ^ 59
def prefixEnd_1250186 : Nat := 4983230072969 + 3 ^ 40 * 1250186 * 2
def baseEnd_1250186 : Nat := 95103159336585314848223

theorem tailTrace_1250186 : CollatzResearch.WordTrace tailWord_1250186 prefixEnd_1250186 95103159336585314848223 := by
  unfold tailWord_1250186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11399507362199277903782603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30398686299198074410086941 11399507362199277903782603)
  ·
    refine ⟨17099261043298916855673905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11399507362199277903782603 17099261043298916855673905)
    ·
      refine ⟨12824445782474187641755429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17099261043298916855673905 12824445782474187641755429)
      ·
        refine ⟨2404583584213910182829143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12824445782474187641755429 2404583584213910182829143)
        ·
          refine ⟨3606875376320865274243715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404583584213910182829143 3606875376320865274243715)
          ·
            refine ⟨5410313064481297911365573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3606875376320865274243715 5410313064481297911365573)
            ·
              refine ⟨1014433699590243358381045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5410313064481297911365573 1014433699590243358381045)
              ·
                refine ⟨95103159336585314848223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1014433699590243358381045 95103159336585314848223)
                ·
                  rfl

theorem cell21_1250186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 5].length) (baseStart_1250186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250186 prefixEnd_1250186 := by exact prefixLift 1250186
  have htrace : WordTrace (prefixWord ++ tailWord_1250186) baseStart_1250186 baseEnd_1250186 := by
    simpa [prefixWord, tailWord_1250186, baseEnd_1250186] using wordTrace_append hprefix tailTrace_1250186
  have hstable : (prefixWord ++ tailWord_1250186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250186).length < 2 ^ (prefixWord ++ tailWord_1250186).sum := by decide
  have hdescent : baseEnd_1250186 < baseStart_1250186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250217 : List Nat := [1, 2, 1, 1, 1, 1, 9, 2, 3]
def baseStart_1250217 : Nat := 118140960795 + 1250217 * 2 ^ 59
def prefixEnd_1250217 : Nat := 4983230072969 + 3 ^ 40 * 1250217 * 2
def baseEnd_1250217 : Nat := 285316552632106779527939

theorem tailTrace_1250217 : CollatzResearch.WordTrace tailWord_1250217 prefixEnd_1250217 285316552632106779527939 := by
  unfold tailWord_1250217
  simp only [CollatzResearch.WordTrace]
  refine ⟨45599160111684803909508905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30399440074456535939672603 45599160111684803909508905)
  ·
    refine ⟨34199370083763602932131679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45599160111684803909508905 34199370083763602932131679)
    ·
      refine ⟨51299055125645404398197519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34199370083763602932131679 51299055125645404398197519)
      ·
        refine ⟨76948582688468106597296279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51299055125645404398197519 76948582688468106597296279)
        ·
          refine ⟨115422874032702159895944419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76948582688468106597296279 115422874032702159895944419)
          ·
            refine ⟨173134311049053239843916629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115422874032702159895944419 173134311049053239843916629)
            ·
              refine ⟨1014458853803046327210449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 173134311049053239843916629 1014458853803046327210449)
              ·
                refine ⟨760844140352284745407837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014458853803046327210449 760844140352284745407837)
                ·
                  refine ⟨285316552632106779527939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760844140352284745407837 285316552632106779527939)
                  ·
                    rfl

theorem cell21_1250217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 2, 3].length) (baseStart_1250217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250217 prefixEnd_1250217 := by exact prefixLift 1250217
  have htrace : WordTrace (prefixWord ++ tailWord_1250217) baseStart_1250217 baseEnd_1250217 := by
    simpa [prefixWord, tailWord_1250217, baseEnd_1250217] using wordTrace_append hprefix tailTrace_1250217
  have hstable : (prefixWord ++ tailWord_1250217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250217).length < 2 ^ (prefixWord ++ tailWord_1250217).sum := by decide
  have hdescent : baseEnd_1250217 < baseStart_1250217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250231 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 4]
def baseStart_1250231 : Nat := 118140960795 + 1250231 * 2 ^ 59
def prefixEnd_1250231 : Nat := 4983230072969 + 3 ^ 40 * 1250231 * 2
def baseEnd_1250231 : Nat := 285319747622845866294577

theorem tailTrace_1250231 : CollatzResearch.WordTrace tailWord_1250231 prefixEnd_1250231 285319747622845866294577 := by
  unfold tailWord_1250231
  simp only [CollatzResearch.WordTrace]
  refine ⟨45599670733634084300518547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30399780489089389533679031 45599670733634084300518547)
  ·
    refine ⟨68399506100451126450777821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45599670733634084300518547 68399506100451126450777821)
    ·
      refine ⟨25649814787669172419041683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68399506100451126450777821 25649814787669172419041683)
      ·
        refine ⟨38474722181503758628562525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25649814787669172419041683 38474722181503758628562525)
        ·
          refine ⟨14428020818063909485710947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38474722181503758628562525 14428020818063909485710947)
          ·
            refine ⟨21642031227095864228566421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14428020818063909485710947 21642031227095864228566421)
            ·
              refine ⟨1014470213770118635714051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 21642031227095864228566421 1014470213770118635714051)
              ·
                refine ⟨1521705320655177953571077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014470213770118635714051 1521705320655177953571077)
                ·
                  refine ⟨285319747622845866294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1521705320655177953571077 285319747622845866294577)
                  ·
                    rfl

theorem cell21_1250231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_1250231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250231 prefixEnd_1250231 := by exact prefixLift 1250231
  have htrace : WordTrace (prefixWord ++ tailWord_1250231) baseStart_1250231 baseEnd_1250231 := by
    simpa [prefixWord, tailWord_1250231, baseEnd_1250231] using wordTrace_append hprefix tailTrace_1250231
  have hstable : (prefixWord ++ tailWord_1250231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250231).length < 2 ^ (prefixWord ++ tailWord_1250231).sum := by decide
  have hdescent : baseEnd_1250231 < baseStart_1250231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250335 : List Nat := [1, 1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_1250335 : Nat := 118140960795 + 1250335 * 2 ^ 59
def prefixEnd_1250335 : Nat := 4983230072969 + 3 ^ 40 * 1250335 * 2
def baseEnd_1250335 : Nat := 285343481839764796561031

theorem tailTrace_1250335 : CollatzResearch.WordTrace tailWord_1250335 prefixEnd_1250335 285343481839764796561031 := by
  unfold tailWord_1250335
  simp only [CollatzResearch.WordTrace]
  refine ⟨45603463925257310062304459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30402309283504873374869639 45603463925257310062304459)
  ·
    refine ⟨68405195887885965093456689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45603463925257310062304459 68405195887885965093456689)
    ·
      refine ⟨51303896915914473820092517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68405195887885965093456689 51303896915914473820092517)
      ·
        refine ⟨9619480671733963841267347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51303896915914473820092517 9619480671733963841267347)
        ·
          refine ⟨14429221007600945761901021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9619480671733963841267347 14429221007600945761901021)
          ·
            refine ⟨5410957877850354660712883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14429221007600945761901021 5410957877850354660712883)
            ·
              refine ⟨8116436816775531991069325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5410957877850354660712883 8116436816775531991069325)
              ·
                refine ⟨3043663806290824496650997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8116436816775531991069325 3043663806290824496650997)
                ·
                  refine ⟨285343481839764796561031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3043663806290824496650997 285343481839764796561031)
                  ·
                    rfl

theorem cell21_1250335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_1250335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250335 prefixEnd_1250335 := by exact prefixLift 1250335
  have htrace : WordTrace (prefixWord ++ tailWord_1250335) baseStart_1250335 baseEnd_1250335 := by
    simpa [prefixWord, tailWord_1250335, baseEnd_1250335] using wordTrace_append hprefix tailTrace_1250335
  have hstable : (prefixWord ++ tailWord_1250335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250335).length < 2 ^ (prefixWord ++ tailWord_1250335).sum := by decide
  have hdescent : baseEnd_1250335 < baseStart_1250335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250386 : List Nat := [3, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_1250386 : Nat := 118140960795 + 1250386 * 2 ^ 59
def prefixEnd_1250386 : Nat := 4983230072969 + 3 ^ 40 * 1250386 * 2
def baseEnd_1250386 : Nat := 285355120734600041210927

theorem tailTrace_1250386 : CollatzResearch.WordTrace tailWord_1250386 prefixEnd_1250386 285355120734600041210927 := by
  unfold tailWord_1250386
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401331012018136443102753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30403549365381697181607341 11401331012018136443102753)
  ·
    refine ⟨8550998259013602332327065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11401331012018136443102753 8550998259013602332327065)
    ·
      refine ⟨6413248694260201749245299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8550998259013602332327065 6413248694260201749245299)
      ·
        refine ⟨9619873041390302623867949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6413248694260201749245299 9619873041390302623867949)
        ·
          refine ⟨3607452390521363483950481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9619873041390302623867949 3607452390521363483950481)
          ·
            refine ⟨2705589292891022612962861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607452390521363483950481 2705589292891022612962861)
            ·
              refine ⟨1014595984834133479861073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2705589292891022612962861 1014595984834133479861073)
              ·
                refine ⟨760946988625600109895805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014595984834133479861073 760946988625600109895805)
                ·
                  refine ⟨285355120734600041210927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760946988625600109895805 285355120734600041210927)
                  ·
                    rfl

theorem cell21_1250386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_1250386 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250386 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250386 prefixEnd_1250386 := by exact prefixLift 1250386
  have htrace : WordTrace (prefixWord ++ tailWord_1250386) baseStart_1250386 baseEnd_1250386 := by
    simpa [prefixWord, tailWord_1250386, baseEnd_1250386] using wordTrace_append hprefix tailTrace_1250386
  have hstable : (prefixWord ++ tailWord_1250386).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250386).length < 2 ^ (prefixWord ++ tailWord_1250386).sum := by decide
  have hdescent : baseEnd_1250386 < baseStart_1250386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250428 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_1250428 : Nat := 118140960795 + 1250428 * 2 ^ 59
def prefixEnd_1250428 : Nat := 4983230072969 + 3 ^ 40 * 1250428 * 2
def baseEnd_1250428 : Nat := 285364705706817301510841

theorem tailTrace_1250428 : CollatzResearch.WordTrace tailWord_1250428 prefixEnd_1250428 285364705706817301510841 := by
  unfold tailWord_1250428
  simp only [CollatzResearch.WordTrace]
  refine ⟨22803427956960193472719969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30404570609280257963626625 22803427956960193472719969)
  ·
    refine ⟨17102570967720145104539977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22803427956960193472719969 17102570967720145104539977)
    ·
      refine ⟨12826928225790108828404983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17102570967720145104539977 12826928225790108828404983)
      ·
        refine ⟨19240392338685163242607475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12826928225790108828404983 19240392338685163242607475)
        ·
          refine ⟨28860588508027744863911213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19240392338685163242607475 28860588508027744863911213)
          ·
            refine ⟨10822720690510404323966705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28860588508027744863911213 10822720690510404323966705)
            ·
              refine ⟨8117040517882803242975029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10822720690510404323966705 8117040517882803242975029)
              ·
                refine ⟨760972548551512804028909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8117040517882803242975029 760972548551512804028909)
                ·
                  refine ⟨285364705706817301510841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 760972548551512804028909 285364705706817301510841)
                  ·
                    rfl

theorem cell21_1250428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_1250428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250428 prefixEnd_1250428 := by exact prefixLift 1250428
  have htrace : WordTrace (prefixWord ++ tailWord_1250428) baseStart_1250428 baseEnd_1250428 := by
    simpa [prefixWord, tailWord_1250428, baseEnd_1250428] using wordTrace_append hprefix tailTrace_1250428
  have hstable : (prefixWord ++ tailWord_1250428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250428).length < 2 ^ (prefixWord ++ tailWord_1250428).sum := by decide
  have hdescent : baseEnd_1250428 < baseStart_1250428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250504 : List Nat := [2, 1, 3, 1, 2, 1, 4, 4, 3]
def baseStart_1250504 : Nat := 118140960795 + 1250504 * 2 ^ 59
def prefixEnd_1250504 : Nat := 4983230072969 + 3 ^ 40 * 1250504 * 2
def baseEnd_1250504 : Nat := 285382049942258058244019

theorem tailTrace_1250504 : CollatzResearch.WordTrace tailWord_1250504 prefixEnd_1250504 285382049942258058244019 := by
  unfold tailWord_1250504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22804813930822525962603283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30406418574430034616804377 22804813930822525962603283)
  ·
    refine ⟨34207220896233788943904925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22804813930822525962603283 34207220896233788943904925)
    ·
      refine ⟨12827707836087670853964347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34207220896233788943904925 12827707836087670853964347)
      ·
        refine ⟨19241561754131506280946521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12827707836087670853964347 19241561754131506280946521)
        ·
          refine ⟨14431171315598629710709891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19241561754131506280946521 14431171315598629710709891)
          ·
            refine ⟨21646756973397944566064837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431171315598629710709891 21646756973397944566064837)
            ·
              refine ⟨4058766932512114606137157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21646756973397944566064837 4058766932512114606137157)
              ·
                refine ⟨761018799846021488650717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4058766932512114606137157 761018799846021488650717)
                ·
                  refine ⟨285382049942258058244019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761018799846021488650717 285382049942258058244019)
                  ·
                    rfl

theorem cell21_1250504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 4, 3].length) (baseStart_1250504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250504 prefixEnd_1250504 := by exact prefixLift 1250504
  have htrace : WordTrace (prefixWord ++ tailWord_1250504) baseStart_1250504 baseEnd_1250504 := by
    simpa [prefixWord, tailWord_1250504, baseEnd_1250504] using wordTrace_append hprefix tailTrace_1250504
  have hstable : (prefixWord ++ tailWord_1250504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250504).length < 2 ^ (prefixWord ++ tailWord_1250504).sum := by decide
  have hdescent : baseEnd_1250504 < baseStart_1250504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250563 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_1250563 : Nat := 118140960795 + 1250563 * 2 ^ 59
def prefixEnd_1250563 : Nat := 4983230072969 + 3 ^ 40 * 1250563 * 2
def baseEnd_1250563 : Nat := 285395514546087066760565

theorem tailTrace_1250563 : CollatzResearch.WordTrace tailWord_1250563 prefixEnd_1250563 285395514546087066760565 := by
  unfold tailWord_1250563
  simp only [CollatzResearch.WordTrace]
  refine ⟨45611779768431305001604343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30407853178954203334402895 45611779768431305001604343)
  ·
    refine ⟨68417669652646957502406515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45611779768431305001604343 68417669652646957502406515)
    ·
      refine ⟨102626504478970436253609773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68417669652646957502406515 102626504478970436253609773)
      ·
        refine ⟨38484939179613913595103665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102626504478970436253609773 38484939179613913595103665)
        ·
          refine ⟨28863704384710435196327749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38484939179613913595103665 28863704384710435196327749)
          ·
            refine ⟨5411944572133206599311453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28863704384710435196327749 5411944572133206599311453)
            ·
              refine ⟨2029479214549952474741795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5411944572133206599311453 2029479214549952474741795)
              ·
                refine ⟨3044218821824928712112693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029479214549952474741795 3044218821824928712112693)
                ·
                  refine ⟨285395514546087066760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3044218821824928712112693 285395514546087066760565)
                  ·
                    rfl

theorem cell21_1250563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_1250563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250563 prefixEnd_1250563 := by exact prefixLift 1250563
  have htrace : WordTrace (prefixWord ++ tailWord_1250563) baseStart_1250563 baseEnd_1250563 := by
    simpa [prefixWord, tailWord_1250563, baseEnd_1250563] using wordTrace_append hprefix tailTrace_1250563
  have hstable : (prefixWord ++ tailWord_1250563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250563).length < 2 ^ (prefixWord ++ tailWord_1250563).sum := by decide
  have hdescent : baseEnd_1250563 < baseStart_1250563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250625 : List Nat := [1, 2, 5, 2, 1, 1, 3, 6]
def baseStart_1250625 : Nat := 118140960795 + 1250625 * 2 ^ 59
def prefixEnd_1250625 : Nat := 4983230072969 + 3 ^ 40 * 1250625 * 2
def baseEnd_1250625 : Nat := 95136554596929578909035

theorem tailTrace_1250625 : CollatzResearch.WordTrace tailWord_1250625 prefixEnd_1250625 95136554596929578909035 := by
  unfold tailWord_1250625
  simp only [CollatzResearch.WordTrace]
  refine ⟨45614041094206689590361329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30409360729471126393574219 45614041094206689590361329)
  ·
    refine ⟨34210530820655017192770997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45614041094206689590361329 34210530820655017192770997)
    ·
      refine ⟨3207237264436407861822281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34210530820655017192770997 3207237264436407861822281)
      ·
        refine ⟨2405427948327305896366711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3207237264436407861822281 2405427948327305896366711)
        ·
          refine ⟨3608141922490958844550067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405427948327305896366711 3608141922490958844550067)
          ·
            refine ⟨5412212883736438266825101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608141922490958844550067 5412212883736438266825101)
            ·
              refine ⟨2029579831401164350059413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5412212883736438266825101 2029579831401164350059413)
              ·
                refine ⟨95136554596929578909035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2029579831401164350059413 95136554596929578909035)
                ·
                  rfl

theorem cell21_1250625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_1250625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250625 prefixEnd_1250625 := by exact prefixLift 1250625
  have htrace : WordTrace (prefixWord ++ tailWord_1250625) baseStart_1250625 baseEnd_1250625 := by
    simpa [prefixWord, tailWord_1250625, baseEnd_1250625] using wordTrace_append hprefix tailTrace_1250625
  have hstable : (prefixWord ++ tailWord_1250625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250625).length < 2 ^ (prefixWord ++ tailWord_1250625).sum := by decide
  have hdescent : baseEnd_1250625 < baseStart_1250625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250656 : List Nat := [2, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_1250656 : Nat := 118140960795 + 1250656 * 2 ^ 59
def prefixEnd_1250656 : Nat := 4983230072969 + 3 ^ 40 * 1250656 * 2
def baseEnd_1250656 : Nat := 285416738413139571710375

theorem tailTrace_1250656 : CollatzResearch.WordTrace tailWord_1250656 prefixEnd_1250656 285416738413139571710375 := by
  unfold tailWord_1250656
  simp only [CollatzResearch.WordTrace]
  refine ⟨22807585878547190942369911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30410114504729587923159881 22807585878547190942369911)
  ·
    refine ⟨34211378817820786413554867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22807585878547190942369911 34211378817820786413554867)
    ·
      refine ⟨51317068226731179620332301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34211378817820786413554867 51317068226731179620332301)
      ·
        refine ⟨19243900585024192357624613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51317068226731179620332301 19243900585024192357624613)
        ·
          refine ⟨3608231359692036067054615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19243900585024192357624613 3608231359692036067054615)
          ·
            refine ⟨5412347039538054100581923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608231359692036067054615 5412347039538054100581923)
            ·
              refine ⟨8118520559307081150872885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412347039538054100581923 8118520559307081150872885)
              ·
                refine ⟨761111302435038857894333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8118520559307081150872885 761111302435038857894333)
                ·
                  refine ⟨285416738413139571710375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761111302435038857894333 285416738413139571710375)
                  ·
                    rfl

theorem cell21_1250656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_1250656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250656 prefixEnd_1250656 := by exact prefixLift 1250656
  have htrace : WordTrace (prefixWord ++ tailWord_1250656) baseStart_1250656 baseEnd_1250656 := by
    simpa [prefixWord, tailWord_1250656, baseEnd_1250656] using wordTrace_append hprefix tailTrace_1250656
  have hstable : (prefixWord ++ tailWord_1250656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250656).length < 2 ^ (prefixWord ++ tailWord_1250656).sum := by decide
  have hdescent : baseEnd_1250656 < baseStart_1250656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250718 : List Nat := [4, 3, 1, 2, 2, 2, 7]
def baseStart_1250718 : Nat := 118140960795 + 1250718 * 2 ^ 59
def prefixEnd_1250718 : Nat := 4983230072969 + 3 ^ 40 * 1250718 * 2
def baseEnd_1250718 : Nat := 31714543073093471297435

theorem tailTrace_1250718 : CollatzResearch.WordTrace tailWord_1250718 prefixEnd_1250718 31714543073093471297435 := by
  unfold tailWord_1250718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702179135358720809187101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30411622055246510982331205 5702179135358720809187101)
  ·
    refine ⟨2138317175759520303445163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5702179135358720809187101 2138317175759520303445163)
    ·
      refine ⟨3207475763639280455167745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2138317175759520303445163 3207475763639280455167745)
      ·
        refine ⟨2405606822729460341375809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3207475763639280455167745 2405606822729460341375809)
        ·
          refine ⟨1804205117047095256031857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405606822729460341375809 1804205117047095256031857)
          ·
            refine ⟨1353153837785321442023893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804205117047095256031857 1353153837785321442023893)
            ·
              refine ⟨31714543073093471297435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1353153837785321442023893 31714543073093471297435)
              ·
                rfl

theorem cell21_1250718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 7].length) (baseStart_1250718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250718 prefixEnd_1250718 := by exact prefixLift 1250718
  have htrace : WordTrace (prefixWord ++ tailWord_1250718) baseStart_1250718 baseEnd_1250718 := by
    simpa [prefixWord, tailWord_1250718, baseEnd_1250718] using wordTrace_append hprefix tailTrace_1250718
  have hstable : (prefixWord ++ tailWord_1250718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250718).length < 2 ^ (prefixWord ++ tailWord_1250718).sum := by decide
  have hdescent : baseEnd_1250718 < baseStart_1250718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250794 : List Nat := [3, 1, 3, 1, 5, 1, 1, 6]
def baseStart_1250794 : Nat := 118140960795 + 1250794 * 2 ^ 59
def prefixEnd_1250794 : Nat := 4983230072969 + 3 ^ 40 * 1250794 * 2
def baseEnd_1250794 : Nat := 95149410631093999470031

theorem tailTrace_1250794 : CollatzResearch.WordTrace tailWord_1250794 prefixEnd_1250794 95149410631093999470031 := by
  unfold tailWord_1250794
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405051257648607863315859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30413470020396287635508957 11405051257648607863315859)
  ·
    refine ⟨17107576886472911794973789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405051257648607863315859 17107576886472911794973789)
    ·
      refine ⟨6415341332427341923115171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17107576886472911794973789 6415341332427341923115171)
      ·
        refine ⟨9623011998641012884672757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415341332427341923115171 9623011998641012884672757)
        ·
          refine ⟨902157374872594957938071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9623011998641012884672757 902157374872594957938071)
          ·
            refine ⟨1353236062308892436907107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902157374872594957938071 1353236062308892436907107)
            ·
              refine ⟨2029854093463338655360661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353236062308892436907107 2029854093463338655360661)
              ·
                refine ⟨95149410631093999470031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2029854093463338655360661 95149410631093999470031)
                ·
                  rfl

theorem cell21_1250794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 6].length) (baseStart_1250794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250794 prefixEnd_1250794 := by exact prefixLift 1250794
  have htrace : WordTrace (prefixWord ++ tailWord_1250794) baseStart_1250794 baseEnd_1250794 := by
    simpa [prefixWord, tailWord_1250794, baseEnd_1250794] using wordTrace_append hprefix tailTrace_1250794
  have hstable : (prefixWord ++ tailWord_1250794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250794).length < 2 ^ (prefixWord ++ tailWord_1250794).sum := by decide
  have hdescent : baseEnd_1250794 < baseStart_1250794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250856 : List Nat := [2, 1, 5, 2, 2, 1, 3, 1, 4]
def baseStart_1250856 : Nat := 118140960795 + 1250856 * 2 ^ 59
def prefixEnd_1250856 : Nat := 4983230072969 + 3 ^ 40 * 1250856 * 2
def baseEnd_1250856 : Nat := 285462381137983668376633

theorem tailTrace_1250856 : CollatzResearch.WordTrace tailWord_1250856 prefixEnd_1250856 285462381137983668376633 := by
  unfold tailWord_1250856
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811233178184908021010211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30414977570913210694680281 22811233178184908021010211)
  ·
    refine ⟨34216849767277362031515317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22811233178184908021010211 34216849767277362031515317)
    ·
      refine ⟨3207829665682252690454561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34216849767277362031515317 3207829665682252690454561)
      ·
        refine ⟨2405872249261689517840921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3207829665682252690454561 2405872249261689517840921)
        ·
          refine ⟨1804404186946267138380691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405872249261689517840921 1804404186946267138380691)
          ·
            refine ⟨2706606280419400707571037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804404186946267138380691 2706606280419400707571037)
            ·
              refine ⟨1014977355157275265339139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2706606280419400707571037 1014977355157275265339139)
              ·
                refine ⟨1522466032735912898008709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014977355157275265339139 1522466032735912898008709)
                ·
                  refine ⟨285462381137983668376633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1522466032735912898008709 285462381137983668376633)
                  ·
                    rfl

theorem cell21_1250856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_1250856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250856 prefixEnd_1250856 := by exact prefixLift 1250856
  have htrace : WordTrace (prefixWord ++ tailWord_1250856) baseStart_1250856 baseEnd_1250856 := by
    simpa [prefixWord, tailWord_1250856, baseEnd_1250856] using wordTrace_append hprefix tailTrace_1250856
  have hstable : (prefixWord ++ tailWord_1250856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250856).length < 2 ^ (prefixWord ++ tailWord_1250856).sum := by decide
  have hdescent : baseEnd_1250856 < baseStart_1250856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250881 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_1250881 : Nat := 118140960795 + 1250881 * 2 ^ 59
def prefixEnd_1250881 : Nat := 4983230072969 + 3 ^ 40 * 1250881 * 2
def baseEnd_1250881 : Nat := 285468086478589180459915

theorem tailTrace_1250881 : CollatzResearch.WordTrace tailWord_1250881 prefixEnd_1250881 285468086478589180459915 := by
  unfold tailWord_1250881
  simp only [CollatzResearch.WordTrace]
  refine ⟨45623378181279245311680497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30415585454186163541120331 45623378181279245311680497)
  ·
    refine ⟨34217533635959433983760373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45623378181279245311680497 34217533635959433983760373)
    ·
      refine ⟨3207893778371196935977535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34217533635959433983760373 3207893778371196935977535)
      ·
        refine ⟨4811840667556795403966303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207893778371196935977535 4811840667556795403966303)
        ·
          refine ⟨7217761001335193105949455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811840667556795403966303 7217761001335193105949455)
          ·
            refine ⟨10826641502002789658924183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7217761001335193105949455 10826641502002789658924183)
            ·
              refine ⟨16239962253004184488386275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10826641502002789658924183 16239962253004184488386275)
              ·
                refine ⟨24359943379506276732579413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16239962253004184488386275 24359943379506276732579413)
                ·
                  refine ⟨285468086478589180459915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24359943379506276732579413 285468086478589180459915)
                  ·
                    rfl

theorem cell21_1250881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_1250881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250881 prefixEnd_1250881 := by exact prefixLift 1250881
  have htrace : WordTrace (prefixWord ++ tailWord_1250881) baseStart_1250881 baseEnd_1250881 := by
    simpa [prefixWord, tailWord_1250881, baseEnd_1250881] using wordTrace_append hprefix tailTrace_1250881
  have hstable : (prefixWord ++ tailWord_1250881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250881).length < 2 ^ (prefixWord ++ tailWord_1250881).sum := by decide
  have hdescent : baseEnd_1250881 < baseStart_1250881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250915 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 4]
def baseStart_1250915 : Nat := 118140960795 + 1250915 * 2 ^ 59
def prefixEnd_1250915 : Nat := 4983230072969 + 3 ^ 40 * 1250915 * 2
def baseEnd_1250915 : Nat := 285475845741812676893179

theorem tailTrace_1250915 : CollatzResearch.WordTrace tailWord_1250915 prefixEnd_1250915 285475845741812676893179 := by
  unfold tailWord_1250915
  simp only [CollatzResearch.WordTrace]
  refine ⟨45624618263156069118418199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30416412175437379412278799 45624618263156069118418199)
  ·
    refine ⟨68436927394734103677627299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45624618263156069118418199 68436927394734103677627299)
    ·
      refine ⟨102655391092101155516440949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68436927394734103677627299 102655391092101155516440949)
      ·
        refine ⟨9623942914884483329666339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102655391092101155516440949 9623942914884483329666339)
        ·
          refine ⟨14435914372326724994499509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9623942914884483329666339 14435914372326724994499509)
          ·
            refine ⟨1353366972405630468234329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14435914372326724994499509 1353366972405630468234329)
            ·
              refine ⟨1015025229304222851175747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353366972405630468234329 1015025229304222851175747)
              ·
                refine ⟨1522537843956334276763621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015025229304222851175747 1522537843956334276763621)
                ·
                  refine ⟨285475845741812676893179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1522537843956334276763621 285475845741812676893179)
                  ·
                    rfl

theorem cell21_1250915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_1250915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1250915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1250915 prefixEnd_1250915 := by exact prefixLift 1250915
  have htrace : WordTrace (prefixWord ++ tailWord_1250915) baseStart_1250915 baseEnd_1250915 := by
    simpa [prefixWord, tailWord_1250915, baseEnd_1250915] using wordTrace_append hprefix tailTrace_1250915
  have hstable : (prefixWord ++ tailWord_1250915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250915).length < 2 ^ (prefixWord ++ tailWord_1250915).sum := by decide
  have hdescent : baseEnd_1250915 < baseStart_1250915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251053 : List Nat := [1, 5, 1, 2, 1, 4, 1, 3, 3]
def baseStart_1251053 : Nat := 118140960795 + 1251053 * 2 ^ 59
def prefixEnd_1251053 : Nat := 4983230072969 + 3 ^ 40 * 1251053 * 2
def baseEnd_1251053 : Nat := 285507339221955103592897

theorem tailTrace_1251053 : CollatzResearch.WordTrace tailWord_1251053 prefixEnd_1251053 285507339221955103592897 := by
  unfold tailWord_1251053
  simp only [CollatzResearch.WordTrace]
  refine ⟨45629651536656118686941813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30419767691104079124627875 45629651536656118686941813)
  ·
    refine ⟨4277779831561511126900795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45629651536656118686941813 4277779831561511126900795)
    ·
      refine ⟨6416669747342266690351193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4277779831561511126900795 6416669747342266690351193)
      ·
        refine ⟨4812502310506700017763395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6416669747342266690351193 4812502310506700017763395)
        ·
          refine ⟨7218753465760050026645093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812502310506700017763395 7218753465760050026645093)
          ·
            refine ⟨1353516274830009379995955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7218753465760050026645093 1353516274830009379995955)
            ·
              refine ⟨2030274412245014069993933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353516274830009379995955 2030274412245014069993933)
              ·
                refine ⟨761352904591880276247725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2030274412245014069993933 761352904591880276247725)
                ·
                  refine ⟨285507339221955103592897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761352904591880276247725 285507339221955103592897)
                  ·
                    rfl

theorem cell21_1251053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_1251053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251053 prefixEnd_1251053 := by exact prefixLift 1251053
  have htrace : WordTrace (prefixWord ++ tailWord_1251053) baseStart_1251053 baseEnd_1251053 := by
    simpa [prefixWord, tailWord_1251053, baseEnd_1251053] using wordTrace_append hprefix tailTrace_1251053
  have hstable : (prefixWord ++ tailWord_1251053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251053).length < 2 ^ (prefixWord ++ tailWord_1251053).sum := by decide
  have hdescent : baseEnd_1251053 < baseStart_1251053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251070 : List Nat := [4, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_1251070 : Nat := 118140960795 + 1251070 * 2 ^ 59
def prefixEnd_1251070 : Nat := 4983230072969 + 3 ^ 40 * 1251070 * 2
def baseEnd_1251070 : Nat := 285511218853566851809529

theorem tailTrace_1251070 : CollatzResearch.WordTrace tailWord_1251070 prefixEnd_1251070 285511218853566851809529 := by
  unfold tailWord_1251070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5703783947199316323788833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30420181051729687060207109 5703783947199316323788833)
  ·
    refine ⟨4277837960399487242841625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5703783947199316323788833 4277837960399487242841625)
    ·
      refine ⟨3208378470299615432131219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4277837960399487242841625 3208378470299615432131219)
      ·
        refine ⟨4812567705449423148196829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3208378470299615432131219 4812567705449423148196829)
        ·
          refine ⟨1804712889543533680573811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4812567705449423148196829 1804712889543533680573811)
          ·
            refine ⟨2707069334315300520860717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804712889543533680573811 2707069334315300520860717)
            ·
              refine ⟨1015151000368237695322769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707069334315300520860717 1015151000368237695322769)
              ·
                refine ⟨761363250276178271492077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015151000368237695322769 761363250276178271492077)
                ·
                  refine ⟨285511218853566851809529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761363250276178271492077 285511218853566851809529)
                  ·
                    rfl

theorem cell21_1251070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_1251070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251070 prefixEnd_1251070 := by exact prefixLift 1251070
  have htrace : WordTrace (prefixWord ++ tailWord_1251070) baseStart_1251070 baseEnd_1251070 := by
    simpa [prefixWord, tailWord_1251070, baseEnd_1251070] using wordTrace_append hprefix tailTrace_1251070
  have hstable : (prefixWord ++ tailWord_1251070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251070).length < 2 ^ (prefixWord ++ tailWord_1251070).sum := by decide
  have hdescent : baseEnd_1251070 < baseStart_1251070 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251123 : List Nat := [1, 1, 1, 2, 7, 9]
def baseStart_1251123 : Nat := 118140960795 + 1251123 * 2 ^ 59
def prefixEnd_1251123 : Nat := 4983230072969 + 3 ^ 40 * 1251123 * 2
def baseEnd_1251123 : Nat := 10574937562061131015781

theorem tailTrace_1251123 : CollatzResearch.WordTrace tailWord_1251123 prefixEnd_1251123 10574937562061131015781 := by
  unfold tailWord_1251123
  simp only [CollatzResearch.WordTrace]
  refine ⟨45632204646402520641990023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30421469764268347094660015 45632204646402520641990023)
  ·
    refine ⟨68448306969603780962985035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45632204646402520641990023 68448306969603780962985035)
    ·
      refine ⟨102672460454405671444477553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68448306969603780962985035 102672460454405671444477553)
      ·
        refine ⟨77004345340804253583358165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102672460454405671444477553 77004345340804253583358165)
        ·
          refine ⟨1804789343925099693359957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77004345340804253583358165 1804789343925099693359957)
          ·
            refine ⟨10574937562061131015781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1804789343925099693359957 10574937562061131015781)
            ·
              rfl

theorem cell21_1251123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 9].length) (baseStart_1251123 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251123 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251123 prefixEnd_1251123 := by exact prefixLift 1251123
  have htrace : WordTrace (prefixWord ++ tailWord_1251123) baseStart_1251123 baseEnd_1251123 := by
    simpa [prefixWord, tailWord_1251123, baseEnd_1251123] using wordTrace_append hprefix tailTrace_1251123
  have hstable : (prefixWord ++ tailWord_1251123).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251123).length < 2 ^ (prefixWord ++ tailWord_1251123).sum := by decide
  have hdescent : baseEnd_1251123 < baseStart_1251123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251129 : List Nat := [1, 2, 1, 7, 1, 1, 1, 4, 3]
def baseStart_1251129 : Nat := 118140960795 + 1251129 * 2 ^ 59
def prefixEnd_1251129 : Nat := 4983230072969 + 3 ^ 40 * 1251129 * 2
def baseEnd_1251129 : Nat := 285524683457395860326075

theorem tailTrace_1251129 : CollatzResearch.WordTrace tailWord_1251129 prefixEnd_1251129 285524683457395860326075 := by
  unfold tailWord_1251129
  simp only [CollatzResearch.WordTrace]
  refine ⟨45632423484380783666708441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30421615656253855777805627 45632423484380783666708441)
  ·
    refine ⟨34224317613285587750031331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45632423484380783666708441 34224317613285587750031331)
    ·
      refine ⟨51336476419928381625046997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34224317613285587750031331 51336476419928381625046997)
      ·
        refine ⟨1203198666092071444337039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 51336476419928381625046997 1203198666092071444337039)
        ·
          refine ⟨1804797999138107166505559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203198666092071444337039 1804797999138107166505559)
          ·
            refine ⟨2707196998707160749758339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804797999138107166505559 2707196998707160749758339)
            ·
              refine ⟨4060795498060741124637509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707196998707160749758339 4060795498060741124637509)
              ·
                refine ⟨761399155886388960869533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4060795498060741124637509 761399155886388960869533)
                ·
                  refine ⟨285524683457395860326075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 761399155886388960869533 285524683457395860326075)
                  ·
                    rfl

theorem cell21_1251129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 4, 3].length) (baseStart_1251129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251129 prefixEnd_1251129 := by exact prefixLift 1251129
  have htrace : WordTrace (prefixWord ++ tailWord_1251129) baseStart_1251129 baseEnd_1251129 := by
    simpa [prefixWord, tailWord_1251129, baseEnd_1251129] using wordTrace_append hprefix tailTrace_1251129
  have hstable : (prefixWord ++ tailWord_1251129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251129).length < 2 ^ (prefixWord ++ tailWord_1251129).sum := by decide
  have hdescent : baseEnd_1251129 < baseStart_1251129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251154 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 7]
def baseStart_1251154 : Nat := 118140960795 + 1251154 * 2 ^ 59
def prefixEnd_1251154 : Nat := 4983230072969 + 3 ^ 40 * 1251154 * 2
def baseEnd_1251154 : Nat := 285530388798001372409357

theorem tailTrace_1251154 : CollatzResearch.WordTrace tailWord_1251154 prefixEnd_1251154 285530388798001372409357 := by
  unfold tailWord_1251154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408333827322553234092129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30422223539526808624245677 11408333827322553234092129)
  ·
    refine ⟨8556250370491914925569097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11408333827322553234092129 8556250370491914925569097)
    ·
      refine ⟨6417187777868936194176823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8556250370491914925569097 6417187777868936194176823)
      ·
        refine ⟨9625781666803404291265235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417187777868936194176823 9625781666803404291265235)
        ·
          refine ⟨14438672500205106436897853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9625781666803404291265235 14438672500205106436897853)
          ·
            refine ⟨5414502187576914913836695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14438672500205106436897853 5414502187576914913836695)
            ·
              refine ⟨8121753281365372370755043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5414502187576914913836695 8121753281365372370755043)
              ·
                refine ⟨12182629922048058556132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121753281365372370755043 12182629922048058556132565)
                ·
                  refine ⟨285530388798001372409357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12182629922048058556132565 285530388798001372409357)
                  ·
                    rfl

theorem cell21_1251154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_1251154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251154 prefixEnd_1251154 := by exact prefixLift 1251154
  have htrace : WordTrace (prefixWord ++ tailWord_1251154) baseStart_1251154 baseEnd_1251154 := by
    simpa [prefixWord, tailWord_1251154, baseEnd_1251154] using wordTrace_append hprefix tailTrace_1251154
  have hstable : (prefixWord ++ tailWord_1251154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251154).length < 2 ^ (prefixWord ++ tailWord_1251154).sum := by decide
  have hdescent : baseEnd_1251154 < baseStart_1251154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251233 : List Nat := [1, 2, 3, 4, 3, 1, 7]
def baseStart_1251233 : Nat := 118140960795 + 1251233 * 2 ^ 59
def prefixEnd_1251233 : Nat := 4983230072969 + 3 ^ 40 * 1251233 * 2
def baseEnd_1251233 : Nat := 31727601963812754510281

theorem tailTrace_1251233 : CollatzResearch.WordTrace tailWord_1251233 prefixEnd_1251233 31727601963812754510281 := by
  unfold tailWord_1251233
  simp only [CollatzResearch.WordTrace]
  refine ⟨45636216676004009428494353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30424144450669339618996235 45636216676004009428494353)
  ·
    refine ⟨34227162507003007071370765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45636216676004009428494353 34227162507003007071370765)
    ·
      refine ⟨12835185940126127651764037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34227162507003007071370765 12835185940126127651764037)
      ·
        refine ⟨2406597363773648934705757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12835185940126127651764037 2406597363773648934705757)
        ·
          refine ⟨902474011415118350514659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2406597363773648934705757 902474011415118350514659)
          ·
            refine ⟨1353711017122677525771989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902474011415118350514659 1353711017122677525771989)
            ·
              refine ⟨31727601963812754510281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1353711017122677525771989 31727601963812754510281)
              ·
                rfl

theorem cell21_1251233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 7].length) (baseStart_1251233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1251233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1251233 prefixEnd_1251233 := by exact prefixLift 1251233
  have htrace : WordTrace (prefixWord ++ tailWord_1251233) baseStart_1251233 baseEnd_1251233 := by
    simpa [prefixWord, tailWord_1251233, baseEnd_1251233] using wordTrace_append hprefix tailTrace_1251233
  have hstable : (prefixWord ++ tailWord_1251233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251233).length < 2 ^ (prefixWord ++ tailWord_1251233).sum := by decide
  have hdescent : baseEnd_1251233 < baseStart_1251233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
