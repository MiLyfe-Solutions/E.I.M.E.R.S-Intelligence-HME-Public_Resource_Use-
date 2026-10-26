import V185TrunkScan20Chunk151

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_924395 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_924395 : Nat := 118140960795 + 924395 * 2 ^ 59
def prefixEnd_924395 : Nat := 4983230072969 + 3 ^ 40 * 924395 * 2
def baseEnd_924395 : Nat := 421919066322680919121147

theorem tailTrace_924395 : CollatzResearch.WordTrace tailWord_924395 prefixEnd_924395 421919066322680919121147 := by
  unfold tailWord_924395
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715455486082263942110639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22476970324054842628073759 33715455486082263942110639)
  ·
    refine ⟨50573183229123395913165959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33715455486082263942110639 50573183229123395913165959)
    ·
      refine ⟨75859774843685093869748939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50573183229123395913165959 75859774843685093869748939)
      ·
        refine ⟨113789662265527640804623409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75859774843685093869748939 113789662265527640804623409)
        ·
          refine ⟨85342246699145730603467557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113789662265527640804623409 85342246699145730603467557)
          ·
            refine ⟨16001671256089824488150167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85342246699145730603467557 16001671256089824488150167)
            ·
              refine ⟨24002506884134736732225251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16001671256089824488150167 24002506884134736732225251)
              ·
                refine ⟨36003760326202105098337877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24002506884134736732225251 36003760326202105098337877)
                ·
                  refine ⟨421919066322680919121147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36003760326202105098337877 421919066322680919121147)
                  ·
                    rfl

theorem cell20_924395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_924395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924395 prefixEnd_924395 := by exact prefixLift 924395
  have htrace : WordTrace (prefixWord ++ tailWord_924395) baseStart_924395 baseEnd_924395 := by
    simpa [prefixWord, tailWord_924395, baseEnd_924395] using wordTrace_append hprefix tailTrace_924395
  have hstable : (prefixWord ++ tailWord_924395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924395).length < 2 ^ (prefixWord ++ tailWord_924395).sum := by decide
  have hdescent : baseEnd_924395 < baseStart_924395 := by decide
  rcases family_descends (prefixWord ++ tailWord_924395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924412 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_924412 : Nat := 118140960795 + 924412 * 2 ^ 59
def prefixEnd_924412 : Nat := 4983230072969 + 3 ^ 40 * 924412 * 2
def baseEnd_924412 : Nat := 421926825585904415554411

theorem tailTrace_924412 : CollatzResearch.WordTrace tailWord_924412 prefixEnd_924412 421926825585904415554411 := by
  unfold tailWord_924412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16858037763510337922739745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22477383684680450563652993 16858037763510337922739745)
  ·
    refine ⟨12643528322632753442054809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16858037763510337922739745 12643528322632753442054809)
    ·
      refine ⟨9482646241974565081541107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12643528322632753442054809 9482646241974565081541107)
      ·
        refine ⟨14223969362961847622311661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9482646241974565081541107 14223969362961847622311661)
        ·
          refine ⟨5333988511110692858366873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14223969362961847622311661 5333988511110692858366873)
          ·
            refine ⟨4000491383333019643775155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5333988511110692858366873 4000491383333019643775155)
            ·
              refine ⟨6000737074999529465662733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000491383333019643775155 6000737074999529465662733)
              ·
                refine ⟨2250276403124823549623525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6000737074999529465662733 2250276403124823549623525)
                ·
                  refine ⟨421926825585904415554411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250276403124823549623525 421926825585904415554411)
                  ·
                    rfl

theorem cell20_924412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_924412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924412 prefixEnd_924412 := by exact prefixLift 924412
  have htrace : WordTrace (prefixWord ++ tailWord_924412) baseStart_924412 baseEnd_924412 := by
    simpa [prefixWord, tailWord_924412, baseEnd_924412] using wordTrace_append hprefix tailTrace_924412
  have hstable : (prefixWord ++ tailWord_924412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924412).length < 2 ^ (prefixWord ++ tailWord_924412).sum := by decide
  have hdescent : baseEnd_924412 < baseStart_924412 := by decide
  rcases family_descends (prefixWord ++ tailWord_924412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924467 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_924467 : Nat := 118140960795 + 924467 * 2 ^ 59
def prefixEnd_924467 : Nat := 4983230072969 + 3 ^ 40 * 924467 * 2
def baseEnd_924467 : Nat := 421951929084568668720853

theorem tailTrace_924467 : CollatzResearch.WordTrace tailWord_924467 prefixEnd_924467 421951929084568668720853 := by
  unfold tailWord_924467
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718081541821420238731655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22478721027880946825821103 33718081541821420238731655)
  ·
    refine ⟨50577122312732130358097483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718081541821420238731655 50577122312732130358097483)
    ·
      refine ⟨75865683469098195537146225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50577122312732130358097483 75865683469098195537146225)
      ·
        refine ⟨56899262601823646652859669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75865683469098195537146225 56899262601823646652859669)
        ·
          refine ⟨2667152934460483436852797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56899262601823646652859669 2667152934460483436852797)
          ·
            refine ⟨1000182350422681288819799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667152934460483436852797 1000182350422681288819799)
            ·
              refine ⟨1500273525634021933229699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000182350422681288819799 1500273525634021933229699)
              ·
                refine ⟨2250410288451032899844549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500273525634021933229699 2250410288451032899844549)
                ·
                  refine ⟨421951929084568668720853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2250410288451032899844549 421951929084568668720853)
                  ·
                    rfl

theorem cell20_924467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_924467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924467 prefixEnd_924467 := by exact prefixLift 924467
  have htrace : WordTrace (prefixWord ++ tailWord_924467) baseStart_924467 baseEnd_924467 := by
    simpa [prefixWord, tailWord_924467, baseEnd_924467] using wordTrace_append hprefix tailTrace_924467
  have hstable : (prefixWord ++ tailWord_924467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924467).length < 2 ^ (prefixWord ++ tailWord_924467).sum := by decide
  have hdescent : baseEnd_924467 < baseStart_924467 := by decide
  rcases family_descends (prefixWord ++ tailWord_924467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924474 : List Nat := [3, 1, 1, 1, 6, 1, 2, 5]
def baseStart_924474 : Nat := 118140960795 + 924474 * 2 ^ 59
def prefixEnd_924474 : Nat := 4983230072969 + 3 ^ 40 * 924474 * 2
def baseEnd_924474 : Nat := 140651708025102585162497

theorem tailTrace_924474 : CollatzResearch.WordTrace tailWord_924474 prefixEnd_924474 140651708025102585162497 := by
  unfold tailWord_924474
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429584213199015108559119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22478891235197373622824317 8429584213199015108559119)
  ·
    refine ⟨12644376319798522662838679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8429584213199015108559119 12644376319798522662838679)
    ·
      refine ⟨18966564479697783994258019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12644376319798522662838679 18966564479697783994258019)
      ·
        refine ⟨28449846719546675991387029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18966564479697783994258019 28449846719546675991387029)
        ·
          refine ⟨1333586564978750437096267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28449846719546675991387029 1333586564978750437096267)
          ·
            refine ⟨2000379847468125655644401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333586564978750437096267 2000379847468125655644401)
            ·
              refine ⟨1500284885601094241733301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000379847468125655644401 1500284885601094241733301)
              ·
                refine ⟨140651708025102585162497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1500284885601094241733301 140651708025102585162497)
                ·
                  rfl

theorem cell20_924474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 5].length) (baseStart_924474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924474 prefixEnd_924474 := by exact prefixLift 924474
  have htrace : WordTrace (prefixWord ++ tailWord_924474) baseStart_924474 baseEnd_924474 := by
    simpa [prefixWord, tailWord_924474, baseEnd_924474] using wordTrace_append hprefix tailTrace_924474
  have hstable : (prefixWord ++ tailWord_924474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924474).length < 2 ^ (prefixWord ++ tailWord_924474).sum := by decide
  have hdescent : baseEnd_924474 < baseStart_924474 := by decide
  rcases family_descends (prefixWord ++ tailWord_924474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924519 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 3]
def baseStart_924519 : Nat := 118140960795 + 924519 * 2 ^ 59
def prefixEnd_924519 : Nat := 4983230072969 + 3 ^ 40 * 924519 * 2
def baseEnd_924519 : Nat := 421975663301487598987307

theorem tailTrace_924519 : CollatzResearch.WordTrace tailWord_924519 prefixEnd_924519 421975663301487598987307 := by
  unfold tailWord_924519
  simp only [CollatzResearch.WordTrace]
  refine ⟨33719978137633033119624611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22479985425088688746416407 33719978137633033119624611)
  ·
    refine ⟨50579967206449549679436917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33719978137633033119624611 50579967206449549679436917)
    ·
      refine ⟨4741871925604645282447211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50579967206449549679436917 4741871925604645282447211)
      ·
        refine ⟨7112807888406967923670817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4741871925604645282447211 7112807888406967923670817)
        ·
          refine ⟨5334605916305225942753113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7112807888406967923670817 5334605916305225942753113)
          ·
            refine ⟨4000954437228919457064835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5334605916305225942753113 4000954437228919457064835)
            ·
              refine ⟨6001431655843379185597253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4000954437228919457064835 6001431655843379185597253)
              ·
                refine ⟨1125268435470633597299485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6001431655843379185597253 1125268435470633597299485)
                ·
                  refine ⟨421975663301487598987307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125268435470633597299485 421975663301487598987307)
                  ·
                    rfl

theorem cell20_924519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_924519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924519 prefixEnd_924519 := by exact prefixLift 924519
  have htrace : WordTrace (prefixWord ++ tailWord_924519) baseStart_924519 baseEnd_924519 := by
    simpa [prefixWord, tailWord_924519, baseEnd_924519] using wordTrace_append hprefix tailTrace_924519
  have hstable : (prefixWord ++ tailWord_924519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924519).length < 2 ^ (prefixWord ++ tailWord_924519).sum := by decide
  have hdescent : baseEnd_924519 < baseStart_924519 := by decide
  rcases family_descends (prefixWord ++ tailWord_924519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924564 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 6]
def baseStart_924564 : Nat := 118140960795 + 924564 * 2 ^ 59
def prefixEnd_924564 : Nat := 4983230072969 + 3 ^ 40 * 924564 * 2
def baseEnd_924564 : Nat := 421996202527667442487123

theorem tailTrace_924564 : CollatzResearch.WordTrace tailWord_924564 prefixEnd_924564 421996202527667442487123 := by
  unfold tailWord_924564
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860809711235002902506373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22481079614980003870008497 16860809711235002902506373)
  ·
    refine ⟨3161401820856563044219945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16860809711235002902506373 3161401820856563044219945)
    ·
      refine ⟨2371051365642422283164959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3161401820856563044219945 2371051365642422283164959)
      ·
        refine ⟨3556577048463633424747439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371051365642422283164959 3556577048463633424747439)
        ·
          refine ⟨5334865572695450137121159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3556577048463633424747439 5334865572695450137121159)
          ·
            refine ⟨8002298359043175205681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334865572695450137121159 8002298359043175205681739)
            ·
              refine ⟨12003447538564762808522609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8002298359043175205681739 12003447538564762808522609)
              ·
                refine ⟨9002585653923572106391957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12003447538564762808522609 9002585653923572106391957)
                ·
                  refine ⟨421996202527667442487123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9002585653923572106391957 421996202527667442487123)
                  ·
                    rfl

theorem cell20_924564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_924564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924564 prefixEnd_924564 := by exact prefixLift 924564
  have htrace : WordTrace (prefixWord ++ tailWord_924564) baseStart_924564 baseEnd_924564 := by
    simpa [prefixWord, tailWord_924564, baseEnd_924564] using wordTrace_append hprefix tailTrace_924564
  have hstable : (prefixWord ++ tailWord_924564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924564).length < 2 ^ (prefixWord ++ tailWord_924564).sum := by decide
  have hdescent : baseEnd_924564 < baseStart_924564 := by decide
  rcases family_descends (prefixWord ++ tailWord_924564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924605 : List Nat := [1, 4, 1, 2, 4, 2, 2, 4]
def baseStart_924605 : Nat := 118140960795 + 924605 * 2 ^ 59
def prefixEnd_924605 : Nat := 4983230072969 + 3 ^ 40 * 924605 * 2
def baseEnd_924605 : Nat := 140671638681617840706763

theorem tailTrace_924605 : CollatzResearch.WordTrace tailWord_924605 prefixEnd_924605 140671638681617840706763 := by
  unfold tailWord_924605
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723114815321469807255269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22482076543547646538170179 33723114815321469807255269)
  ·
    refine ⟨6323084027872775588860363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33723114815321469807255269 6323084027872775588860363)
    ·
      refine ⟨9484626041809163383290545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323084027872775588860363 9484626041809163383290545)
      ·
        refine ⟨7113469531356872537467909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9484626041809163383290545 7113469531356872537467909)
        ·
          refine ⟨1333775537129413600775233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7113469531356872537467909 1333775537129413600775233)
          ·
            refine ⟨1000331652847060200581425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1333775537129413600775233 1000331652847060200581425)
            ·
              refine ⟨750248739635295150436069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000331652847060200581425 750248739635295150436069)
              ·
                refine ⟨140671638681617840706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750248739635295150436069 140671638681617840706763)
                ·
                  rfl

theorem cell20_924605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 2, 4].length) (baseStart_924605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924605 prefixEnd_924605 := by exact prefixLift 924605
  have htrace : WordTrace (prefixWord ++ tailWord_924605) baseStart_924605 baseEnd_924605 := by
    simpa [prefixWord, tailWord_924605, baseEnd_924605] using wordTrace_append hprefix tailTrace_924605
  have hstable : (prefixWord ++ tailWord_924605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924605).length < 2 ^ (prefixWord ++ tailWord_924605).sum := by decide
  have hdescent : baseEnd_924605 < baseStart_924605 := by decide
  rcases family_descends (prefixWord ++ tailWord_924605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924619 : List Nat := [1, 1, 1, 1, 3, 5, 3, 3, 2]
def baseStart_924619 : Nat := 118140960795 + 924619 * 2 ^ 59
def prefixEnd_924619 : Nat := 4983230072969 + 3 ^ 40 * 924619 * 2
def baseEnd_924619 : Nat := 422021306026331695653565

theorem tailTrace_924619 : CollatzResearch.WordTrace tailWord_924619 prefixEnd_924619 422021306026331695653565 := by
  unfold tailWord_924619
  simp only [CollatzResearch.WordTrace]
  refine ⟨33723625437270750198264911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22482416958180500132176607 33723625437270750198264911)
  ·
    refine ⟨50585438155906125297397367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33723625437270750198264911 50585438155906125297397367)
    ·
      refine ⟨75878157233859187946096051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50585438155906125297397367 75878157233859187946096051)
      ·
        refine ⟨113817235850788781919144077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75878157233859187946096051 113817235850788781919144077)
        ·
          refine ⟨42681463444045793219679029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113817235850788781919144077 42681463444045793219679029)
          ·
            refine ⟨4001387197879293114344909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42681463444045793219679029 4001387197879293114344909)
            ·
              refine ⟨1500520199204734917879341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4001387197879293114344909 1500520199204734917879341)
              ·
                refine ⟨562695074701775594204753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500520199204734917879341 562695074701775594204753)
                ·
                  refine ⟨422021306026331695653565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562695074701775594204753 422021306026331695653565)
                  ·
                    rfl

theorem cell20_924619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 2].length) (baseStart_924619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924619 prefixEnd_924619 := by exact prefixLift 924619
  have htrace : WordTrace (prefixWord ++ tailWord_924619) baseStart_924619 baseEnd_924619 := by
    simpa [prefixWord, tailWord_924619, baseEnd_924619] using wordTrace_append hprefix tailTrace_924619
  have hstable : (prefixWord ++ tailWord_924619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924619).length < 2 ^ (prefixWord ++ tailWord_924619).sum := by decide
  have hdescent : baseEnd_924619 < baseStart_924619 := by decide
  rcases family_descends (prefixWord ++ tailWord_924619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924626 : List Nat := [3, 2, 2, 3, 1, 3, 6]
def baseStart_924626 : Nat := 118140960795 + 924626 * 2 ^ 59
def prefixEnd_924626 : Nat := 4983230072969 + 3 ^ 40 * 924626 * 2
def baseEnd_924626 : Nat := 46891611224118975824467

theorem tailTrace_924626 : CollatzResearch.WordTrace tailWord_924626 prefixEnd_924626 46891611224118975824467 := by
  unfold tailWord_924626
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430970187061347598442433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22482587165496926929179821 8430970187061347598442433)
  ·
    refine ⟨6323227640296010698831825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8430970187061347598442433 6323227640296010698831825)
    ·
      refine ⟨4742420730222008024123869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6323227640296010698831825 4742420730222008024123869)
      ·
        refine ⟨1778407773833253009046451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4742420730222008024123869 1778407773833253009046451)
        ·
          refine ⟨2667611660749879513569677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778407773833253009046451 2667611660749879513569677)
          ·
            refine ⟨1000354372781204817588629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2667611660749879513569677 1000354372781204817588629)
            ·
              refine ⟨46891611224118975824467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1000354372781204817588629 46891611224118975824467)
              ·
                rfl

theorem cell20_924626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 6].length) (baseStart_924626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924626 prefixEnd_924626 := by exact prefixLift 924626
  have htrace : WordTrace (prefixWord ++ tailWord_924626) baseStart_924626 baseEnd_924626 := by
    simpa [prefixWord, tailWord_924626, baseEnd_924626] using wordTrace_append hprefix tailTrace_924626
  have hstable : (prefixWord ++ tailWord_924626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924626).length < 2 ^ (prefixWord ++ tailWord_924626).sum := by decide
  have hdescent : baseEnd_924626 < baseStart_924626 := by decide
  rcases family_descends (prefixWord ++ tailWord_924626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924647 : List Nat := [1, 1, 5, 2, 2, 1, 1, 7]
def baseStart_924647 : Nat := 118140960795 + 924647 * 2 ^ 59
def prefixEnd_924647 : Nat := 4983230072969 + 3 ^ 40 * 924647 * 2
def baseEnd_924647 : Nat := 140678028663096014240039

theorem tailTrace_924647 : CollatzResearch.WordTrace tailWord_924647 prefixEnd_924647 140678028663096014240039 := by
  unfold tailWord_924647
  simp only [CollatzResearch.WordTrace]
  refine ⟨33724646681169310980284195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22483097787446207320189463 33724646681169310980284195)
  ·
    refine ⟨50586970021753966470426293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33724646681169310980284195 50586970021753966470426293)
    ·
      refine ⟨4742528439539434356602465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50586970021753966470426293 4742528439539434356602465)
      ·
        refine ⟨3556896329654575767451849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4742528439539434356602465 3556896329654575767451849)
        ·
          refine ⟨2667672247240931825588887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3556896329654575767451849 2667672247240931825588887)
          ·
            refine ⟨4001508370861397738383331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667672247240931825588887 4001508370861397738383331)
            ·
              refine ⟨6002262556292096607574997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001508370861397738383331 6002262556292096607574997)
              ·
                refine ⟨140678028663096014240039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6002262556292096607574997 140678028663096014240039)
                ·
                  rfl

theorem cell20_924647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 7].length) (baseStart_924647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924647 prefixEnd_924647 := by exact prefixLift 924647
  have htrace : WordTrace (prefixWord ++ tailWord_924647) baseStart_924647 baseEnd_924647 := by
    simpa [prefixWord, tailWord_924647, baseEnd_924647] using wordTrace_append hprefix tailTrace_924647
  have hstable : (prefixWord ++ tailWord_924647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924647).length < 2 ^ (prefixWord ++ tailWord_924647).sum := by decide
  have hdescent : baseEnd_924647 < baseStart_924647 := by decide
  rcases family_descends (prefixWord ++ tailWord_924647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924650 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_924650 : Nat := 118140960795 + 924650 * 2 ^ 59
def prefixEnd_924650 : Nat := 4983230072969 + 3 ^ 40 * 924650 * 2
def baseEnd_924650 : Nat := 422035455271033365620105

theorem tailTrace_924650 : CollatzResearch.WordTrace tailWord_924650 prefixEnd_924650 422035455271033365620105 := by
  unfold tailWord_924650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8431189025039610623160851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22483170733438961661762269 8431189025039610623160851)
  ·
    refine ⟨12646783537559415934741277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8431189025039610623160851 12646783537559415934741277)
    ·
      refine ⟨4742543826584780975527979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12646783537559415934741277 4742543826584780975527979)
      ·
        refine ⟨7113815739877171463291969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4742543826584780975527979 7113815739877171463291969)
        ·
          refine ⟨5335361804907878597468977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7113815739877171463291969 5335361804907878597468977)
          ·
            refine ⟨4001521353680908948101733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5335361804907878597468977 4001521353680908948101733)
            ·
              refine ⟨750285253815170427769075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4001521353680908948101733 750285253815170427769075)
              ·
                refine ⟨1125427880722755641653613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750285253815170427769075 1125427880722755641653613)
                ·
                  refine ⟨422035455271033365620105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125427880722755641653613 422035455271033365620105)
                  ·
                    rfl

theorem cell20_924650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_924650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924650 prefixEnd_924650 := by exact prefixLift 924650
  have htrace : WordTrace (prefixWord ++ tailWord_924650) baseStart_924650 baseEnd_924650 := by
    simpa [prefixWord, tailWord_924650, baseEnd_924650] using wordTrace_append hprefix tailTrace_924650
  have hstable : (prefixWord ++ tailWord_924650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924650).length < 2 ^ (prefixWord ++ tailWord_924650).sum := by decide
  have hdescent : baseEnd_924650 < baseStart_924650 := by decide
  rcases family_descends (prefixWord ++ tailWord_924650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924733 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 2]
def baseStart_924733 : Nat := 118140960795 + 924733 * 2 ^ 59
def prefixEnd_924733 : Nat := 4983230072969 + 3 ^ 40 * 924733 * 2
def baseEnd_924733 : Nat := 422073338732653965853099

theorem tailTrace_924733 : CollatzResearch.WordTrace tailWord_924733 prefixEnd_924733 422073338732653965853099 := by
  unfold tailWord_924733
  simp only [CollatzResearch.WordTrace]
  refine ⟨33727783358857747667914853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22485188905905165111943235 33727783358857747667914853)
  ·
    refine ⟨6323959379785827687734035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33727783358857747667914853 6323959379785827687734035)
    ·
      refine ⟨9485939069678741531601053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323959379785827687734035 9485939069678741531601053)
      ·
        refine ⟨3557227151129528074350395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9485939069678741531601053 3557227151129528074350395)
        ·
          refine ⟨5335840726694292111525593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557227151129528074350395 5335840726694292111525593)
          ·
            refine ⟨4001880545020719083644195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5335840726694292111525593 4001880545020719083644195)
            ·
              refine ⟨6002820817531078625466293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001880545020719083644195 6002820817531078625466293)
              ·
                refine ⟨562764451643538621137465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6002820817531078625466293 562764451643538621137465)
                ·
                  refine ⟨422073338732653965853099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562764451643538621137465 422073338732653965853099)
                  ·
                    rfl

theorem cell20_924733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_924733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924733 prefixEnd_924733 := by exact prefixLift 924733
  have htrace : WordTrace (prefixWord ++ tailWord_924733) baseStart_924733 baseEnd_924733 := by
    simpa [prefixWord, tailWord_924733, baseEnd_924733] using wordTrace_append hprefix tailTrace_924733
  have hstable : (prefixWord ++ tailWord_924733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924733).length < 2 ^ (prefixWord ++ tailWord_924733).sum := by decide
  have hdescent : baseEnd_924733 < baseStart_924733 := by decide
  rcases family_descends (prefixWord ++ tailWord_924733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924744 : List Nat := [2, 1, 3, 1, 1, 1, 11]
def baseStart_924744 : Nat := 118140960795 + 924744 * 2 ^ 59
def prefixEnd_924744 : Nat := 4983230072969 + 3 ^ 40 * 924744 * 2
def baseEnd_924744 : Nat := 46897595492487424054043

theorem tailTrace_924744 : CollatzResearch.WordTrace tailWord_924744 prefixEnd_924744 46897595492487424054043 := by
  unfold tailWord_924744
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864092280908948273282643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22485456374545264364376857 16864092280908948273282643)
  ·
    refine ⟨25296138421363422409923965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16864092280908948273282643 25296138421363422409923965)
    ·
      refine ⟨9486051908011283403721487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25296138421363422409923965 9486051908011283403721487)
      ·
        refine ⟨14229077862016925105582231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486051908011283403721487 14229077862016925105582231)
        ·
          refine ⟨21343616793025387658373347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229077862016925105582231 21343616793025387658373347)
          ·
            refine ⟨32015425189538081487560021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21343616793025387658373347 32015425189538081487560021)
            ·
              refine ⟨46897595492487424054043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32015425189538081487560021 46897595492487424054043)
              ·
                rfl

theorem cell20_924744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 11].length) (baseStart_924744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924744 prefixEnd_924744 := by exact prefixLift 924744
  have htrace : WordTrace (prefixWord ++ tailWord_924744) baseStart_924744 baseEnd_924744 := by
    simpa [prefixWord, tailWord_924744, baseEnd_924744] using wordTrace_append hprefix tailTrace_924744
  have hstable : (prefixWord ++ tailWord_924744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924744).length < 2 ^ (prefixWord ++ tailWord_924744).sum := by decide
  have hdescent : baseEnd_924744 < baseStart_924744 := by decide
  rcases family_descends (prefixWord ++ tailWord_924744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924754 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 4]
def baseStart_924754 : Nat := 118140960795 + 924754 * 2 ^ 59
def prefixEnd_924754 : Nat := 4983230072969 + 3 ^ 40 * 924754 * 2
def baseEnd_924754 : Nat := 422082923704871226153013

theorem tailTrace_924754 : CollatzResearch.WordTrace tailWord_924754 prefixEnd_924754 422082923704871226153013 := by
  unfold tailWord_924754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432137322945417063607329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22485699527854445502952877 8432137322945417063607329)
  ·
    refine ⟨6324102992209062797705497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8432137322945417063607329 6324102992209062797705497)
    ·
      refine ⟨4743077244156797098279123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6324102992209062797705497 4743077244156797098279123)
      ·
        refine ⟨7114615866235195647418685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743077244156797098279123 7114615866235195647418685)
        ·
          refine ⟨2667980949838198367782007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7114615866235195647418685 2667980949838198367782007)
          ·
            refine ⟨4001971424757297551673011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667980949838198367782007 4001971424757297551673011)
            ·
              refine ⟨6002957137135946327509517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4001971424757297551673011 6002957137135946327509517)
              ·
                refine ⟨2251108926425979872816069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6002957137135946327509517 2251108926425979872816069)
                ·
                  refine ⟨422082923704871226153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251108926425979872816069 422082923704871226153013)
                  ·
                    rfl

theorem cell20_924754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_924754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924754 prefixEnd_924754 := by exact prefixLift 924754
  have htrace : WordTrace (prefixWord ++ tailWord_924754) baseStart_924754 baseEnd_924754 := by
    simpa [prefixWord, tailWord_924754, baseEnd_924754] using wordTrace_append hprefix tailTrace_924754
  have hstable : (prefixWord ++ tailWord_924754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924754).length < 2 ^ (prefixWord ++ tailWord_924754).sum := by decide
  have hdescent : baseEnd_924754 < baseStart_924754 := by decide
  rcases family_descends (prefixWord ++ tailWord_924754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924764 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_924764 : Nat := 118140960795 + 924764 * 2 ^ 59
def prefixEnd_924764 : Nat := 4983230072969 + 3 ^ 40 * 924764 * 2
def baseEnd_924764 : Nat := 422087487977355635819639

theorem tailTrace_924764 : CollatzResearch.WordTrace tailWord_924764 prefixEnd_924764 422087487977355635819639 := by
  unfold tailWord_924764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16864457010872719981146673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22485942681163626641528897 16864457010872719981146673)
  ·
    refine ⟨12648342758154539985860005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16864457010872719981146673 12648342758154539985860005)
    ·
      refine ⟨2371564267153976247348751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12648342758154539985860005 2371564267153976247348751)
      ·
        refine ⟨3557346400730964371023127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371564267153976247348751 3557346400730964371023127)
        ·
          refine ⟨5336019601096446556534691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557346400730964371023127 5336019601096446556534691)
          ·
            refine ⟨8004029401644669834802037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5336019601096446556534691 8004029401644669834802037)
            ·
              refine ⟨750377756404187797012691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8004029401644669834802037 750377756404187797012691)
              ·
                refine ⟨1125566634606281695519037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750377756404187797012691 1125566634606281695519037)
                ·
                  refine ⟨422087487977355635819639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125566634606281695519037 422087487977355635819639)
                  ·
                    rfl

theorem cell20_924764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_924764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924764 prefixEnd_924764 := by exact prefixLift 924764
  have htrace : WordTrace (prefixWord ++ tailWord_924764) baseStart_924764 baseEnd_924764 := by
    simpa [prefixWord, tailWord_924764, baseEnd_924764] using wordTrace_append hprefix tailTrace_924764
  have hstable : (prefixWord ++ tailWord_924764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924764).length < 2 ^ (prefixWord ++ tailWord_924764).sum := by decide
  have hdescent : baseEnd_924764 < baseStart_924764 := by decide
  rcases family_descends (prefixWord ++ tailWord_924764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924778 : List Nat := [3, 1, 3, 2, 2, 1, 4, 4]
def baseStart_924778 : Nat := 118140960795 + 924778 * 2 ^ 59
def prefixEnd_924778 : Nat := 4983230072969 + 3 ^ 40 * 924778 * 2
def baseEnd_924778 : Nat := 140697959319611269784305

theorem tailTrace_924778 : CollatzResearch.WordTrace tailWord_924778 prefixEnd_924778 140697959319611269784305 := by
  unfold tailWord_924778
  simp only [CollatzResearch.WordTrace]
  refine ⟨8432356160923680088325747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22486283095796480235535325 8432356160923680088325747)
  ·
    refine ⟨12648534241385520132488621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8432356160923680088325747 12648534241385520132488621)
    ·
      refine ⟨4743200340519570049683233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12648534241385520132488621 4743200340519570049683233)
      ·
        refine ⟨3557400255389677537262425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4743200340519570049683233 3557400255389677537262425)
        ·
          refine ⟨2668050191542258152946819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557400255389677537262425 2668050191542258152946819)
          ·
            refine ⟨4002075287313387229420229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668050191542258152946819 4002075287313387229420229)
            ·
              refine ⟨750389116371260105516293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4002075287313387229420229 750389116371260105516293)
              ·
                refine ⟨140697959319611269784305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 750389116371260105516293 140697959319611269784305)
                ·
                  rfl

theorem cell20_924778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_924778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924778 prefixEnd_924778 := by exact prefixLift 924778
  have htrace : WordTrace (prefixWord ++ tailWord_924778) baseStart_924778 baseEnd_924778 := by
    simpa [prefixWord, tailWord_924778, baseEnd_924778] using wordTrace_append hprefix tailTrace_924778
  have hstable : (prefixWord ++ tailWord_924778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924778).length < 2 ^ (prefixWord ++ tailWord_924778).sum := by decide
  have hdescent : baseEnd_924778 < baseStart_924778 := by decide
  rcases family_descends (prefixWord ++ tailWord_924778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924823 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_924823 : Nat := 118140960795 + 924823 * 2 ^ 59
def prefixEnd_924823 : Nat := 4983230072969 + 3 ^ 40 * 924823 * 2
def baseEnd_924823 : Nat := 422114417185013652852731

theorem tailTrace_924823 : CollatzResearch.WordTrace tailWord_924823 prefixEnd_924823 422114417185013652852731 := by
  unfold tailWord_924823
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731065928531693038691123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22487377285687795359127415 33731065928531693038691123)
  ·
    refine ⟨50596598892797539558036685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731065928531693038691123 50596598892797539558036685)
    ·
      refine ⟨18973724584799077334263757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50596598892797539558036685 18973724584799077334263757)
      ·
        refine ⟨7115146719299654000348909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18973724584799077334263757 7115146719299654000348909)
        ·
          refine ⟨2668180019737370250130841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7115146719299654000348909 2668180019737370250130841)
          ·
            refine ⟨2001135014803027687598131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668180019737370250130841 2001135014803027687598131)
            ·
              refine ⟨3001702522204541531397197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001135014803027687598131 3001702522204541531397197)
              ·
                refine ⟨1125638445826703074273949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3001702522204541531397197 1125638445826703074273949)
                ·
                  refine ⟨422114417185013652852731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125638445826703074273949 422114417185013652852731)
                  ·
                    rfl

theorem cell20_924823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_924823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924823 prefixEnd_924823 := by exact prefixLift 924823
  have htrace : WordTrace (prefixWord ++ tailWord_924823) baseStart_924823 baseEnd_924823 := by
    simpa [prefixWord, tailWord_924823, baseEnd_924823] using wordTrace_append hprefix tailTrace_924823
  have hstable : (prefixWord ++ tailWord_924823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924823).length < 2 ^ (prefixWord ++ tailWord_924823).sum := by decide
  have hdescent : baseEnd_924823 < baseStart_924823 := by decide
  rcases family_descends (prefixWord ++ tailWord_924823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924827 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 9]
def baseStart_924827 : Nat := 118140960795 + 924827 * 2 ^ 59
def prefixEnd_924827 : Nat := 4983230072969 + 3 ^ 40 * 924827 * 2
def baseEnd_924827 : Nat := 422116242894007416719381

theorem tailTrace_924827 : CollatzResearch.WordTrace tailWord_924827 prefixEnd_924827 422116242894007416719381 := by
  unfold tailWord_924827
  simp only [CollatzResearch.WordTrace]
  refine ⟨33731211820517201721836735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22487474547011467814557823 33731211820517201721836735)
  ·
    refine ⟨50596817730775802582755103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33731211820517201721836735 50596817730775802582755103)
    ·
      refine ⟨75895226596163703874132655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50596817730775802582755103 75895226596163703874132655)
      ·
        refine ⟨113842839894245555811198983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75895226596163703874132655 113842839894245555811198983)
        ·
          refine ⟨170764259841368333716798475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113842839894245555811198983 170764259841368333716798475)
          ·
            refine ⟨256146389762052500575197713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170764259841368333716798475 256146389762052500575197713)
            ·
              refine ⟨192109792321539375431398285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256146389762052500575197713 192109792321539375431398285)
              ·
                refine ⟨72041172120577265786774357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192109792321539375431398285 72041172120577265786774357)
                ·
                  refine ⟨422116242894007416719381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72041172120577265786774357 422116242894007416719381)
                  ·
                    rfl

theorem cell20_924827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 9].length) (baseStart_924827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924827 prefixEnd_924827 := by exact prefixLift 924827
  have htrace : WordTrace (prefixWord ++ tailWord_924827) baseStart_924827 baseEnd_924827 := by
    simpa [prefixWord, tailWord_924827, baseEnd_924827] using wordTrace_append hprefix tailTrace_924827
  have hstable : (prefixWord ++ tailWord_924827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924827).length < 2 ^ (prefixWord ++ tailWord_924827).sum := by decide
  have hdescent : baseEnd_924827 < baseStart_924827 := by decide
  rcases family_descends (prefixWord ++ tailWord_924827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924854 : List Nat := [5, 1, 3, 2, 9]
def baseStart_924854 : Nat := 118140960795 + 924854 * 2 ^ 59
def prefixEnd_924854 : Nat := 4983230072969 + 3 ^ 40 * 924854 * 2
def baseEnd_924854 : Nat := 5211463783082905219991

theorem tailTrace_924854 : CollatzResearch.WordTrace tailWord_924854 prefixEnd_924854 5211463783082905219991 := by
  unfold tailWord_924854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108262286963711583316851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22488131060946256888713077 2108262286963711583316851)
  ·
    refine ⟨3162393430445567374975277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108262286963711583316851 3162393430445567374975277)
    ·
      refine ⟨1185897536417087765615729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3162393430445567374975277 1185897536417087765615729)
      ·
        refine ⟨889423152312815824211797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185897536417087765615729 889423152312815824211797)
        ·
          refine ⟨5211463783082905219991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 889423152312815824211797 5211463783082905219991)
          ·
            rfl

theorem cell20_924854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 9].length) (baseStart_924854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924854 prefixEnd_924854 := by exact prefixLift 924854
  have htrace : WordTrace (prefixWord ++ tailWord_924854) baseStart_924854 baseEnd_924854 := by
    simpa [prefixWord, tailWord_924854, baseEnd_924854] using wordTrace_append hprefix tailTrace_924854
  have hstable : (prefixWord ++ tailWord_924854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924854).length < 2 ^ (prefixWord ++ tailWord_924854).sum := by decide
  have hdescent : baseEnd_924854 < baseStart_924854 := by decide
  rcases family_descends (prefixWord ++ tailWord_924854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924927 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 4]
def baseStart_924927 : Nat := 118140960795 + 924927 * 2 ^ 59
def prefixEnd_924927 : Nat := 4983230072969 + 3 ^ 40 * 924927 * 2
def baseEnd_924927 : Nat := 422161885618851513385639

theorem tailTrace_924927 : CollatzResearch.WordTrace tailWord_924927 prefixEnd_924927 422161885618851513385639 := by
  unfold tailWord_924927
  simp only [CollatzResearch.WordTrace]
  refine ⟨33734859120154918800477035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22489906080103279200318023 33734859120154918800477035)
  ·
    refine ⟨50602288680232378200715553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33734859120154918800477035 50602288680232378200715553)
    ·
      refine ⟨37951716510174283650536665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50602288680232378200715553 37951716510174283650536665)
      ·
        refine ⟨28463787382630712737902499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37951716510174283650536665 28463787382630712737902499)
        ·
          refine ⟨42695681073946069106853749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28463787382630712737902499 42695681073946069106853749)
          ·
            refine ⟨4002720100682443978767539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42695681073946069106853749 4002720100682443978767539)
            ·
              refine ⟨6004080151023665968151309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002720100682443978767539 6004080151023665968151309)
              ·
                refine ⟨2251530056633874738056741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6004080151023665968151309 2251530056633874738056741)
                ·
                  refine ⟨422161885618851513385639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251530056633874738056741 422161885618851513385639)
                  ·
                    rfl

theorem cell20_924927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 4].length) (baseStart_924927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924927 prefixEnd_924927 := by exact prefixLift 924927
  have htrace : WordTrace (prefixWord ++ tailWord_924927) baseStart_924927 baseEnd_924927 := by
    simpa [prefixWord, tailWord_924927, baseEnd_924927] using wordTrace_append hprefix tailTrace_924927
  have hstable : (prefixWord ++ tailWord_924927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924927).length < 2 ^ (prefixWord ++ tailWord_924927).sum := by decide
  have hdescent : baseEnd_924927 < baseStart_924927 := by decide
  rcases family_descends (prefixWord ++ tailWord_924927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924937 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_924937 : Nat := 118140960795 + 924937 * 2 ^ 59
def prefixEnd_924937 : Nat := 4983230072969 + 3 ^ 40 * 924937 * 2
def baseEnd_924937 : Nat := 422166449891335923052265

theorem tailTrace_924937 : CollatzResearch.WordTrace tailWord_924937 prefixEnd_924937 422166449891335923052265 := by
  unfold tailWord_924937
  simp only [CollatzResearch.WordTrace]
  refine ⟨33735223850118690508341065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22490149233412460338894043 33735223850118690508341065)
  ·
    refine ⟨25301417887589017881255799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33735223850118690508341065 25301417887589017881255799)
    ·
      refine ⟨37952126831383526821883699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25301417887589017881255799 37952126831383526821883699)
      ·
        refine ⟨56928190247075290232825549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37952126831383526821883699 56928190247075290232825549)
        ·
          refine ⟨21348071342653233837309581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56928190247075290232825549 21348071342653233837309581)
          ·
            refine ⟨8005526753494962688991093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21348071342653233837309581 8005526753494962688991093)
            ·
              refine ⟨750518133140152752092915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8005526753494962688991093 750518133140152752092915)
              ·
                refine ⟨1125777199710229128139373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750518133140152752092915 1125777199710229128139373)
                ·
                  refine ⟨422166449891335923052265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1125777199710229128139373 422166449891335923052265)
                  ·
                    rfl

theorem cell20_924937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_924937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924937 prefixEnd_924937 := by exact prefixLift 924937
  have htrace : WordTrace (prefixWord ++ tailWord_924937) baseStart_924937 baseEnd_924937 := by
    simpa [prefixWord, tailWord_924937, baseEnd_924937] using wordTrace_append hprefix tailTrace_924937
  have hstable : (prefixWord ++ tailWord_924937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924937).length < 2 ^ (prefixWord ++ tailWord_924937).sum := by decide
  have hdescent : baseEnd_924937 < baseStart_924937 := by decide
  rcases family_descends (prefixWord ++ tailWord_924937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924978 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 2]
def baseStart_924978 : Nat := 118140960795 + 924978 * 2 ^ 59
def prefixEnd_924978 : Nat := 4983230072969 + 3 ^ 40 * 924978 * 2
def baseEnd_924978 : Nat := 422185163408522002685431

theorem tailTrace_924978 : CollatzResearch.WordTrace tailWord_924978 prefixEnd_924978 422185163408522002685431 := by
  unfold tailWord_924978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8434179810742538627645897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22491146161980103007055725 8434179810742538627645897)
  ·
    refine ⟨6325634858056903970734423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8434179810742538627645897 6325634858056903970734423)
    ·
      refine ⟨9488452287085355956101635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6325634858056903970734423 9488452287085355956101635)
      ·
        refine ⟨14232678430628033934152453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9488452287085355956101635 14232678430628033934152453)
        ·
          refine ⟨2668627205742756362653585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14232678430628033934152453 2668627205742756362653585)
          ·
            refine ⟨2001470404307067271990189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668627205742756362653585 2001470404307067271990189)
            ·
              refine ⟨750551401615150226996321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2001470404307067271990189 750551401615150226996321)
              ·
                refine ⟨562913551211362670247241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750551401615150226996321 562913551211362670247241)
                ·
                  refine ⟨422185163408522002685431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562913551211362670247241 422185163408522002685431)
                  ·
                    rfl

theorem cell20_924978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_924978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_924978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_924978 prefixEnd_924978 := by exact prefixLift 924978
  have htrace : WordTrace (prefixWord ++ tailWord_924978) baseStart_924978 baseEnd_924978 := by
    simpa [prefixWord, tailWord_924978, baseEnd_924978] using wordTrace_append hprefix tailTrace_924978
  have hstable : (prefixWord ++ tailWord_924978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924978).length < 2 ^ (prefixWord ++ tailWord_924978).sum := by decide
  have hdescent : baseEnd_924978 < baseStart_924978 := by decide
  rcases family_descends (prefixWord ++ tailWord_924978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925017 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 7]
def baseStart_925017 : Nat := 118140960795 + 925017 * 2 ^ 59
def prefixEnd_925017 : Nat := 4983230072969 + 3 ^ 40 * 925017 * 2
def baseEnd_925017 : Nat := 422202964071211200385271

theorem tailTrace_925017 : CollatzResearch.WordTrace tailWord_925017 prefixEnd_925017 422202964071211200385271 := by
  unfold tailWord_925017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33738141689828864171253305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22492094459885909447502203 33738141689828864171253305)
  ·
    refine ⟨25303606267371648128439979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33738141689828864171253305 25303606267371648128439979)
    ·
      refine ⟨37955409401057472192659969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25303606267371648128439979 37955409401057472192659969)
      ·
        refine ⟨28466557050793104144494977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37955409401057472192659969 28466557050793104144494977)
        ·
          refine ⟨21349917788094828108371233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28466557050793104144494977 21349917788094828108371233)
          ·
            refine ⟨16012438341071121081278425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21349917788094828108371233 16012438341071121081278425)
            ·
              refine ⟨12009328755803340810958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16012438341071121081278425 12009328755803340810958819)
              ·
                refine ⟨18013993133705011216438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12009328755803340810958819 18013993133705011216438229)
                ·
                  refine ⟨422202964071211200385271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18013993133705011216438229 422202964071211200385271)
                  ·
                    rfl

theorem cell20_925017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_925017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925017 prefixEnd_925017 := by exact prefixLift 925017
  have htrace : WordTrace (prefixWord ++ tailWord_925017) baseStart_925017 baseEnd_925017 := by
    simpa [prefixWord, tailWord_925017, baseEnd_925017] using wordTrace_append hprefix tailTrace_925017
  have hstable : (prefixWord ++ tailWord_925017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925017).length < 2 ^ (prefixWord ++ tailWord_925017).sum := by decide
  have hdescent : baseEnd_925017 < baseStart_925017 := by decide
  rcases family_descends (prefixWord ++ tailWord_925017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925037 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 2]
def baseStart_925037 : Nat := 118140960795 + 925037 * 2 ^ 59
def prefixEnd_925037 : Nat := 4983230072969 + 3 ^ 40 * 925037 * 2
def baseEnd_925037 : Nat := 422212092616180019718523

theorem tailTrace_925037 : CollatzResearch.WordTrace tailWord_925037 prefixEnd_925037 422212092616180019718523 := by
  unfold tailWord_925037
  simp only [CollatzResearch.WordTrace]
  refine ⟨33738871149756407586981365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22492580766504271724654243 33738871149756407586981365)
  ·
    refine ⟨3163019170289663211279503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33738871149756407586981365 3163019170289663211279503)
    ·
      refine ⟨4744528755434494816919255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163019170289663211279503 4744528755434494816919255)
      ·
        refine ⟨7116793133151742225378883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4744528755434494816919255 7116793133151742225378883)
        ·
          refine ⟨10675189699727613338068325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116793133151742225378883 10675189699727613338068325)
          ·
            refine ⟨2001598068698927500887811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10675189699727613338068325 2001598068698927500887811)
            ·
              refine ⟨3002397103048391251331717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001598068698927500887811 3002397103048391251331717)
              ·
                refine ⟨562949456821573359624697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3002397103048391251331717 562949456821573359624697)
                ·
                  refine ⟨422212092616180019718523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 562949456821573359624697 422212092616180019718523)
                  ·
                    rfl

theorem cell20_925037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 2].length) (baseStart_925037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925037 prefixEnd_925037 := by exact prefixLift 925037
  have htrace : WordTrace (prefixWord ++ tailWord_925037) baseStart_925037 baseEnd_925037 := by
    simpa [prefixWord, tailWord_925037, baseEnd_925037] using wordTrace_append hprefix tailTrace_925037
  have hstable : (prefixWord ++ tailWord_925037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925037).length < 2 ^ (prefixWord ++ tailWord_925037).sum := by decide
  have hdescent : baseEnd_925037 < baseStart_925037 := by decide
  rcases family_descends (prefixWord ++ tailWord_925037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925054 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_925054 : Nat := 118140960795 + 925054 * 2 ^ 59
def prefixEnd_925054 : Nat := 4983230072969 + 3 ^ 40 * 925054 * 2
def baseEnd_925054 : Nat := 422219851879403516151787

theorem tailTrace_925054 : CollatzResearch.WordTrace tailWord_925054 prefixEnd_925054 422219851879403516151787 := by
  unfold tailWord_925054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217436398836852436293777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22492994127129879660233477 4217436398836852436293777)
  ·
    refine ⟨3163077299127639327220333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4217436398836852436293777 3163077299127639327220333)
    ·
      refine ⟨1186153987172864747707625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3163077299127639327220333 1186153987172864747707625)
      ·
        refine ⟨889615490379648560780719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1186153987172864747707625 889615490379648560780719)
        ·
          refine ⟨1334423235569472841171079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889615490379648560780719 1334423235569472841171079)
          ·
            refine ⟨2001634853354209261756619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334423235569472841171079 2001634853354209261756619)
            ·
              refine ⟨3002452280031313892634929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001634853354209261756619 3002452280031313892634929)
              ·
                refine ⟨2251839210023485419476197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002452280031313892634929 2251839210023485419476197)
                ·
                  refine ⟨422219851879403516151787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251839210023485419476197 422219851879403516151787)
                  ·
                    rfl

theorem cell20_925054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_925054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925054 prefixEnd_925054 := by exact prefixLift 925054
  have htrace : WordTrace (prefixWord ++ tailWord_925054) baseStart_925054 baseEnd_925054 := by
    simpa [prefixWord, tailWord_925054, baseEnd_925054] using wordTrace_append hprefix tailTrace_925054
  have hstable : (prefixWord ++ tailWord_925054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925054).length < 2 ^ (prefixWord ++ tailWord_925054).sum := by decide
  have hdescent : baseEnd_925054 < baseStart_925054 := by decide
  rcases family_descends (prefixWord ++ tailWord_925054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925117 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_925117 : Nat := 118140960795 + 925117 * 2 ^ 59
def prefixEnd_925117 : Nat := 4983230072969 + 3 ^ 40 * 925117 * 2
def baseEnd_925117 : Nat := 422248606796055297051529

theorem tailTrace_925117 : CollatzResearch.WordTrace tailWord_925117 prefixEnd_925117 422248606796055297051529 := by
  unfold tailWord_925117
  simp only [CollatzResearch.WordTrace]
  refine ⟨33741788989466581249893605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22494525992977720833262403 33741788989466581249893605)
  ·
    refine ⟨6326585435524983984355051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33741788989466581249893605 6326585435524983984355051)
    ·
      refine ⟨9489878153287475976532577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326585435524983984355051 9489878153287475976532577)
      ·
        refine ⟨7117408614965606982399433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9489878153287475976532577 7117408614965606982399433)
        ·
          refine ⟨5338056461224205236799575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7117408614965606982399433 5338056461224205236799575)
          ·
            refine ⟨8007084691836307855199363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338056461224205236799575 8007084691836307855199363)
            ·
              refine ⟨12010627037754461782799045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007084691836307855199363 12010627037754461782799045)
              ·
                refine ⟨2251992569578961584274821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12010627037754461782799045 2251992569578961584274821)
                ·
                  refine ⟨422248606796055297051529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2251992569578961584274821 422248606796055297051529)
                  ·
                    rfl

theorem cell20_925117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_925117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925117 prefixEnd_925117 := by exact prefixLift 925117
  have htrace : WordTrace (prefixWord ++ tailWord_925117) baseStart_925117 baseEnd_925117 := by
    simpa [prefixWord, tailWord_925117, baseEnd_925117] using wordTrace_append hprefix tailTrace_925117
  have hstable : (prefixWord ++ tailWord_925117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925117).length < 2 ^ (prefixWord ++ tailWord_925117).sum := by decide
  have hdescent : baseEnd_925117 < baseStart_925117 := by decide
  rcases family_descends (prefixWord ++ tailWord_925117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925122 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 2]
def baseStart_925122 : Nat := 118140960795 + 925122 * 2 ^ 59
def prefixEnd_925122 : Nat := 4983230072969 + 3 ^ 40 * 925122 * 2
def baseEnd_925122 : Nat := 422250888932297501884843

theorem tailTrace_925122 : CollatzResearch.WordTrace tailWord_925122 prefixEnd_925122 422250888932297501884843 := by
  unfold tailWord_925122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435492838612116775956405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22494647569632311402550413 8435492838612116775956405)
  ·
    refine ⟨790827453619885947745913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8435492838612116775956405 790827453619885947745913)
    ·
      refine ⟨593120590214914460809435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 790827453619885947745913 593120590214914460809435)
      ·
        refine ⟨889680885322371691214153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593120590214914460809435 889680885322371691214153)
        ·
          refine ⟨667260663991778768410615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889680885322371691214153 667260663991778768410615)
          ·
            refine ⟨1000890995987668152615923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667260663991778768410615 1000890995987668152615923)
            ·
              refine ⟨1501336493981502228923885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000890995987668152615923 1501336493981502228923885)
              ·
                refine ⟨563001185243063335846457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501336493981502228923885 563001185243063335846457)
                ·
                  refine ⟨422250888932297501884843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563001185243063335846457 422250888932297501884843)
                  ·
                    rfl

theorem cell20_925122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_925122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925122 prefixEnd_925122 := by exact prefixLift 925122
  have htrace : WordTrace (prefixWord ++ tailWord_925122) baseStart_925122 baseEnd_925122 := by
    simpa [prefixWord, tailWord_925122, baseEnd_925122] using wordTrace_append hprefix tailTrace_925122
  have hstable : (prefixWord ++ tailWord_925122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925122).length < 2 ^ (prefixWord ++ tailWord_925122).sum := by decide
  have hdescent : baseEnd_925122 < baseStart_925122 := by decide
  rcases family_descends (prefixWord ++ tailWord_925122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925131 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 5]
def baseStart_925131 : Nat := 118140960795 + 925131 * 2 ^ 59
def prefixEnd_925131 : Nat := 4983230072969 + 3 ^ 40 * 925131 * 2
def baseEnd_925131 : Nat := 422254996777533470584805

theorem tailTrace_925131 : CollatzResearch.WordTrace tailWord_925131 prefixEnd_925131 422254996777533470584805 := by
  unfold tailWord_925131
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742299611415861640903247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22494866407610574427268831 33742299611415861640903247)
  ·
    refine ⟨50613449417123792461354871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33742299611415861640903247 50613449417123792461354871)
    ·
      refine ⟨75920174125685688692032307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50613449417123792461354871 75920174125685688692032307)
      ·
        refine ⟨113880261188528533038048461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75920174125685688692032307 113880261188528533038048461)
        ·
          refine ⟨42705097945698199889268173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113880261188528533038048461 42705097945698199889268173)
          ·
            refine ⟨16014411729636824958475565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42705097945698199889268173 16014411729636824958475565)
            ·
              refine ⟨6005404398613809359428337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16014411729636824958475565 6005404398613809359428337)
              ·
                refine ⟨4504053298960357019571253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005404398613809359428337 4504053298960357019571253)
                ·
                  refine ⟨422254996777533470584805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504053298960357019571253 422254996777533470584805)
                  ·
                    rfl

theorem cell20_925131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_925131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925131 prefixEnd_925131 := by exact prefixLift 925131
  have htrace : WordTrace (prefixWord ++ tailWord_925131) baseStart_925131 baseEnd_925131 := by
    simpa [prefixWord, tailWord_925131, baseEnd_925131] using wordTrace_append hprefix tailTrace_925131
  have hstable : (prefixWord ++ tailWord_925131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925131).length < 2 ^ (prefixWord ++ tailWord_925131).sum := by decide
  have hdescent : baseEnd_925131 < baseStart_925131 := by decide
  rcases family_descends (prefixWord ++ tailWord_925131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925151 : List Nat := [1, 1, 2, 3, 3, 1, 5, 2, 2]
def baseStart_925151 : Nat := 118140960795 + 925151 * 2 ^ 59
def prefixEnd_925151 : Nat := 4983230072969 + 3 ^ 40 * 925151 * 2
def baseEnd_925151 : Nat := 422264125322502289918057

theorem tailTrace_925151 : CollatzResearch.WordTrace tailWord_925151 prefixEnd_925151 422264125322502289918057 := by
  unfold tailWord_925151
  simp only [CollatzResearch.WordTrace]
  refine ⟨33743029071343405056631307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22495352714228936704420871 33743029071343405056631307)
  ·
    refine ⟨50614543607015107584946961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33743029071343405056631307 50614543607015107584946961)
    ·
      refine ⟨37960907705261330688710221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50614543607015107584946961 37960907705261330688710221)
      ·
        refine ⟨14235340389472999008266333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37960907705261330688710221 14235340389472999008266333)
        ·
          refine ⟨5338252646052374628099875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14235340389472999008266333 5338252646052374628099875)
          ·
            refine ⟨8007378969078561942149813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338252646052374628099875 8007378969078561942149813)
            ·
              refine ⟨750691778351115182076545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8007378969078561942149813 750691778351115182076545)
              ·
                refine ⟨563018833763336386557409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750691778351115182076545 563018833763336386557409)
                ·
                  refine ⟨422264125322502289918057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563018833763336386557409 422264125322502289918057)
                  ·
                    rfl

theorem cell20_925151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 2].length) (baseStart_925151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925151 prefixEnd_925151 := by exact prefixLift 925151
  have htrace : WordTrace (prefixWord ++ tailWord_925151) baseStart_925151 baseEnd_925151 := by
    simpa [prefixWord, tailWord_925151, baseEnd_925151] using wordTrace_append hprefix tailTrace_925151
  have hstable : (prefixWord ++ tailWord_925151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925151).length < 2 ^ (prefixWord ++ tailWord_925151).sum := by decide
  have hdescent : baseEnd_925151 < baseStart_925151 := by decide
  rcases family_descends (prefixWord ++ tailWord_925151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925217 : List Nat := [1, 2, 3, 2, 2, 4, 1, 5]
def baseStart_925217 : Nat := 118140960795 + 925217 * 2 ^ 59
def prefixEnd_925217 : Nat := 4983230072969 + 3 ^ 40 * 925217 * 2
def baseEnd_925217 : Nat := 140764749840299797905929

theorem tailTrace_925217 : CollatzResearch.WordTrace tailWord_925217 prefixEnd_925217 140764749840299797905929 := by
  unfold tailWord_925217
  simp only [CollatzResearch.WordTrace]
  refine ⟨33745436289104298328533905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22496957526069532219022603 33745436289104298328533905)
  ·
    refine ⟨25309077216828223746400429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33745436289104298328533905 25309077216828223746400429)
    ·
      refine ⟨9490903956310583904900161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25309077216828223746400429 9490903956310583904900161)
      ·
        refine ⟨7118177967232937928675121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9490903956310583904900161 7118177967232937928675121)
        ·
          refine ⟨5338633475424703446506341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7118177967232937928675121 5338633475424703446506341)
          ·
            refine ⟨1000993776642131896219939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5338633475424703446506341 1000993776642131896219939)
            ·
              refine ⟨1501490664963197844329909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000993776642131896219939 1501490664963197844329909)
              ·
                refine ⟨140764749840299797905929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1501490664963197844329909 140764749840299797905929)
                ·
                  rfl

theorem cell20_925217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 5].length) (baseStart_925217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925217 prefixEnd_925217 := by exact prefixLift 925217
  have htrace : WordTrace (prefixWord ++ tailWord_925217) baseStart_925217 baseEnd_925217 := by
    simpa [prefixWord, tailWord_925217, baseEnd_925217] using wordTrace_append hprefix tailTrace_925217
  have hstable : (prefixWord ++ tailWord_925217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925217).length < 2 ^ (prefixWord ++ tailWord_925217).sum := by decide
  have hdescent : baseEnd_925217 < baseStart_925217 := by decide
  rcases family_descends (prefixWord ++ tailWord_925217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925254 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_925254 : Nat := 118140960795 + 925254 * 2 ^ 59
def prefixEnd_925254 : Nat := 4983230072969 + 3 ^ 40 * 925254 * 2
def baseEnd_925254 : Nat := 422311137329091709484303

theorem tailTrace_925254 : CollatzResearch.WordTrace tailWord_925254 prefixEnd_925254 422311137329091709484303 := by
  unfold tailWord_925254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054587055936570426488463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22497857193313502431753877 1054587055936570426488463)
  ·
    refine ⟨1581880583904855639732695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054587055936570426488463 1581880583904855639732695)
    ·
      refine ⟨2372820875857283459599043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581880583904855639732695 2372820875857283459599043)
      ·
        refine ⟨3559231313785925189398565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372820875857283459599043 3559231313785925189398565)
        ·
          refine ⟨667355871334860973012231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3559231313785925189398565 667355871334860973012231)
          ·
            refine ⟨1001033807002291459518347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667355871334860973012231 1001033807002291459518347)
            ·
              refine ⟨1501550710503437189277521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001033807002291459518347 1501550710503437189277521)
              ·
                refine ⟨1126163032877577891958141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501550710503437189277521 1126163032877577891958141)
                ·
                  refine ⟨422311137329091709484303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126163032877577891958141 422311137329091709484303)
                  ·
                    rfl

theorem cell20_925254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_925254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925254 prefixEnd_925254 := by exact prefixLift 925254
  have htrace : WordTrace (prefixWord ++ tailWord_925254) baseStart_925254 baseEnd_925254 := by
    simpa [prefixWord, tailWord_925254, baseEnd_925254] using wordTrace_append hprefix tailTrace_925254
  have hstable : (prefixWord ++ tailWord_925254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925254).length < 2 ^ (prefixWord ++ tailWord_925254).sum := by decide
  have hdescent : baseEnd_925254 < baseStart_925254 := by decide
  rcases family_descends (prefixWord ++ tailWord_925254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925293 : List Nat := [1, 5, 1, 1, 4, 1, 1, 6]
def baseStart_925293 : Nat := 118140960795 + 925293 * 2 ^ 59
def prefixEnd_925293 : Nat := 4983230072969 + 3 ^ 40 * 925293 * 2
def baseEnd_925293 : Nat := 140776312663926969061381

theorem tailTrace_925293 : CollatzResearch.WordTrace tailWord_925293 prefixEnd_925293 140776312663926969061381 := by
  unfold tailWord_925293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33748208236828963308300533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22498805491219308872200355 33748208236828963308300533)
  ·
    refine ⟨3163894522202715310153175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33748208236828963308300533 3163894522202715310153175)
    ·
      refine ⟨4745841783304072965229763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3163894522202715310153175 4745841783304072965229763)
      ·
        refine ⟨7118762674956109447844645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4745841783304072965229763 7118762674956109447844645)
        ·
          refine ⟨1334768001554270521470871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7118762674956109447844645 1334768001554270521470871)
          ·
            refine ⟨2002152002331405782206307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334768001554270521470871 2002152002331405782206307)
            ·
              refine ⟨3003228003497108673309461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002152002331405782206307 3003228003497108673309461)
              ·
                refine ⟨140776312663926969061381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3003228003497108673309461 140776312663926969061381)
                ·
                  rfl

theorem cell20_925293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 6].length) (baseStart_925293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925293 prefixEnd_925293 := by exact prefixLift 925293
  have htrace : WordTrace (prefixWord ++ tailWord_925293) baseStart_925293 baseEnd_925293 := by
    simpa [prefixWord, tailWord_925293, baseEnd_925293] using wordTrace_append hprefix tailTrace_925293
  have hstable : (prefixWord ++ tailWord_925293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925293).length < 2 ^ (prefixWord ++ tailWord_925293).sum := by decide
  have hdescent : baseEnd_925293 < baseStart_925293 := by decide
  rcases family_descends (prefixWord ++ tailWord_925293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925320 : List Nat := [2, 1, 3, 5, 2, 1, 1, 1, 4]
def baseStart_925320 : Nat := 118140960795 + 925320 * 2 ^ 59
def prefixEnd_925320 : Nat := 4983230072969 + 3 ^ 40 * 925320 * 2
def baseEnd_925320 : Nat := 422341261527488813284033

theorem tailTrace_925320 : CollatzResearch.WordTrace tailWord_925320 prefixEnd_925320 422341261527488813284033 := by
  unfold tailWord_925320
  simp only [CollatzResearch.WordTrace]
  refine ⟨16874596503865573459766707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22499462005154097946355609 16874596503865573459766707)
  ·
    refine ⟨25311894755798360189650061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16874596503865573459766707 25311894755798360189650061)
    ·
      refine ⟨9491960533424385071118773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25311894755798360189650061 9491960533424385071118773)
      ·
        refine ⟨889871300008536100417385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9491960533424385071118773 889871300008536100417385)
        ·
          refine ⟨667403475006402075313039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 889871300008536100417385 667403475006402075313039)
          ·
            refine ⟨1001105212509603112969559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667403475006402075313039 1001105212509603112969559)
            ·
              refine ⟨1501657818764404669454339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001105212509603112969559 1501657818764404669454339)
              ·
                refine ⟨2252486728146607004181509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501657818764404669454339 2252486728146607004181509)
                ·
                  refine ⟨422341261527488813284033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252486728146607004181509 422341261527488813284033)
                  ·
                    rfl

theorem cell20_925320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 2, 1, 1, 1, 4].length) (baseStart_925320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925320 prefixEnd_925320 := by exact prefixLift 925320
  have htrace : WordTrace (prefixWord ++ tailWord_925320) baseStart_925320 baseEnd_925320 := by
    simpa [prefixWord, tailWord_925320, baseEnd_925320] using wordTrace_append hprefix tailTrace_925320
  have hstable : (prefixWord ++ tailWord_925320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925320).length < 2 ^ (prefixWord ++ tailWord_925320).sum := by decide
  have hdescent : baseEnd_925320 < baseStart_925320 := by decide
  rcases family_descends (prefixWord ++ tailWord_925320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925321 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_925321 : Nat := 118140960795 + 925321 * 2 ^ 59
def prefixEnd_925321 : Nat := 4983230072969 + 3 ^ 40 * 925321 * 2
def baseEnd_925321 : Nat := 422341717954737254250695

theorem tailTrace_925321 : CollatzResearch.WordTrace tailWord_925321 prefixEnd_925321 422341717954737254250695 := by
  unfold tailWord_925321
  simp only [CollatzResearch.WordTrace]
  refine ⟨33749229480727524090319817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22499486320485016060213211 33749229480727524090319817)
  ·
    refine ⟨25311922110545643067739863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33749229480727524090319817 25311922110545643067739863)
    ·
      refine ⟨37967883165818464601609795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25311922110545643067739863 37967883165818464601609795)
      ·
        refine ⟨56951824748727696902414693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37967883165818464601609795 56951824748727696902414693)
        ·
          refine ⟨10678467140386443169202755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56951824748727696902414693 10678467140386443169202755)
          ·
            refine ⟨16017700710579664753804133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10678467140386443169202755 16017700710579664753804133)
            ·
              refine ⟨3003318883233687141338275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16017700710579664753804133 3003318883233687141338275)
              ·
                refine ⟨4504978324850530712007413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3003318883233687141338275 4504978324850530712007413)
                ·
                  refine ⟨422341717954737254250695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4504978324850530712007413 422341717954737254250695)
                  ·
                    rfl

theorem cell20_925321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_925321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925321 prefixEnd_925321 := by exact prefixLift 925321
  have htrace : WordTrace (prefixWord ++ tailWord_925321) baseStart_925321 baseEnd_925321 := by
    simpa [prefixWord, tailWord_925321, baseEnd_925321] using wordTrace_append hprefix tailTrace_925321
  have hstable : (prefixWord ++ tailWord_925321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925321).length < 2 ^ (prefixWord ++ tailWord_925321).sum := by decide
  have hdescent : baseEnd_925321 < baseStart_925321 := by decide
  rcases family_descends (prefixWord ++ tailWord_925321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925376 : List Nat := [2, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_925376 : Nat := 118140960795 + 925376 * 2 ^ 59
def prefixEnd_925376 : Nat := 4983230072969 + 3 ^ 40 * 925376 * 2
def baseEnd_925376 : Nat := 422366821453401507417137

theorem tailTrace_925376 : CollatzResearch.WordTrace tailWord_925376 prefixEnd_925376 422366821453401507417137 := by
  unfold tailWord_925376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16875617747764134241785991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22500823663685512322381321 16875617747764134241785991)
  ·
    refine ⟨25313426621646201362678987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16875617747764134241785991 25313426621646201362678987)
    ·
      refine ⟨37970139932469302044018481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25313426621646201362678987 37970139932469302044018481)
      ·
        refine ⟨28477604949351976533013861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37970139932469302044018481 28477604949351976533013861)
        ·
          refine ⟨5339550928003495599940099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28477604949351976533013861 5339550928003495599940099)
          ·
            refine ⟨8009326392005243399910149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5339550928003495599940099 8009326392005243399910149)
            ·
              refine ⟨1501748698500983137483153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8009326392005243399910149 1501748698500983137483153)
              ·
                refine ⟨1126311523875737353112365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1501748698500983137483153 1126311523875737353112365)
                ·
                  refine ⟨422366821453401507417137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126311523875737353112365 422366821453401507417137)
                  ·
                    rfl

theorem cell20_925376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_925376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925376 prefixEnd_925376 := by exact prefixLift 925376
  have htrace : WordTrace (prefixWord ++ tailWord_925376) baseStart_925376 baseEnd_925376 := by
    simpa [prefixWord, tailWord_925376, baseEnd_925376] using wordTrace_append hprefix tailTrace_925376
  have hstable : (prefixWord ++ tailWord_925376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925376).length < 2 ^ (prefixWord ++ tailWord_925376).sum := by decide
  have hdescent : baseEnd_925376 < baseStart_925376 := by decide
  rcases family_descends (prefixWord ++ tailWord_925376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925386 : List Nat := [3, 1, 2, 1, 6, 1, 1, 5]
def baseStart_925386 : Nat := 118140960795 + 925386 * 2 ^ 59
def prefixEnd_925386 : Nat := 4983230072969 + 3 ^ 40 * 925386 * 2
def baseEnd_925386 : Nat := 140790461908628639027921

theorem tailTrace_925386 : CollatzResearch.WordTrace tailWord_925386 prefixEnd_925386 140790461908628639027921 := by
  unfold tailWord_925386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8437900056373010047859003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22501066816994693460957341 8437900056373010047859003)
  ·
    refine ⟨12656850084559515071788505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8437900056373010047859003 12656850084559515071788505)
    ·
      refine ⟨9492637563419636303841379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12656850084559515071788505 9492637563419636303841379)
      ·
        refine ⟨14238956345129454455762069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9492637563419636303841379 14238956345129454455762069)
        ·
          refine ⟨667451078677943177613847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14238956345129454455762069 667451078677943177613847)
          ·
            refine ⟨1001176618016914766420771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667451078677943177613847 1001176618016914766420771)
            ·
              refine ⟨1501764927025372149631157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001176618016914766420771 1501764927025372149631157)
              ·
                refine ⟨140790461908628639027921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1501764927025372149631157 140790461908628639027921)
                ·
                  rfl

theorem cell20_925386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_925386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925386 prefixEnd_925386 := by exact prefixLift 925386
  have htrace : WordTrace (prefixWord ++ tailWord_925386) baseStart_925386 baseEnd_925386 := by
    simpa [prefixWord, tailWord_925386, baseEnd_925386] using wordTrace_append hprefix tailTrace_925386
  have hstable : (prefixWord ++ tailWord_925386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925386).length < 2 ^ (prefixWord ++ tailWord_925386).sum := by decide
  have hdescent : baseEnd_925386 < baseStart_925386 := by decide
  rcases family_descends (prefixWord ++ tailWord_925386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925435 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_925435 : Nat := 118140960795 + 925435 * 2 ^ 59
def prefixEnd_925435 : Nat := 4983230072969 + 3 ^ 40 * 925435 * 2
def baseEnd_925435 : Nat := 422393750661059524450229

theorem tailTrace_925435 : CollatzResearch.WordTrace tailWord_925435 prefixEnd_925435 422393750661059524450229 := by
  unfold tailWord_925435
  simp only [CollatzResearch.WordTrace]
  refine ⟨33753387402314521559969759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22502258268209681039979839 33753387402314521559969759)
  ·
    refine ⟨50630081103471782339954639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33753387402314521559969759 50630081103471782339954639)
    ·
      refine ⟨75945121655207673509931959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50630081103471782339954639 75945121655207673509931959)
      ·
        refine ⟨113917682482811510264897939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75945121655207673509931959 113917682482811510264897939)
        ·
          refine ⟨170876523724217265397346909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113917682482811510264897939 170876523724217265397346909)
          ·
            refine ⟨64078696396581474524005091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170876523724217265397346909 64078696396581474524005091)
            ·
              refine ⟨96118044594872211786007637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64078696396581474524005091 96118044594872211786007637)
              ·
                refine ⟨1126383335096158731867277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 96118044594872211786007637 1126383335096158731867277)
                ·
                  refine ⟨422393750661059524450229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126383335096158731867277 422393750661059524450229)
                  ·
                    rfl

theorem cell20_925435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_925435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925435 prefixEnd_925435 := by exact prefixLift 925435
  have htrace : WordTrace (prefixWord ++ tailWord_925435) baseStart_925435 baseEnd_925435 := by
    simpa [prefixWord, tailWord_925435, baseEnd_925435] using wordTrace_append hprefix tailTrace_925435
  have hstable : (prefixWord ++ tailWord_925435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925435).length < 2 ^ (prefixWord ++ tailWord_925435).sum := by decide
  have hdescent : baseEnd_925435 < baseStart_925435 := by decide
  rcases family_descends (prefixWord ++ tailWord_925435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925449 : List Nat := [1, 2, 1, 1, 3, 2, 1, 9]
def baseStart_925449 : Nat := 118140960795 + 925449 * 2 ^ 59
def prefixEnd_925449 : Nat := 4983230072969 + 3 ^ 40 * 925449 * 2
def baseEnd_925449 : Nat := 140800046880845899327835

theorem tailTrace_925449 : CollatzResearch.WordTrace tailWord_925449 prefixEnd_925449 140800046880845899327835 := by
  unfold tailWord_925449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33753898024263801950979401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22502598682842534633986267 33753898024263801950979401)
  ·
    refine ⟨25315423518197851463234551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33753898024263801950979401 25315423518197851463234551)
    ·
      refine ⟨37973135277296777194851827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25315423518197851463234551 37973135277296777194851827)
      ·
        refine ⟨56959702915945165792277741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37973135277296777194851827 56959702915945165792277741)
        ·
          refine ⟨21359888593479437172104153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56959702915945165792277741 21359888593479437172104153)
          ·
            refine ⟨16019916445109577879078115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21359888593479437172104153 16019916445109577879078115)
            ·
              refine ⟨24029874667664366818617173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16019916445109577879078115 24029874667664366818617173)
              ·
                refine ⟨140800046880845899327835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24029874667664366818617173 140800046880845899327835)
                ·
                  rfl

theorem cell20_925449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 9].length) (baseStart_925449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925449 prefixEnd_925449 := by exact prefixLift 925449
  have htrace : WordTrace (prefixWord ++ tailWord_925449) baseStart_925449 baseEnd_925449 := by
    simpa [prefixWord, tailWord_925449, baseEnd_925449] using wordTrace_append hprefix tailTrace_925449
  have hstable : (prefixWord ++ tailWord_925449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925449).length < 2 ^ (prefixWord ++ tailWord_925449).sum := by decide
  have hdescent : baseEnd_925449 < baseStart_925449 := by decide
  rcases family_descends (prefixWord ++ tailWord_925449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925466 : List Nat := [3, 1, 1, 3, 2, 3, 1, 6]
def baseStart_925466 : Nat := 118140960795 + 925466 * 2 ^ 59
def prefixEnd_925466 : Nat := 4983230072969 + 3 ^ 40 * 925466 * 2
def baseEnd_925466 : Nat := 140802633301920398138923

theorem tailTrace_925466 : CollatzResearch.WordTrace tailWord_925466 prefixEnd_925466 140802633301920398138923 := by
  unfold tailWord_925466
  simp only [CollatzResearch.WordTrace]
  refine ⟨8438629516300553463587063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22503012043468142569565501 8438629516300553463587063)
  ·
    refine ⟨12657944274450830195380595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8438629516300553463587063 12657944274450830195380595)
    ·
      refine ⟨18986916411676245293070893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12657944274450830195380595 18986916411676245293070893)
      ·
        refine ⟨7120093654378591984901585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18986916411676245293070893 7120093654378591984901585)
        ·
          refine ⟨5340070240783943988676189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7120093654378591984901585 5340070240783943988676189)
          ·
            refine ⟨2002526340293978995753571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5340070240783943988676189 2002526340293978995753571)
            ·
              refine ⟨3003789510440968493630357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2002526340293978995753571 3003789510440968493630357)
              ·
                refine ⟨140802633301920398138923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3003789510440968493630357 140802633301920398138923)
                ·
                  rfl

theorem cell20_925466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_925466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925466 prefixEnd_925466 := by exact prefixLift 925466
  have htrace : WordTrace (prefixWord ++ tailWord_925466) baseStart_925466 baseEnd_925466 := by
    simpa [prefixWord, tailWord_925466, baseEnd_925466] using wordTrace_append hprefix tailTrace_925466
  have hstable : (prefixWord ++ tailWord_925466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925466).length < 2 ^ (prefixWord ++ tailWord_925466).sum := by decide
  have hdescent : baseEnd_925466 < baseStart_925466 := by decide
  rcases family_descends (prefixWord ++ tailWord_925466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925473 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 5]
def baseStart_925473 : Nat := 118140960795 + 925473 * 2 ^ 59
def prefixEnd_925473 : Nat := 4983230072969 + 3 ^ 40 * 925473 * 2
def baseEnd_925473 : Nat := 422411094896500281183407

theorem tailTrace_925473 : CollatzResearch.WordTrace tailWord_925473 prefixEnd_925473 422411094896500281183407 := by
  unfold tailWord_925473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33754773376176854049853073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22503182250784569366568715 33754773376176854049853073)
  ·
    refine ⟨25316080032132640537389805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33754773376176854049853073 25316080032132640537389805)
    ·
      refine ⟨9493530012049740201521177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25316080032132640537389805 9493530012049740201521177)
      ·
        refine ⟨7120147509037305151140883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9493530012049740201521177 7120147509037305151140883)
        ·
          refine ⟨10680221263555957726711325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120147509037305151140883 10680221263555957726711325)
          ·
            refine ⟨4005082973833484147516747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10680221263555957726711325 4005082973833484147516747)
            ·
              refine ⟨6007624460750226221275121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4005082973833484147516747 6007624460750226221275121)
              ·
                refine ⟨4505718345562669665956341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6007624460750226221275121 4505718345562669665956341)
                ·
                  refine ⟨422411094896500281183407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4505718345562669665956341 422411094896500281183407)
                  ·
                    rfl

theorem cell20_925473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_925473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925473 prefixEnd_925473 := by exact prefixLift 925473
  have htrace : WordTrace (prefixWord ++ tailWord_925473) baseStart_925473 baseEnd_925473 := by
    simpa [prefixWord, tailWord_925473, baseEnd_925473] using wordTrace_append hprefix tailTrace_925473
  have hstable : (prefixWord ++ tailWord_925473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925473).length < 2 ^ (prefixWord ++ tailWord_925473).sum := by decide
  have hdescent : baseEnd_925473 < baseStart_925473 := by decide
  rcases family_descends (prefixWord ++ tailWord_925473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925493 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 4]
def baseStart_925493 : Nat := 118140960795 + 925493 * 2 ^ 59
def prefixEnd_925493 : Nat := 4983230072969 + 3 ^ 40 * 925493 * 2
def baseEnd_925493 : Nat := 422420223441469100516659

theorem tailTrace_925493 : CollatzResearch.WordTrace tailWord_925493 prefixEnd_925493 422420223441469100516659 := by
  unfold tailWord_925493
  simp only [CollatzResearch.WordTrace]
  refine ⟨33755502836104397465581133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22503668557402931643720755 33755502836104397465581133)
  ·
    refine ⟨12658313563539149049592925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33755502836104397465581133 12658313563539149049592925)
    ·
      refine ⟨4746867586327180893597347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12658313563539149049592925 4746867586327180893597347)
      ·
        refine ⟨7120301379490771340396021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4746867586327180893597347 7120301379490771340396021)
        ·
          refine ⟨667528254327259813162127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7120301379490771340396021 667528254327259813162127)
          ·
            refine ⟨1001292381490889719743191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667528254327259813162127 1001292381490889719743191)
            ·
              refine ⟨1501938572236334579614787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001292381490889719743191 1501938572236334579614787)
              ·
                refine ⟨2252907858354501869422181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1501938572236334579614787 2252907858354501869422181)
                ·
                  refine ⟨422420223441469100516659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2252907858354501869422181 422420223441469100516659)
                  ·
                    rfl

theorem cell20_925493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 4].length) (baseStart_925493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925493 prefixEnd_925493 := by exact prefixLift 925493
  have htrace : WordTrace (prefixWord ++ tailWord_925493) baseStart_925493 baseEnd_925493 := by
    simpa [prefixWord, tailWord_925493, baseEnd_925493] using wordTrace_append hprefix tailTrace_925493
  have hstable : (prefixWord ++ tailWord_925493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925493).length < 2 ^ (prefixWord ++ tailWord_925493).sum := by decide
  have hdescent : baseEnd_925493 < baseStart_925493 := by decide
  rcases family_descends (prefixWord ++ tailWord_925493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925507 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_925507 : Nat := 118140960795 + 925507 * 2 ^ 59
def prefixEnd_925507 : Nat := 4983230072969 + 3 ^ 40 * 925507 * 2
def baseEnd_925507 : Nat := 422426613422947274049935

theorem tailTrace_925507 : CollatzResearch.WordTrace tailWord_925507 prefixEnd_925507 422426613422947274049935 := by
  unfold tailWord_925507
  simp only [CollatzResearch.WordTrace]
  refine ⟨33756013458053677856590775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22504008972035785237727183 33756013458053677856590775)
  ·
    refine ⟨50634020187080516784886163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33756013458053677856590775 50634020187080516784886163)
    ·
      refine ⟨75951030280620775177329245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50634020187080516784886163 75951030280620775177329245)
      ·
        refine ⟨28481636355232790691498467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75951030280620775177329245 28481636355232790691498467)
        ·
          refine ⟨42722454532849186037247701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28481636355232790691498467 42722454532849186037247701)
          ·
            refine ⟨1001307528113652797747993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42722454532849186037247701 1001307528113652797747993)
            ·
              refine ⟨750980646085239598310995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1001307528113652797747993 750980646085239598310995)
              ·
                refine ⟨1126470969127859397466493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750980646085239598310995 1126470969127859397466493)
                ·
                  refine ⟨422426613422947274049935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126470969127859397466493 422426613422947274049935)
                  ·
                    rfl

theorem cell20_925507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_925507 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925507 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925507 prefixEnd_925507 := by exact prefixLift 925507
  have htrace : WordTrace (prefixWord ++ tailWord_925507) baseStart_925507 baseEnd_925507 := by
    simpa [prefixWord, tailWord_925507, baseEnd_925507] using wordTrace_append hprefix tailTrace_925507
  have hstable : (prefixWord ++ tailWord_925507).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925507).length < 2 ^ (prefixWord ++ tailWord_925507).sum := by decide
  have hdescent : baseEnd_925507 < baseStart_925507 := by decide
  rcases family_descends (prefixWord ++ tailWord_925507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925549 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_925549 : Nat := 118140960795 + 925549 * 2 ^ 59
def prefixEnd_925549 : Nat := 4983230072969 + 3 ^ 40 * 925549 * 2
def baseEnd_925549 : Nat := 422445783367381794649763

theorem tailTrace_925549 : CollatzResearch.WordTrace tailWord_925549 prefixEnd_925549 422445783367381794649763 := by
  unfold tailWord_925549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33757545323901519029619701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22505030215934346019746467 33757545323901519029619701)
  ·
    refine ⟨3164769874115767409026847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33757545323901519029619701 3164769874115767409026847)
    ·
      refine ⟨4747154811173651113540271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3164769874115767409026847 4747154811173651113540271)
      ·
        refine ⟨7120732216760476670310407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4747154811173651113540271 7120732216760476670310407)
        ·
          refine ⟨10681098325140715005465611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7120732216760476670310407 10681098325140715005465611)
          ·
            refine ⟨16021647487711072508198417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10681098325140715005465611 16021647487711072508198417)
            ·
              refine ⟨12016235615783304381148813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16021647487711072508198417 12016235615783304381148813)
              ·
                refine ⟨4506088355918739142930805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12016235615783304381148813 4506088355918739142930805)
                ·
                  refine ⟨422445783367381794649763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4506088355918739142930805 422445783367381794649763)
                  ·
                    rfl

theorem cell20_925549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_925549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925549 prefixEnd_925549 := by exact prefixLift 925549
  have htrace : WordTrace (prefixWord ++ tailWord_925549) baseStart_925549 baseEnd_925549 := by
    simpa [prefixWord, tailWord_925549, baseEnd_925549] using wordTrace_append hprefix tailTrace_925549
  have hstable : (prefixWord ++ tailWord_925549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925549).length < 2 ^ (prefixWord ++ tailWord_925549).sum := by decide
  have hdescent : baseEnd_925549 < baseStart_925549 := by decide
  rcases family_descends (prefixWord ++ tailWord_925549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925604 : List Nat := [2, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_925604 : Nat := 118140960795 + 925604 * 2 ^ 59
def prefixEnd_925604 : Nat := 4983230072969 + 3 ^ 40 * 925604 * 2
def baseEnd_925604 : Nat := 422470886866046047816205

theorem tailTrace_925604 : CollatzResearch.WordTrace tailWord_925604 prefixEnd_925604 422470886866046047816205 := by
  unfold tailWord_925604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16879775669351131711435933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22506367559134842281914577 16879775669351131711435933)
  ·
    refine ⟨6329915876006674391788475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16879775669351131711435933 6329915876006674391788475)
    ·
      refine ⟨9494873814010011587682713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6329915876006674391788475 9494873814010011587682713)
      ·
        refine ⟨7121155360507508690762035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9494873814010011587682713 7121155360507508690762035)
        ·
          refine ⟨10681733040761263036143053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7121155360507508690762035 10681733040761263036143053)
          ·
            refine ⟨4005649890285473638553645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10681733040761263036143053 4005649890285473638553645)
            ·
              refine ⟨1502118708857052614457617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4005649890285473638553645 1502118708857052614457617)
              ·
                refine ⟨1126589031642789460843213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502118708857052614457617 1126589031642789460843213)
                ·
                  refine ⟨422470886866046047816205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126589031642789460843213 422470886866046047816205)
                  ·
                    rfl

theorem cell20_925604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_925604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925604 prefixEnd_925604 := by exact prefixLift 925604
  have htrace : WordTrace (prefixWord ++ tailWord_925604) baseStart_925604 baseEnd_925604 := by
    simpa [prefixWord, tailWord_925604, baseEnd_925604] using wordTrace_append hprefix tailTrace_925604
  have hstable : (prefixWord ++ tailWord_925604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925604).length < 2 ^ (prefixWord ++ tailWord_925604).sum := by decide
  have hdescent : baseEnd_925604 < baseStart_925604 := by decide
  rcases family_descends (prefixWord ++ tailWord_925604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925621 : List Nat := [1, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_925621 : Nat := 118140960795 + 925621 * 2 ^ 59
def prefixEnd_925621 : Nat := 4983230072969 + 3 ^ 40 * 925621 * 2
def baseEnd_925621 : Nat := 422478646129269544249469

theorem tailTrace_925621 : CollatzResearch.WordTrace tailWord_925621 prefixEnd_925621 422478646129269544249469 := by
  unfold tailWord_925621
  simp only [CollatzResearch.WordTrace]
  refine ⟨33760171379640675326240717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22506780919760450217493811 33760171379640675326240717)
  ·
    refine ⟨12660064267365253247340269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33760171379640675326240717 12660064267365253247340269)
    ·
      refine ⟨4747524100261969967752601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12660064267365253247340269 4747524100261969967752601)
      ·
        refine ⟨3560643075196477475814451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4747524100261969967752601 3560643075196477475814451)
        ·
          refine ⟨5340964612794716213721677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3560643075196477475814451 5340964612794716213721677)
          ·
            refine ⟨2002861729798018580145629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5340964612794716213721677 2002861729798018580145629)
            ·
              refine ⟨751073148674256967554611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2002861729798018580145629 751073148674256967554611)
              ·
                refine ⟨1126609723011385451331917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751073148674256967554611 1126609723011385451331917)
                ·
                  refine ⟨422478646129269544249469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126609723011385451331917 422478646129269544249469)
                  ·
                    rfl

theorem cell20_925621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_925621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925621 prefixEnd_925621 := by exact prefixLift 925621
  have htrace : WordTrace (prefixWord ++ tailWord_925621) baseStart_925621 baseEnd_925621 := by
    simpa [prefixWord, tailWord_925621, baseEnd_925621] using wordTrace_append hprefix tailTrace_925621
  have hstable : (prefixWord ++ tailWord_925621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925621).length < 2 ^ (prefixWord ++ tailWord_925621).sum := by decide
  have hdescent : baseEnd_925621 < baseStart_925621 := by decide
  rcases family_descends (prefixWord ++ tailWord_925621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925632 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 4]
def baseStart_925632 : Nat := 118140960795 + 925632 * 2 ^ 59
def prefixEnd_925632 : Nat := 4983230072969 + 3 ^ 40 * 925632 * 2
def baseEnd_925632 : Nat := 422483666829002394882757

theorem tailTrace_925632 : CollatzResearch.WordTrace tailWord_925632 prefixEnd_925632 422483666829002394882757 := by
  unfold tailWord_925632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16880286291300412102445575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22507048388400549469927433 16880286291300412102445575)
  ·
    refine ⟨25320429436950618153668363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16880286291300412102445575 25320429436950618153668363)
    ·
      refine ⟨37980644155425927230502545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25320429436950618153668363 37980644155425927230502545)
      ·
        refine ⟨28485483116569445422876909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37980644155425927230502545 28485483116569445422876909)
        ·
          refine ⟨10682056168713542033578841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28485483116569445422876909 10682056168713542033578841)
          ·
            refine ⟨8011542126535156525184131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10682056168713542033578841 8011542126535156525184131)
            ·
              refine ⟨12017313189802734787776197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8011542126535156525184131 12017313189802734787776197)
              ·
                refine ⟨2253246223088012772708037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12017313189802734787776197 2253246223088012772708037)
                ·
                  refine ⟨422483666829002394882757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2253246223088012772708037 422483666829002394882757)
                  ·
                    rfl

theorem cell20_925632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_925632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925632 prefixEnd_925632 := by exact prefixLift 925632
  have htrace : WordTrace (prefixWord ++ tailWord_925632) baseStart_925632 baseEnd_925632 := by
    simpa [prefixWord, tailWord_925632, baseEnd_925632] using wordTrace_append hprefix tailTrace_925632
  have hstable : (prefixWord ++ tailWord_925632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925632).length < 2 ^ (prefixWord ++ tailWord_925632).sum := by decide
  have hdescent : baseEnd_925632 < baseStart_925632 := by decide
  rcases family_descends (prefixWord ++ tailWord_925632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925649 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 2]
def baseStart_925649 : Nat := 118140960795 + 925649 * 2 ^ 59
def prefixEnd_925649 : Nat := 4983230072969 + 3 ^ 40 * 925649 * 2
def baseEnd_925649 : Nat := 422491426092225891316021

theorem tailTrace_925649 : CollatzResearch.WordTrace tailWord_925649 prefixEnd_925649 422491426092225891316021 := by
  unfold tailWord_925649
  simp only [CollatzResearch.WordTrace]
  refine ⟨33761192623539236108260001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22507461749026157405506667 33761192623539236108260001)
  ·
    refine ⟨25320894467654427081195001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33761192623539236108260001 25320894467654427081195001)
    ·
      refine ⟨18990670850740820310896251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25320894467654427081195001 18990670850740820310896251)
      ·
        refine ⟨28486006276111230466344377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18990670850740820310896251 28486006276111230466344377)
        ·
          refine ⟨21364504707083422849758283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28486006276111230466344377 21364504707083422849758283)
          ·
            refine ⟨32046757060625134274637425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21364504707083422849758283 32046757060625134274637425)
            ·
              refine ⟨24035067795468850705978069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32046757060625134274637425 24035067795468850705978069)
              ·
                refine ⟨563321901456301188421361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24035067795468850705978069 563321901456301188421361)
                ·
                  refine ⟨422491426092225891316021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563321901456301188421361 422491426092225891316021)
                  ·
                    rfl

theorem cell20_925649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 2].length) (baseStart_925649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925649 prefixEnd_925649 := by exact prefixLift 925649
  have htrace : WordTrace (prefixWord ++ tailWord_925649) baseStart_925649 baseEnd_925649 := by
    simpa [prefixWord, tailWord_925649, baseEnd_925649] using wordTrace_append hprefix tailTrace_925649
  have hstable : (prefixWord ++ tailWord_925649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925649).length < 2 ^ (prefixWord ++ tailWord_925649).sum := by decide
  have hdescent : baseEnd_925649 < baseStart_925649 := by decide
  rcases family_descends (prefixWord ++ tailWord_925649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925663 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_925663 : Nat := 118140960795 + 925663 * 2 ^ 59
def prefixEnd_925663 : Nat := 4983230072969 + 3 ^ 40 * 925663 * 2
def baseEnd_925663 : Nat := 422497816073704064849297

theorem tailTrace_925663 : CollatzResearch.WordTrace tailWord_925663 prefixEnd_925663 422497816073704064849297 := by
  unfold tailWord_925663
  simp only [CollatzResearch.WordTrace]
  refine ⟨33761703245488516499269643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22507802163659010999513095 33761703245488516499269643)
  ·
    refine ⟨50642554868232774748904465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33761703245488516499269643 50642554868232774748904465)
    ·
      refine ⟨37981916151174581061678349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50642554868232774748904465 37981916151174581061678349)
      ·
        refine ⟨14243218556690467898129381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37981916151174581061678349 14243218556690467898129381)
        ·
          refine ⟨2670603479379462730899259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14243218556690467898129381 2670603479379462730899259)
          ·
            refine ⟨4005905219069194096348889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2670603479379462730899259 4005905219069194096348889)
            ·
              refine ⟨3004428914301895572261667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4005905219069194096348889 3004428914301895572261667)
              ·
                refine ⟨4506643371452843358392501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3004428914301895572261667 4506643371452843358392501)
                ·
                  refine ⟨422497816073704064849297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4506643371452843358392501 422497816073704064849297)
                  ·
                    rfl

theorem cell20_925663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_925663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925663 prefixEnd_925663 := by exact prefixLift 925663
  have htrace : WordTrace (prefixWord ++ tailWord_925663) baseStart_925663 baseEnd_925663 := by
    simpa [prefixWord, tailWord_925663, baseEnd_925663] using wordTrace_append hprefix tailTrace_925663
  have hstable : (prefixWord ++ tailWord_925663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925663).length < 2 ^ (prefixWord ++ tailWord_925663).sum := by decide
  have hdescent : baseEnd_925663 < baseStart_925663 := by decide
  rcases family_descends (prefixWord ++ tailWord_925663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925680 : List Nat := [2, 1, 1, 1, 3, 2, 6, 1, 3]
def baseStart_925680 : Nat := 118140960795 + 925680 * 2 ^ 59
def prefixEnd_925680 : Nat := 4983230072969 + 3 ^ 40 * 925680 * 2
def baseEnd_925680 : Nat := 422505575336927561282561

theorem tailTrace_925680 : CollatzResearch.WordTrace tailWord_925680 prefixEnd_925680 422505575336927561282561 := by
  unfold tailWord_925680
  simp only [CollatzResearch.WordTrace]
  refine ⟨16881161643213464201319247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22508215524284618935092329 16881161643213464201319247)
  ·
    refine ⟨25321742464820196301978871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16881161643213464201319247 25321742464820196301978871)
    ·
      refine ⟨37982613697230294452968307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25321742464820196301978871 37982613697230294452968307)
      ·
        refine ⟨56973920545845441679452461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37982613697230294452968307 56973920545845441679452461)
        ·
          refine ⟨21365220204692040629794673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56973920545845441679452461 21365220204692040629794673)
          ·
            refine ⟨16023915153519030472346005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21365220204692040629794673 16023915153519030472346005)
            ·
              refine ⟨751121022821204553391219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16023915153519030472346005 751121022821204553391219)
              ·
                refine ⟨1126681534231806830086829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751121022821204553391219 1126681534231806830086829)
                ·
                  refine ⟨422505575336927561282561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1126681534231806830086829 422505575336927561282561)
                  ·
                    rfl

theorem cell20_925680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 6, 1, 3].length) (baseStart_925680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925680 prefixEnd_925680 := by exact prefixLift 925680
  have htrace : WordTrace (prefixWord ++ tailWord_925680) baseStart_925680 baseEnd_925680 := by
    simpa [prefixWord, tailWord_925680, baseEnd_925680] using wordTrace_append hprefix tailTrace_925680
  have hstable : (prefixWord ++ tailWord_925680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925680).length < 2 ^ (prefixWord ++ tailWord_925680).sum := by decide
  have hdescent : baseEnd_925680 < baseStart_925680 := by decide
  rcases family_descends (prefixWord ++ tailWord_925680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925746 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 6]
def baseStart_925746 : Nat := 118140960795 + 925746 * 2 ^ 59
def prefixEnd_925746 : Nat := 4983230072969 + 3 ^ 40 * 925746 * 2
def baseEnd_925746 : Nat := 422535699535324665082291

theorem tailTrace_925746 : CollatzResearch.WordTrace tailWord_925746 prefixEnd_925746 422535699535324665082291 := by
  unfold tailWord_925746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8441182626046955418635273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22509820336125214449694061 8441182626046955418635273)
  ·
    refine ⟨6330886969535216563976455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8441182626046955418635273 6330886969535216563976455)
    ·
      refine ⟨9496330454302824845964683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6330886969535216563976455 9496330454302824845964683)
      ·
        refine ⟨14244495681454237268947025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9496330454302824845964683 14244495681454237268947025)
        ·
          refine ⟨10683371761090677951710269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14244495681454237268947025 10683371761090677951710269)
          ·
            refine ⟨4006264410409004231891351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10683371761090677951710269 4006264410409004231891351)
            ·
              refine ⟨6009396615613506347837027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006264410409004231891351 6009396615613506347837027)
              ·
                refine ⟨9014094923420259521755541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6009396615613506347837027 9014094923420259521755541)
                ·
                  refine ⟨422535699535324665082291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9014094923420259521755541 422535699535324665082291)
                  ·
                    rfl

theorem cell20_925746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_925746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925746 prefixEnd_925746 := by exact prefixLift 925746
  have htrace : WordTrace (prefixWord ++ tailWord_925746) baseStart_925746 baseEnd_925746 := by
    simpa [prefixWord, tailWord_925746, baseEnd_925746] using wordTrace_append hprefix tailTrace_925746
  have hstable : (prefixWord ++ tailWord_925746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925746).length < 2 ^ (prefixWord ++ tailWord_925746).sum := by decide
  have hdescent : baseEnd_925746 < baseStart_925746 := by decide
  rcases family_descends (prefixWord ++ tailWord_925746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925784 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_925784 : Nat := 118140960795 + 925784 * 2 ^ 59
def prefixEnd_925784 : Nat := 4983230072969 + 3 ^ 40 * 925784 * 2
def baseEnd_925784 : Nat := 422553043770765421815469

theorem tailTrace_925784 : CollatzResearch.WordTrace tailWord_925784 prefixEnd_925784 422553043770765421815469 := by
  unfold tailWord_925784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883058239025077082212203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22510744318700102776282937 16883058239025077082212203)
  ·
    refine ⟨25324587358537615623318305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16883058239025077082212203 25324587358537615623318305)
    ·
      refine ⟨18993440518903211717488729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25324587358537615623318305 18993440518903211717488729)
      ·
        refine ⟨14245080389177408788116547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18993440518903211717488729 14245080389177408788116547)
        ·
          refine ⟨21367620583766113182174821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14245080389177408788116547 21367620583766113182174821)
          ·
            refine ⟨4006428859456146221657779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21367620583766113182174821 4006428859456146221657779)
            ·
              refine ⟨6009643289184219332486669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4006428859456146221657779 6009643289184219332486669)
              ·
                refine ⟨2253616233444082249682501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6009643289184219332486669 2253616233444082249682501)
                ·
                  refine ⟨422553043770765421815469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2253616233444082249682501 422553043770765421815469)
                  ·
                    rfl

theorem cell20_925784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_925784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925784 prefixEnd_925784 := by exact prefixLift 925784
  have htrace : WordTrace (prefixWord ++ tailWord_925784) baseStart_925784 baseEnd_925784 := by
    simpa [prefixWord, tailWord_925784, baseEnd_925784] using wordTrace_append hprefix tailTrace_925784
  have hstable : (prefixWord ++ tailWord_925784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925784).length < 2 ^ (prefixWord ++ tailWord_925784).sum := by decide
  have hdescent : baseEnd_925784 < baseStart_925784 := by decide
  rcases family_descends (prefixWord ++ tailWord_925784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925808 : List Nat := [2, 1, 1, 1, 5, 2, 4, 4]
def baseStart_925808 : Nat := 118140960795 + 925808 * 2 ^ 59
def prefixEnd_925808 : Nat := 4983230072969 + 3 ^ 40 * 925808 * 2
def baseEnd_925808 : Nat := 140854666008242668338457

theorem tailTrace_925808 : CollatzResearch.WordTrace tailWord_925808 prefixEnd_925808 140854666008242668338457 := by
  unfold tailWord_925808
  simp only [CollatzResearch.WordTrace]
  refine ⟨16883495914981603131649039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22511327886642137508865385 16883495914981603131649039)
  ·
    refine ⟨25325243872472404697473559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16883495914981603131649039 25325243872472404697473559)
    ·
      refine ⟨37987865808708607046210339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25325243872472404697473559 37987865808708607046210339)
      ·
        refine ⟨56981798713062910569315509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37987865808708607046210339 56981798713062910569315509)
        ·
          refine ⟨5342043629349647865873329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56981798713062910569315509 5342043629349647865873329)
          ·
            refine ⟨4006532722012235899404997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5342043629349647865873329 4006532722012235899404997)
            ·
              refine ⟨751224885377294231138437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4006532722012235899404997 751224885377294231138437)
              ·
                refine ⟨140854666008242668338457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751224885377294231138437 140854666008242668338457)
                ·
                  rfl

theorem cell20_925808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_925808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925808 prefixEnd_925808 := by exact prefixLift 925808
  have htrace : WordTrace (prefixWord ++ tailWord_925808) baseStart_925808 baseEnd_925808 := by
    simpa [prefixWord, tailWord_925808, baseEnd_925808] using wordTrace_append hprefix tailTrace_925808
  have hstable : (prefixWord ++ tailWord_925808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925808).length < 2 ^ (prefixWord ++ tailWord_925808).sum := by decide
  have hdescent : baseEnd_925808 < baseStart_925808 := by decide
  rcases family_descends (prefixWord ++ tailWord_925808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925825 : List Nat := [1, 2, 4, 2, 4, 1, 6]
def baseStart_925825 : Nat := 118140960795 + 925825 * 2 ^ 59
def prefixEnd_925825 : Nat := 4983230072969 + 3 ^ 40 * 925825 * 2
def baseEnd_925825 : Nat := 46952417476439055716515

theorem tailTrace_925825 : CollatzResearch.WordTrace tailWord_925825 prefixEnd_925825 46952417476439055716515 := by
  unfold tailWord_925825
  simp only [CollatzResearch.WordTrace]
  refine ⟨33767611870901618166666929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22511741247267745444444619 33767611870901618166666929)
  ·
    refine ⟨25325708903176213625000197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33767611870901618166666929 25325708903176213625000197)
    ·
      refine ⟨4748570419345540054687537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25325708903176213625000197 4748570419345540054687537)
      ·
        refine ⟨3561427814509155041015653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4748570419345540054687537 3561427814509155041015653)
        ·
          refine ⟨667767715220466570190435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3561427814509155041015653 667767715220466570190435)
          ·
            refine ⟨1001651572830699855285653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 667767715220466570190435 1001651572830699855285653)
            ·
              refine ⟨46952417476439055716515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1001651572830699855285653 46952417476439055716515)
              ·
                rfl

theorem cell20_925825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 6].length) (baseStart_925825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925825 prefixEnd_925825 := by exact prefixLift 925825
  have htrace : WordTrace (prefixWord ++ tailWord_925825) baseStart_925825 baseEnd_925825 := by
    simpa [prefixWord, tailWord_925825, baseEnd_925825] using wordTrace_append hprefix tailTrace_925825
  have hstable : (prefixWord ++ tailWord_925825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925825).length < 2 ^ (prefixWord ++ tailWord_925825).sum := by decide
  have hdescent : baseEnd_925825 < baseStart_925825 := by decide
  rcases family_descends (prefixWord ++ tailWord_925825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925829 : List Nat := [1, 3, 1, 1, 5, 1, 8]
def baseStart_925829 : Nat := 118140960795 + 925829 * 2 ^ 59
def prefixEnd_925829 : Nat := 4983230072969 + 3 ^ 40 * 925829 * 2
def baseEnd_925829 : Nat := 46952620332993918368365

theorem tailTrace_925829 : CollatzResearch.WordTrace tailWord_925829 prefixEnd_925829 46952620332993918368365 := by
  unfold tailWord_925829
  simp only [CollatzResearch.WordTrace]
  refine ⟨33767757762887126849812541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22511838508591417899875027 33767757762887126849812541)
  ·
    refine ⟨12662909161082672568679703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33767757762887126849812541 12662909161082672568679703)
    ·
      refine ⟨18994363741624008853019555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12662909161082672568679703 18994363741624008853019555)
      ·
        refine ⟨28491545612436013279529333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18994363741624008853019555 28491545612436013279529333)
        ·
          refine ⟨2671082401165876244955875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28491545612436013279529333 2671082401165876244955875)
          ·
            refine ⟨4006623601748814367433813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2671082401165876244955875 4006623601748814367433813)
            ·
              refine ⟨46952620332993918368365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4006623601748814367433813 46952620332993918368365)
              ·
                rfl

theorem cell20_925829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 8].length) (baseStart_925829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925829 prefixEnd_925829 := by exact prefixLift 925829
  have htrace : WordTrace (prefixWord ++ tailWord_925829) baseStart_925829 baseEnd_925829 := by
    simpa [prefixWord, tailWord_925829, baseEnd_925829] using wordTrace_append hprefix tailTrace_925829
  have hstable : (prefixWord ++ tailWord_925829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925829).length < 2 ^ (prefixWord ++ tailWord_925829).sum := by decide
  have hdescent : baseEnd_925829 < baseStart_925829 := by decide
  rcases family_descends (prefixWord ++ tailWord_925829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925884 : List Nat := [2, 2, 2, 3, 4, 7]
def baseStart_925884 : Nat := 118140960795 + 925884 * 2 ^ 59
def prefixEnd_925884 : Nat := 4983230072969 + 3 ^ 40 * 925884 * 2
def baseEnd_925884 : Nat := 15651803203541093277101

theorem tailTrace_925884 : CollatzResearch.WordTrace tailWord_925884 prefixEnd_925884 15651803203541093277101 := by
  unfold tailWord_925884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16884881888843935621532353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22513175851791914162043137 16884881888843935621532353)
  ·
    refine ⟨12663661416632951716149265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16884881888843935621532353 12663661416632951716149265)
    ·
      refine ⟨9497746062474713787111949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12663661416632951716149265 9497746062474713787111949)
      ·
        refine ⟨3561654773428017670166981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9497746062474713787111949 3561654773428017670166981)
        ·
          refine ⟨667810270017753313156309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3561654773428017670166981 667810270017753313156309)
          ·
            refine ⟨15651803203541093277101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 667810270017753313156309 15651803203541093277101)
            ·
              rfl

theorem cell20_925884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 7].length) (baseStart_925884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925884 prefixEnd_925884 := by exact prefixLift 925884
  have htrace : WordTrace (prefixWord ++ tailWord_925884) baseStart_925884 baseEnd_925884 := by
    simpa [prefixWord, tailWord_925884, baseEnd_925884] using wordTrace_append hprefix tailTrace_925884
  have hstable : (prefixWord ++ tailWord_925884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925884).length < 2 ^ (prefixWord ++ tailWord_925884).sum := by decide
  have hdescent : baseEnd_925884 < baseStart_925884 := by decide
  rcases family_descends (prefixWord ++ tailWord_925884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925890 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 2]
def baseStart_925890 : Nat := 118140960795 + 925890 * 2 ^ 59
def prefixEnd_925890 : Nat := 4983230072969 + 3 ^ 40 * 925890 * 2
def baseEnd_925890 : Nat := 422601425059100164281703

theorem tailTrace_925890 : CollatzResearch.WordTrace tailWord_925890 prefixEnd_925890 422601425059100164281703 := by
  unfold tailWord_925890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442495653916533566945781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22513321743777422845188749 8442495653916533566945781)
  ·
    refine ⟨791483967554675021901167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8442495653916533566945781 791483967554675021901167)
    ·
      refine ⟨1187225951332012532851751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 791483967554675021901167 1187225951332012532851751)
      ·
        refine ⟨1780838926998018799277627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1187225951332012532851751 1780838926998018799277627)
        ·
          refine ⟨2671258390497028198916441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1780838926998018799277627 2671258390497028198916441)
          ·
            refine ⟨2003443792872771149187331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2671258390497028198916441 2003443792872771149187331)
            ·
              refine ⟨3005165689309156723780997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003443792872771149187331 3005165689309156723780997)
              ·
                refine ⟨563468566745466885708937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3005165689309156723780997 563468566745466885708937)
                ·
                  refine ⟨422601425059100164281703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563468566745466885708937 422601425059100164281703)
                  ·
                    rfl

theorem cell20_925890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_925890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925890 prefixEnd_925890 := by exact prefixLift 925890
  have htrace : WordTrace (prefixWord ++ tailWord_925890) baseStart_925890 baseEnd_925890 := by
    simpa [prefixWord, tailWord_925890, baseEnd_925890] using wordTrace_append hprefix tailTrace_925890
  have hstable : (prefixWord ++ tailWord_925890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925890).length < 2 ^ (prefixWord ++ tailWord_925890).sum := by decide
  have hdescent : baseEnd_925890 < baseStart_925890 := by decide
  rcases family_descends (prefixWord ++ tailWord_925890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925898 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_925898 : Nat := 118140960795 + 925898 * 2 ^ 59
def prefixEnd_925898 : Nat := 4983230072969 + 3 ^ 40 * 925898 * 2
def baseEnd_925898 : Nat := 422605076477087692015003

theorem tailTrace_925898 : CollatzResearch.WordTrace tailWord_925898 prefixEnd_925898 422605076477087692015003 := by
  unfold tailWord_925898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8442568599909287908518587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22513516266424767756049565 8442568599909287908518587)
  ·
    refine ⟨12663852899863931862777881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8442568599909287908518587 12663852899863931862777881)
    ·
      refine ⟨9497889674897948897083411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12663852899863931862777881 9497889674897948897083411)
      ·
        refine ⟨14246834512346923345625117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9497889674897948897083411 14246834512346923345625117)
        ·
          refine ⟨5342562942130096254609419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14246834512346923345625117 5342562942130096254609419)
          ·
            refine ⟨8013844413195144381914129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5342562942130096254609419 8013844413195144381914129)
            ·
              refine ⟨6010383309896358286435597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8013844413195144381914129 6010383309896358286435597)
              ·
                refine ⟨2253893741211134357413349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6010383309896358286435597 2253893741211134357413349)
                ·
                  refine ⟨422605076477087692015003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2253893741211134357413349 422605076477087692015003)
                  ·
                    rfl

theorem cell20_925898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_925898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925898 prefixEnd_925898 := by exact prefixLift 925898
  have htrace : WordTrace (prefixWord ++ tailWord_925898) baseStart_925898 baseEnd_925898 := by
    simpa [prefixWord, tailWord_925898, baseEnd_925898] using wordTrace_append hprefix tailTrace_925898
  have hstable : (prefixWord ++ tailWord_925898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925898).length < 2 ^ (prefixWord ++ tailWord_925898).sum := by decide
  have hdescent : baseEnd_925898 < baseStart_925898 := by decide
  rcases family_descends (prefixWord ++ tailWord_925898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925905 : List Nat := [1, 2, 2, 1, 2, 2, 5, 5]
def baseStart_925905 : Nat := 118140960795 + 925905 * 2 ^ 59
def prefixEnd_925905 : Nat := 4983230072969 + 3 ^ 40 * 925905 * 2
def baseEnd_925905 : Nat := 140869423822608926260547

theorem tailTrace_925905 : CollatzResearch.WordTrace tailWord_925905 prefixEnd_925905 140869423822608926260547 := by
  unfold tailWord_925905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33770529710611791829579169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22513686473741194553052779 33770529710611791829579169)
  ·
    refine ⟨25327897282958843872184377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33770529710611791829579169 25327897282958843872184377)
    ·
      refine ⟨18995922962219132904138283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25327897282958843872184377 18995922962219132904138283)
      ·
        refine ⟨28493884443328699356207425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18995922962219132904138283 28493884443328699356207425)
        ·
          refine ⟨21370413332496524517155569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28493884443328699356207425 21370413332496524517155569)
          ·
            refine ⟨16027809999372393387866677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21370413332496524517155569 16027809999372393387866677)
            ·
              refine ⟨1502607187441161880112501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16027809999372393387866677 1502607187441161880112501)
              ·
                refine ⟨140869423822608926260547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1502607187441161880112501 140869423822608926260547)
                ·
                  rfl

theorem cell20_925905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 5].length) (baseStart_925905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925905 prefixEnd_925905 := by exact prefixLift 925905
  have htrace : WordTrace (prefixWord ++ tailWord_925905) baseStart_925905 baseEnd_925905 := by
    simpa [prefixWord, tailWord_925905, baseEnd_925905] using wordTrace_append hprefix tailTrace_925905
  have hstable : (prefixWord ++ tailWord_925905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925905).length < 2 ^ (prefixWord ++ tailWord_925905).sum := by decide
  have hdescent : baseEnd_925905 < baseStart_925905 := by decide
  rcases family_descends (prefixWord ++ tailWord_925905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925946 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_925946 : Nat := 118140960795 + 925946 * 2 ^ 59
def prefixEnd_925946 : Nat := 4983230072969 + 3 ^ 40 * 925946 * 2
def baseEnd_925946 : Nat := 422626984985012858414807

theorem tailTrace_925946 : CollatzResearch.WordTrace tailWord_925946 prefixEnd_925946 422626984985012858414807 := by
  unfold tailWord_925946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8443006275865813957955423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22514683402308837221214461 8443006275865813957955423)
  ·
    refine ⟨12664509413798720936933135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8443006275865813957955423 12664509413798720936933135)
    ·
      refine ⟨18996764120698081405399703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12664509413798720936933135 18996764120698081405399703)
      ·
        refine ⟨28495146181047122108099555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18996764120698081405399703 28495146181047122108099555)
        ·
          refine ⟨42742719271570683162149333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28495146181047122108099555 42742719271570683162149333)
          ·
            refine ⟨1001782482927437886612875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42742719271570683162149333 1001782482927437886612875)
            ·
              refine ⟨1502673724391156829919313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001782482927437886612875 1502673724391156829919313)
              ·
                refine ⟨1127005293293367622439485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502673724391156829919313 1127005293293367622439485)
                ·
                  refine ⟨422626984985012858414807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127005293293367622439485 422626984985012858414807)
                  ·
                    rfl

theorem cell20_925946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_925946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925946 prefixEnd_925946 := by exact prefixLift 925946
  have htrace : WordTrace (prefixWord ++ tailWord_925946) baseStart_925946 baseEnd_925946 := by
    simpa [prefixWord, tailWord_925946, baseEnd_925946] using wordTrace_append hprefix tailTrace_925946
  have hstable : (prefixWord ++ tailWord_925946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925946).length < 2 ^ (prefixWord ++ tailWord_925946).sum := by decide
  have hdescent : baseEnd_925946 < baseStart_925946 := by decide
  rcases family_descends (prefixWord ++ tailWord_925946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925953 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 2]
def baseStart_925953 : Nat := 118140960795 + 925953 * 2 ^ 59
def prefixEnd_925953 : Nat := 4983230072969 + 3 ^ 40 * 925953 * 2
def baseEnd_925953 : Nat := 422630179975751945181445

theorem tailTrace_925953 : CollatzResearch.WordTrace tailWord_925953 prefixEnd_925953 422630179975751945181445 := by
  unfold tailWord_925953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33772280414437896027326513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22514853609625264018217675 33772280414437896027326513)
  ·
    refine ⟨25329210310828422020494885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33772280414437896027326513 25329210310828422020494885)
    ·
      refine ⟨4749226933280329128842791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25329210310828422020494885 4749226933280329128842791)
      ·
        refine ⟨7123840399920493693264187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749226933280329128842791 7123840399920493693264187)
        ·
          refine ⟨10685760599880740539896281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7123840399920493693264187 10685760599880740539896281)
          ·
            refine ⟨8014320449910555404922211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10685760599880740539896281 8014320449910555404922211)
            ·
              refine ⟨12021480674865833107383317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8014320449910555404922211 12021480674865833107383317)
              ·
                refine ⟨563506906634335926908593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12021480674865833107383317 563506906634335926908593)
                ·
                  refine ⟨422630179975751945181445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563506906634335926908593 422630179975751945181445)
                  ·
                    rfl

theorem cell20_925953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 2].length) (baseStart_925953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_925953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_925953 prefixEnd_925953 := by exact prefixLift 925953
  have htrace : WordTrace (prefixWord ++ tailWord_925953) baseStart_925953 baseEnd_925953 := by
    simpa [prefixWord, tailWord_925953, baseEnd_925953] using wordTrace_append hprefix tailTrace_925953
  have hstable : (prefixWord ++ tailWord_925953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925953).length < 2 ^ (prefixWord ++ tailWord_925953).sum := by decide
  have hdescent : baseEnd_925953 < baseStart_925953 := by decide
  rcases family_descends (prefixWord ++ tailWord_925953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926005 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_926005 : Nat := 118140960795 + 926005 * 2 ^ 59
def prefixEnd_926005 : Nat := 4983230072969 + 3 ^ 40 * 926005 * 2
def baseEnd_926005 : Nat := 422653914192670875447899

theorem tailTrace_926005 : CollatzResearch.WordTrace tailWord_926005 prefixEnd_926005 422653914192670875447899 := by
  unfold tailWord_926005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33774177010249508908219469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22516118006833005938812979 33774177010249508908219469)
  ·
    refine ⟨12665316378843565840582301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33774177010249508908219469 12665316378843565840582301)
    ·
      refine ⟨4749493642066337190218363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12665316378843565840582301 4749493642066337190218363)
      ·
        refine ⟨7124240463099505785327545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4749493642066337190218363 7124240463099505785327545)
        ·
          refine ⟨5343180347324629338995659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7124240463099505785327545 5343180347324629338995659)
          ·
            refine ⟨8014770520986944008493489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343180347324629338995659 8014770520986944008493489)
            ·
              refine ⟨6011077890740208006370117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8014770520986944008493489 6011077890740208006370117)
              ·
                refine ⟨1127077104513789001194397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6011077890740208006370117 1127077104513789001194397)
                ·
                  refine ⟨422653914192670875447899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127077104513789001194397 422653914192670875447899)
                  ·
                    rfl

theorem cell20_926005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_926005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926005 prefixEnd_926005 := by exact prefixLift 926005
  have htrace : WordTrace (prefixWord ++ tailWord_926005) baseStart_926005 baseEnd_926005 := by
    simpa [prefixWord, tailWord_926005, baseEnd_926005] using wordTrace_append hprefix tailTrace_926005
  have hstable : (prefixWord ++ tailWord_926005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926005).length < 2 ^ (prefixWord ++ tailWord_926005).sum := by decide
  have hdescent : baseEnd_926005 < baseStart_926005 := by decide
  rcases family_descends (prefixWord ++ tailWord_926005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926060 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_926060 : Nat := 118140960795 + 926060 * 2 ^ 59
def prefixEnd_926060 : Nat := 4983230072969 + 3 ^ 40 * 926060 * 2
def baseEnd_926060 : Nat := 422679017691335128614341

theorem tailTrace_926060 : CollatzResearch.WordTrace tailWord_926060 prefixEnd_926060 422679017691335128614341 := by
  unfold tailWord_926060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888091512525126650735817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22517455350033502200981089 16888091512525126650735817)
  ·
    refine ⟨12666068634393844988051863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16888091512525126650735817 12666068634393844988051863)
    ·
      refine ⟨18999102951590767482077795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12666068634393844988051863 18999102951590767482077795)
      ·
        refine ⟨28498654427386151223116693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18999102951590767482077795 28498654427386151223116693)
        ·
          refine ⟨1335874426283725838583595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28498654427386151223116693 1335874426283725838583595)
          ·
            refine ⟨2003811639425588757875393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1335874426283725838583595 2003811639425588757875393)
            ·
              refine ⟨1502858729569191568406545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2003811639425588757875393 1502858729569191568406545)
              ·
                refine ⟨1127144047176893676304909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1502858729569191568406545 1127144047176893676304909)
                ·
                  refine ⟨422679017691335128614341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127144047176893676304909 422679017691335128614341)
                  ·
                    rfl

theorem cell20_926060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_926060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926060 prefixEnd_926060 := by exact prefixLift 926060
  have htrace : WordTrace (prefixWord ++ tailWord_926060) baseStart_926060 baseEnd_926060 := by
    simpa [prefixWord, tailWord_926060, baseEnd_926060] using wordTrace_append hprefix tailTrace_926060
  have hstable : (prefixWord ++ tailWord_926060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926060).length < 2 ^ (prefixWord ++ tailWord_926060).sum := by decide
  have hdescent : baseEnd_926060 < baseStart_926060 := by decide
  rcases family_descends (prefixWord ++ tailWord_926060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926070 : List Nat := [5, 1, 1, 4, 1, 2, 1, 5]
def baseStart_926070 : Nat := 118140960795 + 926070 * 2 ^ 59
def prefixEnd_926070 : Nat := 4983230072969 + 3 ^ 40 * 926070 * 2
def baseEnd_926070 : Nat := 140894527321273179426989

theorem tailTrace_926070 : CollatzResearch.WordTrace tailWord_926070 prefixEnd_926070 140894527321273179426989 := by
  unfold tailWord_926070
  simp only [CollatzResearch.WordTrace]
  refine ⟨2111034234688376563083479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22517698503342683339557109 2111034234688376563083479)
  ·
    refine ⟨3166551352032564844625219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2111034234688376563083479 3166551352032564844625219)
    ·
      refine ⟨4749827028048847266937829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3166551352032564844625219 4749827028048847266937829)
      ·
        refine ⟨890592567759158862550843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4749827028048847266937829 890592567759158862550843)
        ·
          refine ⟨1335888851638738293826265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890592567759158862550843 1335888851638738293826265)
          ·
            refine ⟨1001916638729053720369699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1335888851638738293826265 1001916638729053720369699)
            ·
              refine ⟨1502874958093580580554549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1001916638729053720369699 1502874958093580580554549)
              ·
                refine ⟨140894527321273179426989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1502874958093580580554549 140894527321273179426989)
                ·
                  rfl

theorem cell20_926070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_926070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926070 prefixEnd_926070 := by exact prefixLift 926070
  have htrace : WordTrace (prefixWord ++ tailWord_926070) baseStart_926070 baseEnd_926070 := by
    simpa [prefixWord, tailWord_926070, baseEnd_926070] using wordTrace_append hprefix tailTrace_926070
  have hstable : (prefixWord ++ tailWord_926070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926070).length < 2 ^ (prefixWord ++ tailWord_926070).sum := by decide
  have hdescent : baseEnd_926070 < baseStart_926070 := by decide
  rcases family_descends (prefixWord ++ tailWord_926070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926088 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 4]
def baseStart_926088 : Nat := 118140960795 + 926088 * 2 ^ 59
def prefixEnd_926088 : Nat := 4983230072969 + 3 ^ 40 * 926088 * 2
def baseEnd_926088 : Nat := 422691797654291475680893

theorem tailTrace_926088 : CollatzResearch.WordTrace tailWord_926088 prefixEnd_926088 422691797654291475680893 := by
  unfold tailWord_926088
  simp only [CollatzResearch.WordTrace]
  refine ⟨16888602134474407041745459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22518136179299209388993945 16888602134474407041745459)
  ·
    refine ⟨25332903201711610562618189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16888602134474407041745459 25332903201711610562618189)
    ·
      refine ⟨9499838700641853960981821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25332903201711610562618189 9499838700641853960981821)
      ·
        refine ⟨3562439512740695235368183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9499838700641853960981821 3562439512740695235368183)
        ·
          refine ⟨5343659269111042853052275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562439512740695235368183 5343659269111042853052275)
          ·
            refine ⟨8015488903666564279578413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5343659269111042853052275 8015488903666564279578413)
            ·
              refine ⟨3005808338874961604841905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8015488903666564279578413 3005808338874961604841905)
              ·
                refine ⟨2254356254156221203631429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3005808338874961604841905 2254356254156221203631429)
                ·
                  refine ⟨422691797654291475680893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254356254156221203631429 422691797654291475680893)
                  ·
                    rfl

theorem cell20_926088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 4].length) (baseStart_926088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926088 prefixEnd_926088 := by exact prefixLift 926088
  have htrace : WordTrace (prefixWord ++ tailWord_926088) baseStart_926088 baseEnd_926088 := by
    simpa [prefixWord, tailWord_926088, baseEnd_926088] using wordTrace_append hprefix tailTrace_926088
  have hstable : (prefixWord ++ tailWord_926088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926088).length < 2 ^ (prefixWord ++ tailWord_926088).sum := by decide
  have hdescent : baseEnd_926088 < baseStart_926088 := by decide
  rcases family_descends (prefixWord ++ tailWord_926088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926105 : List Nat := [1, 2, 1, 2, 1, 4, 4, 3, 2]
def baseStart_926105 : Nat := 118140960795 + 926105 * 2 ^ 59
def prefixEnd_926105 : Nat := 4983230072969 + 3 ^ 40 * 926105 * 2
def baseEnd_926105 : Nat := 422699556917514972114157

theorem tailTrace_926105 : CollatzResearch.WordTrace tailWord_926105 prefixEnd_926105 422699556917514972114157 := by
  unfold tailWord_926105
  simp only [CollatzResearch.WordTrace]
  refine ⟨33777824309887225986859769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22518549539924817324573179 33777824309887225986859769)
  ·
    refine ⟨25333368232415419490144827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33777824309887225986859769 25333368232415419490144827)
    ·
      refine ⟨38000052348623129235217241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25333368232415419490144827 38000052348623129235217241)
      ·
        refine ⟨28500039261467346926412931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38000052348623129235217241 28500039261467346926412931)
        ·
          refine ⟨42750058892201020389619397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28500039261467346926412931 42750058892201020389619397)
          ·
            refine ⟨8015636042287691323053637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42750058892201020389619397 8015636042287691323053637)
            ·
              refine ⟨1502931757928942123072557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8015636042287691323053637 1502931757928942123072557)
              ·
                refine ⟨563599409223353296152209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1502931757928942123072557 563599409223353296152209)
                ·
                  refine ⟨422699556917514972114157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563599409223353296152209 422699556917514972114157)
                  ·
                    rfl

theorem cell20_926105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 3, 2].length) (baseStart_926105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926105 prefixEnd_926105 := by exact prefixLift 926105
  have htrace : WordTrace (prefixWord ++ tailWord_926105) baseStart_926105 baseEnd_926105 := by
    simpa [prefixWord, tailWord_926105, baseEnd_926105] using wordTrace_append hprefix tailTrace_926105
  have hstable : (prefixWord ++ tailWord_926105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926105).length < 2 ^ (prefixWord ++ tailWord_926105).sum := by decide
  have hdescent : baseEnd_926105 < baseStart_926105 := by decide
  rcases family_descends (prefixWord ++ tailWord_926105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926119 : List Nat := [1, 1, 6, 1, 1, 3, 1, 1, 5]
def baseStart_926119 : Nat := 118140960795 + 926119 * 2 ^ 59
def prefixEnd_926119 : Nat := 4983230072969 + 3 ^ 40 * 926119 * 2
def baseEnd_926119 : Nat := 422705946898993145647433

theorem tailTrace_926119 : CollatzResearch.WordTrace tailWord_926119 prefixEnd_926119 422705946898993145647433 := by
  unfold tailWord_926119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33778334931836506377869411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22518889954557670918579607 33778334931836506377869411)
  ·
    refine ⟨50667502397754759566804117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33778334931836506377869411 50667502397754759566804117)
    ·
      refine ⟨2375039174894754354693943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50667502397754759566804117 2375039174894754354693943)
      ·
        refine ⟨3562558762342131532040915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2375039174894754354693943 3562558762342131532040915)
        ·
          refine ⟨5343838143513197298061373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562558762342131532040915 5343838143513197298061373)
          ·
            refine ⟨2003939303817448986773015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5343838143513197298061373 2003939303817448986773015)
            ·
              refine ⟨3005908955726173480159523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2003939303817448986773015 3005908955726173480159523)
              ·
                refine ⟨4508863433589260220239285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3005908955726173480159523 4508863433589260220239285)
                ·
                  refine ⟨422705946898993145647433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4508863433589260220239285 422705946898993145647433)
                  ·
                    rfl

theorem cell20_926119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_926119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926119 prefixEnd_926119 := by exact prefixLift 926119
  have htrace : WordTrace (prefixWord ++ tailWord_926119) baseStart_926119 baseEnd_926119 := by
    simpa [prefixWord, tailWord_926119, baseEnd_926119] using wordTrace_append hprefix tailTrace_926119
  have hstable : (prefixWord ++ tailWord_926119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926119).length < 2 ^ (prefixWord ++ tailWord_926119).sum := by decide
  have hdescent : baseEnd_926119 < baseStart_926119 := by decide
  rcases family_descends (prefixWord ++ tailWord_926119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926185 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_926185 : Nat := 118140960795 + 926185 * 2 ^ 59
def prefixEnd_926185 : Nat := 4983230072969 + 3 ^ 40 * 926185 * 2
def baseEnd_926185 : Nat := 422736071097390249447163

theorem tailTrace_926185 : CollatzResearch.WordTrace tailWord_926185 prefixEnd_926185 422736071097390249447163 := by
  unfold tailWord_926185
  simp only [CollatzResearch.WordTrace]
  refine ⟨33780742149597399649772009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22520494766398266433181339 33780742149597399649772009)
  ·
    refine ⟨25335556612198049737329007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33780742149597399649772009 25335556612198049737329007)
    ·
      refine ⟨38003334918297074605993511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25335556612198049737329007 38003334918297074605993511)
      ·
        refine ⟨57005002377445611908990267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38003334918297074605993511 57005002377445611908990267)
        ·
          refine ⟨85507503566168417863485401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57005002377445611908990267 85507503566168417863485401)
          ·
            refine ⟨64130627674626313397614051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85507503566168417863485401 64130627674626313397614051)
            ·
              refine ⟨96195941511939470096421077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64130627674626313397614051 96195941511939470096421077)
              ·
                refine ⟨2254592379186081330384869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96195941511939470096421077 2254592379186081330384869)
                ·
                  refine ⟨422736071097390249447163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254592379186081330384869 422736071097390249447163)
                  ·
                    rfl

theorem cell20_926185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_926185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926185 prefixEnd_926185 := by exact prefixLift 926185
  have htrace : WordTrace (prefixWord ++ tailWord_926185) baseStart_926185 baseEnd_926185 := by
    simpa [prefixWord, tailWord_926185, baseEnd_926185] using wordTrace_append hprefix tailTrace_926185
  have hstable : (prefixWord ++ tailWord_926185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926185).length < 2 ^ (prefixWord ++ tailWord_926185).sum := by decide
  have hdescent : baseEnd_926185 < baseStart_926185 := by decide
  rcases family_descends (prefixWord ++ tailWord_926185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926209 : List Nat := [1, 2, 4, 1, 3, 1, 2, 6]
def baseStart_926209 : Nat := 118140960795 + 926209 * 2 ^ 59
def prefixEnd_926209 : Nat := 4983230072969 + 3 ^ 40 * 926209 * 2
def baseEnd_926209 : Nat := 140915675117117610882355

theorem tailTrace_926209 : CollatzResearch.WordTrace tailWord_926209 prefixEnd_926209 140915675117117610882355 := by
  unfold tailWord_926209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33781617501510451748645681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22521078334340301165763787 33781617501510451748645681)
  ·
    refine ⟨25336213126132838811484261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33781617501510451748645681 25336213126132838811484261)
    ·
      refine ⟨4750539961149907277153299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25336213126132838811484261 4750539961149907277153299)
      ·
        refine ⟨7125809941724860915729949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750539961149907277153299 7125809941724860915729949)
        ·
          refine ⟨2672178728146822843398731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7125809941724860915729949 2672178728146822843398731)
          ·
            refine ⟨4008268092220234265098097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672178728146822843398731 4008268092220234265098097)
            ·
              refine ⟨3006201069165175698823573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4008268092220234265098097 3006201069165175698823573)
              ·
                refine ⟨140915675117117610882355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3006201069165175698823573 140915675117117610882355)
                ·
                  rfl

theorem cell20_926209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 6].length) (baseStart_926209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926209 prefixEnd_926209 := by exact prefixLift 926209
  have htrace : WordTrace (prefixWord ++ tailWord_926209) baseStart_926209 baseEnd_926209 := by
    simpa [prefixWord, tailWord_926209, baseEnd_926209] using wordTrace_append hprefix tailTrace_926209
  have hstable : (prefixWord ++ tailWord_926209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926209).length < 2 ^ (prefixWord ++ tailWord_926209).sum := by decide
  have hdescent : baseEnd_926209 < baseStart_926209 := by decide
  rcases family_descends (prefixWord ++ tailWord_926209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926236 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 2]
def baseStart_926236 : Nat := 118140960795 + 926236 * 2 ^ 59
def prefixEnd_926236 : Nat := 4983230072969 + 3 ^ 40 * 926236 * 2
def baseEnd_926236 : Nat := 422759348887060738746955

theorem tailTrace_926236 : CollatzResearch.WordTrace tailWord_926236 prefixEnd_926236 422759348887060738746955 := by
  unfold tailWord_926236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891301136206317679939281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22521734848275090239919041 16891301136206317679939281)
  ·
    refine ⟨12668475852154738259954461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16891301136206317679939281 12668475852154738259954461)
    ·
      refine ⟨4750678444558026847482923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12668475852154738259954461 4750678444558026847482923)
      ·
        refine ⟨7126017666837040271224385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4750678444558026847482923 7126017666837040271224385)
        ·
          refine ⟨5344513250127780203418289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7126017666837040271224385 5344513250127780203418289)
          ·
            refine ⟨4008384937595835152563717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5344513250127780203418289 4008384937595835152563717)
            ·
              refine ⟨751572175799219091105697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4008384937595835152563717 751572175799219091105697)
              ·
                refine ⟨563679131849414318329273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751572175799219091105697 563679131849414318329273)
                ·
                  refine ⟨422759348887060738746955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563679131849414318329273 422759348887060738746955)
                  ·
                    rfl

theorem cell20_926236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_926236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926236 prefixEnd_926236 := by exact prefixLift 926236
  have htrace : WordTrace (prefixWord ++ tailWord_926236) baseStart_926236 baseEnd_926236 := by
    simpa [prefixWord, tailWord_926236, baseEnd_926236] using wordTrace_append hprefix tailTrace_926236
  have hstable : (prefixWord ++ tailWord_926236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926236).length < 2 ^ (prefixWord ++ tailWord_926236).sum := by decide
  have hdescent : baseEnd_926236 < baseStart_926236 := by decide
  rcases family_descends (prefixWord ++ tailWord_926236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926253 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 4]
def baseStart_926253 : Nat := 118140960795 + 926253 * 2 ^ 59
def prefixEnd_926253 : Nat := 4983230072969 + 3 ^ 40 * 926253 * 2
def baseEnd_926253 : Nat := 422767108150284235180219

theorem tailTrace_926253 : CollatzResearch.WordTrace tailWord_926253 prefixEnd_926253 422767108150284235180219 := by
  unfold tailWord_926253
  simp only [CollatzResearch.WordTrace]
  refine ⟨33783222313351047263247413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22522148208900698175498275 33783222313351047263247413)
  ·
    refine ⟨3167177091876660680929445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33783222313351047263247413 3167177091876660680929445)
    ·
      refine ⟨593845704726873877674271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3167177091876660680929445 593845704726873877674271)
      ·
        refine ⟨890768557090310816511407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593845704726873877674271 890768557090310816511407)
        ·
          refine ⟨1336152835635466224767111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890768557090310816511407 1336152835635466224767111)
          ·
            refine ⟨2004229253453199337150667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336152835635466224767111 2004229253453199337150667)
            ·
              refine ⟨3006343880179799005726001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2004229253453199337150667 3006343880179799005726001)
              ·
                refine ⟨2254757910134849254294501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3006343880179799005726001 2254757910134849254294501)
                ·
                  refine ⟨422767108150284235180219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2254757910134849254294501 422767108150284235180219)
                  ·
                    rfl

theorem cell20_926253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_926253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926253 prefixEnd_926253 := by exact prefixLift 926253
  have htrace : WordTrace (prefixWord ++ tailWord_926253) baseStart_926253 baseEnd_926253 := by
    simpa [prefixWord, tailWord_926253, baseEnd_926253] using wordTrace_append hprefix tailTrace_926253
  have hstable : (prefixWord ++ tailWord_926253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926253).length < 2 ^ (prefixWord ++ tailWord_926253).sum := by decide
  have hdescent : baseEnd_926253 < baseStart_926253 := by decide
  rcases family_descends (prefixWord ++ tailWord_926253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926260 : List Nat := [2, 5, 1, 3, 1, 1, 3, 4]
def baseStart_926260 : Nat := 118140960795 + 926260 * 2 ^ 59
def prefixEnd_926260 : Nat := 4983230072969 + 3 ^ 40 * 926260 * 2
def baseEnd_926260 : Nat := 140923434380341107315619

theorem tailTrace_926260 : CollatzResearch.WordTrace tailWord_926260 prefixEnd_926260 140923434380341107315619 := by
  unfold tailWord_926260
  simp only [CollatzResearch.WordTrace]
  refine ⟨16891738812162843729376117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22522318416217124972501489 16891738812162843729376117)
  ·
    refine ⟨1583600513640266599629011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16891738812162843729376117 1583600513640266599629011)
    ·
      refine ⟨2375400770460399899443517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583600513640266599629011 2375400770460399899443517)
      ·
        refine ⟨890775288922649962291319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2375400770460399899443517 890775288922649962291319)
        ·
          refine ⟨1336162933383974943436979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 890775288922649962291319 1336162933383974943436979)
          ·
            refine ⟨2004244400075962415155469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336162933383974943436979 2004244400075962415155469)
            ·
              refine ⟨751591650028485905683301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2004244400075962415155469 751591650028485905683301)
              ·
                refine ⟨140923434380341107315619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751591650028485905683301 140923434380341107315619)
                ·
                  rfl

theorem cell20_926260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_926260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926260 prefixEnd_926260 := by exact prefixLift 926260
  have htrace : WordTrace (prefixWord ++ tailWord_926260) baseStart_926260 baseEnd_926260 := by
    simpa [prefixWord, tailWord_926260, baseEnd_926260] using wordTrace_append hprefix tailTrace_926260
  have hstable : (prefixWord ++ tailWord_926260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926260).length < 2 ^ (prefixWord ++ tailWord_926260).sum := by decide
  have hdescent : baseEnd_926260 < baseStart_926260 := by decide
  rcases family_descends (prefixWord ++ tailWord_926260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926350 : List Nat := [4, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_926350 : Nat := 118140960795 + 926350 * 2 ^ 59
def prefixEnd_926350 : Nat := 4983230072969 + 3 ^ 40 * 926350 * 2
def baseEnd_926350 : Nat := 422811381593383008946489

theorem tailTrace_926350 : CollatzResearch.WordTrace tailWord_926350 prefixEnd_926350 422811381593383008946489 := by
  unfold tailWord_926350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4223345024249954103691063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22524506795999755219685669 4223345024249954103691063)
  ·
    refine ⟨6335017536374931155536595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4223345024249954103691063 6335017536374931155536595)
    ·
      refine ⟨9502526304562396733304893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6335017536374931155536595 9502526304562396733304893)
      ·
        refine ⟨3563447364210898774989335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9502526304562396733304893 3563447364210898774989335)
        ·
          refine ⟨5345171046316348162484003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563447364210898774989335 5345171046316348162484003)
          ·
            refine ⟨8017756569474522243726005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345171046316348162484003 8017756569474522243726005)
            ·
              refine ⟨751664678388236460349313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8017756569474522243726005 751664678388236460349313)
              ·
                refine ⟨563748508791177345261985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751664678388236460349313 563748508791177345261985)
                ·
                  refine ⟨422811381593383008946489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563748508791177345261985 422811381593383008946489)
                  ·
                    rfl

theorem cell20_926350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_926350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926350 prefixEnd_926350 := by exact prefixLift 926350
  have htrace : WordTrace (prefixWord ++ tailWord_926350) baseStart_926350 baseEnd_926350 := by
    simpa [prefixWord, tailWord_926350, baseEnd_926350] using wordTrace_append hprefix tailTrace_926350
  have hstable : (prefixWord ++ tailWord_926350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926350).length < 2 ^ (prefixWord ++ tailWord_926350).sum := by decide
  have hdescent : baseEnd_926350 < baseStart_926350 := by decide
  rcases family_descends (prefixWord ++ tailWord_926350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926364 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 3]
def baseStart_926364 : Nat := 118140960795 + 926364 * 2 ^ 59
def prefixEnd_926364 : Nat := 4983230072969 + 3 ^ 40 * 926364 * 2
def baseEnd_926364 : Nat := 422817771574861182479765

theorem tailTrace_926364 : CollatzResearch.WordTrace tailWord_926364 prefixEnd_926364 422817771574861182479765 := by
  unfold tailWord_926364
  simp only [CollatzResearch.WordTrace]
  refine ⟨16893635407974456610269073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22524847210632608813692097 16893635407974456610269073)
  ·
    refine ⟨12670226555980842457701805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16893635407974456610269073 12670226555980842457701805)
    ·
      refine ⟨4751334958492815921638177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12670226555980842457701805 4751334958492815921638177)
      ·
        refine ⟨3563501218869611941228633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4751334958492815921638177 3563501218869611941228633)
        ·
          refine ⟨2672625914152208955921475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3563501218869611941228633 2672625914152208955921475)
          ·
            refine ⟨4008938871228313433882213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2672625914152208955921475 4008938871228313433882213)
            ·
              refine ⟨751676038355308768852915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4008938871228313433882213 751676038355308768852915)
              ·
                refine ⟨1127514057532963153279373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751676038355308768852915 1127514057532963153279373)
                ·
                  refine ⟨422817771574861182479765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127514057532963153279373 422817771574861182479765)
                  ·
                    rfl

theorem cell20_926364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_926364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926364 prefixEnd_926364 := by exact prefixLift 926364
  have htrace : WordTrace (prefixWord ++ tailWord_926364) baseStart_926364 baseEnd_926364 := by
    simpa [prefixWord, tailWord_926364, baseEnd_926364] using wordTrace_append hprefix tailTrace_926364
  have hstable : (prefixWord ++ tailWord_926364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926364).length < 2 ^ (prefixWord ++ tailWord_926364).sum := by decide
  have hdescent : baseEnd_926364 < baseStart_926364 := by decide
  rcases family_descends (prefixWord ++ tailWord_926364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926401 : List Nat := [1, 2, 6, 2, 2, 1, 2, 2, 2]
def baseStart_926401 : Nat := 118140960795 + 926401 * 2 ^ 59
def prefixEnd_926401 : Nat := 4983230072969 + 3 ^ 40 * 926401 * 2
def baseEnd_926401 : Nat := 422834659383053498246281

theorem tailTrace_926401 : CollatzResearch.WordTrace tailWord_926401 prefixEnd_926401 422834659383053498246281 := by
  unfold tailWord_926401
  simp only [CollatzResearch.WordTrace]
  refine ⟨33788620316814868539635057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22525746877876579026423371 33788620316814868539635057)
  ·
    refine ⟨25341465237611151404726293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33788620316814868539635057 25341465237611151404726293)
    ·
      refine ⟨1187881183013022722096545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25341465237611151404726293 1187881183013022722096545)
      ·
        refine ⟨890910887259767041572409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1187881183013022722096545 890910887259767041572409)
        ·
          refine ⟨668183165444825281179307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890910887259767041572409 668183165444825281179307)
          ·
            refine ⟨1002274748167237921768961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668183165444825281179307 1002274748167237921768961)
            ·
              refine ⟨751706061125428441326721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002274748167237921768961 751706061125428441326721)
              ·
                refine ⟨563779545844071330995041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751706061125428441326721 563779545844071330995041)
                ·
                  refine ⟨422834659383053498246281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563779545844071330995041 422834659383053498246281)
                  ·
                    rfl

theorem cell20_926401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_926401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926401 prefixEnd_926401 := by exact prefixLift 926401
  have htrace : WordTrace (prefixWord ++ tailWord_926401) baseStart_926401 baseEnd_926401 := by
    simpa [prefixWord, tailWord_926401, baseEnd_926401] using wordTrace_append hprefix tailTrace_926401
  have hstable : (prefixWord ++ tailWord_926401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926401).length < 2 ^ (prefixWord ++ tailWord_926401).sum := by decide
  have hdescent : baseEnd_926401 < baseStart_926401 := by decide
  rcases family_descends (prefixWord ++ tailWord_926401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926447 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 2]
def baseStart_926447 : Nat := 118140960795 + 926447 * 2 ^ 59
def prefixEnd_926447 : Nat := 4983230072969 + 3 ^ 40 * 926447 * 2
def baseEnd_926447 : Nat := 422855655036481782712759

theorem tailTrace_926447 : CollatzResearch.WordTrace tailWord_926447 prefixEnd_926447 422855655036481782712759 := by
  unfold tailWord_926447
  simp only [CollatzResearch.WordTrace]
  refine ⟨33790298074648218395809595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22526865383098812263873063 33790298074648218395809595)
  ·
    refine ⟨50685447111972327593714393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33790298074648218395809595 50685447111972327593714393)
    ·
      refine ⟨38014085333979245695285795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50685447111972327593714393 38014085333979245695285795)
      ·
        refine ⟨57021128000968868542928693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38014085333979245695285795 57021128000968868542928693)
        ·
          refine ⟨5345730750090831425899565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57021128000968868542928693 5345730750090831425899565)
          ·
            refine ⟨2004649031284061784712337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5345730750090831425899565 2004649031284061784712337)
            ·
              refine ⟨1503486773463046338534253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2004649031284061784712337 1503486773463046338534253)
              ·
                refine ⟨563807540048642376950345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1503486773463046338534253 563807540048642376950345)
                ·
                  refine ⟨422855655036481782712759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563807540048642376950345 422855655036481782712759)
                  ·
                    rfl

theorem cell20_926447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 2].length) (baseStart_926447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926447 prefixEnd_926447 := by exact prefixLift 926447
  have htrace : WordTrace (prefixWord ++ tailWord_926447) baseStart_926447 baseEnd_926447 := by
    simpa [prefixWord, tailWord_926447, baseEnd_926447] using wordTrace_append hprefix tailTrace_926447
  have hstable : (prefixWord ++ tailWord_926447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926447).length < 2 ^ (prefixWord ++ tailWord_926447).sum := by decide
  have hdescent : baseEnd_926447 < baseStart_926447 := by decide
  rcases family_descends (prefixWord ++ tailWord_926447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926453 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 3]
def baseStart_926453 : Nat := 118140960795 + 926453 * 2 ^ 59
def prefixEnd_926453 : Nat := 4983230072969 + 3 ^ 40 * 926453 * 2
def baseEnd_926453 : Nat := 422858393599972428512735

theorem tailTrace_926453 : CollatzResearch.WordTrace tailWord_926453 prefixEnd_926453 422858393599972428512735 := by
  unfold tailWord_926453
  simp only [CollatzResearch.WordTrace]
  refine ⟨33790516912626481420528013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22527011275084320947018675 33790516912626481420528013)
  ·
    refine ⟨12671443842234930532698005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33790516912626481420528013 12671443842234930532698005)
    ·
      refine ⟨593973930104762368720219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12671443842234930532698005 593973930104762368720219)
      ·
        refine ⟨890960895157143553080329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593973930104762368720219 890960895157143553080329)
        ·
          refine ⟨668220671367857664810247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 890960895157143553080329 668220671367857664810247)
          ·
            refine ⟨1002331007051786497215371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668220671367857664810247 1002331007051786497215371)
            ·
              refine ⟨1503496510577679745823057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002331007051786497215371 1503496510577679745823057)
              ·
                refine ⟨1127622382933259809367293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1503496510577679745823057 1127622382933259809367293)
                ·
                  refine ⟨422858393599972428512735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127622382933259809367293 422858393599972428512735)
                  ·
                    rfl

theorem cell20_926453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_926453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926453 prefixEnd_926453 := by exact prefixLift 926453
  have htrace : WordTrace (prefixWord ++ tailWord_926453) baseStart_926453 baseEnd_926453 := by
    simpa [prefixWord, tailWord_926453, baseEnd_926453] using wordTrace_append hprefix tailTrace_926453
  have hstable : (prefixWord ++ tailWord_926453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926453).length < 2 ^ (prefixWord ++ tailWord_926453).sum := by decide
  have hdescent : baseEnd_926453 < baseStart_926453 := by decide
  rcases family_descends (prefixWord ++ tailWord_926453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926468 : List Nat := [2, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_926468 : Nat := 118140960795 + 926468 * 2 ^ 59
def prefixEnd_926468 : Nat := 4983230072969 + 3 ^ 40 * 926468 * 2
def baseEnd_926468 : Nat := 422865240008699043012673

theorem tailTrace_926468 : CollatzResearch.WordTrace tailWord_926468 prefixEnd_926468 422865240008699043012673 := by
  unfold tailWord_926468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895532003786069491162029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22527376005048092654882705 16895532003786069491162029)
  ·
    refine ⟨6335824501419776059185761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16895532003786069491162029 6335824501419776059185761)
    ·
      refine ⟨4751868376064832044389321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6335824501419776059185761 4751868376064832044389321)
      ·
        refine ⟨3563901282048624033291991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4751868376064832044389321 3563901282048624033291991)
        ·
          refine ⟨5345851923072936049937987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3563901282048624033291991 5345851923072936049937987)
          ·
            refine ⟨8018777884609404074906981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5345851923072936049937987 8018777884609404074906981)
            ·
              refine ⟨1503520853364263264045059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8018777884609404074906981 1503520853364263264045059)
              ·
                refine ⟨2255281280046394896067589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1503520853364263264045059 2255281280046394896067589)
                ·
                  refine ⟨422865240008699043012673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2255281280046394896067589 422865240008699043012673)
                  ·
                    rfl

theorem cell20_926468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_926468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926468 prefixEnd_926468 := by exact prefixLift 926468
  have htrace : WordTrace (prefixWord ++ tailWord_926468) baseStart_926468 baseEnd_926468 := by
    simpa [prefixWord, tailWord_926468, baseEnd_926468] using wordTrace_append hprefix tailTrace_926468
  have hstable : (prefixWord ++ tailWord_926468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926468).length < 2 ^ (prefixWord ++ tailWord_926468).sum := by decide
  have hdescent : baseEnd_926468 < baseStart_926468 := by decide
  rcases family_descends (prefixWord ++ tailWord_926468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926492 : List Nat := [2, 2, 3, 1, 1, 5, 2, 4]
def baseStart_926492 : Nat := 118140960795 + 926492 * 2 ^ 59
def prefixEnd_926492 : Nat := 4983230072969 + 3 ^ 40 * 926492 * 2
def baseEnd_926492 : Nat := 140958731420887208737525

theorem tailTrace_926492 : CollatzResearch.WordTrace tailWord_926492 prefixEnd_926492 140958731420887208737525 := by
  unfold tailWord_926492
  simp only [CollatzResearch.WordTrace]
  refine ⟨16895969679742595540598865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22527959572990127387465153 16895969679742595540598865)
  ·
    refine ⟨12671977259806946655449149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16895969679742595540598865 12671977259806946655449149)
    ·
      refine ⟨4751991472427604995793431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12671977259806946655449149 4751991472427604995793431)
      ·
        refine ⟨7127987208641407493690147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4751991472427604995793431 7127987208641407493690147)
        ·
          refine ⟨10691980812962111240535221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7127987208641407493690147 10691980812962111240535221)
          ·
            refine ⟨1002373201215197928800177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10691980812962111240535221 1002373201215197928800177)
            ·
              refine ⟨751779900911398446600133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002373201215197928800177 751779900911398446600133)
              ·
                refine ⟨140958731420887208737525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 751779900911398446600133 140958731420887208737525)
                ·
                  rfl

theorem cell20_926492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_926492 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926492 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926492 prefixEnd_926492 := by exact prefixLift 926492
  have htrace : WordTrace (prefixWord ++ tailWord_926492) baseStart_926492 baseEnd_926492 := by
    simpa [prefixWord, tailWord_926492, baseEnd_926492] using wordTrace_append hprefix tailTrace_926492
  have hstable : (prefixWord ++ tailWord_926492).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926492).length < 2 ^ (prefixWord ++ tailWord_926492).sum := by decide
  have hdescent : baseEnd_926492 < baseStart_926492 := by decide
  rcases family_descends (prefixWord ++ tailWord_926492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926509 : List Nat := [1, 5, 3, 2, 1, 2, 6]
def baseStart_926509 : Nat := 118140960795 + 926509 * 2 ^ 59
def prefixEnd_926509 : Nat := 4983230072969 + 3 ^ 40 * 926509 * 2
def baseEnd_926509 : Nat := 46987105947320569182871

theorem tailTrace_926509 : CollatzResearch.WordTrace tailWord_926509 prefixEnd_926509 46987105947320569182871 := by
  unfold tailWord_926509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33792559400423602984566581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22528372933615735323044387 33792559400423602984566581)
  ·
    refine ⟨3168052443789712779803117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33792559400423602984566581 3168052443789712779803117)
    ·
      refine ⟨1188019666421142292426169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3168052443789712779803117 1188019666421142292426169)
      ·
        refine ⟨891014749815856719319627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1188019666421142292426169 891014749815856719319627)
        ·
          refine ⟨1336522124723785078979441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891014749815856719319627 1336522124723785078979441)
          ·
            refine ⟨1002391593542838809234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1336522124723785078979441 1002391593542838809234581)
            ·
              refine ⟨46987105947320569182871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1002391593542838809234581 46987105947320569182871)
              ·
                rfl

theorem cell20_926509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 6].length) (baseStart_926509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926509 prefixEnd_926509 := by exact prefixLift 926509
  have htrace : WordTrace (prefixWord ++ tailWord_926509) baseStart_926509 baseEnd_926509 := by
    simpa [prefixWord, tailWord_926509, baseEnd_926509] using wordTrace_append hprefix tailTrace_926509
  have hstable : (prefixWord ++ tailWord_926509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926509).length < 2 ^ (prefixWord ++ tailWord_926509).sum := by decide
  have hdescent : baseEnd_926509 < baseStart_926509 := by decide
  rcases family_descends (prefixWord ++ tailWord_926509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926520 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 3]
def baseStart_926520 : Nat := 118140960795 + 926520 * 2 ^ 59
def prefixEnd_926520 : Nat := 4983230072969 + 3 ^ 40 * 926520 * 2
def baseEnd_926520 : Nat := 422888974225617973279127

theorem tailTrace_926520 : CollatzResearch.WordTrace tailWord_926520 prefixEnd_926520 422888974225617973279127 := by
  unfold tailWord_926520
  simp only [CollatzResearch.WordTrace]
  refine ⟨16896480301691875931608507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22528640402255834575478009 16896480301691875931608507)
  ·
    refine ⟨25344720452537813897412761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16896480301691875931608507 25344720452537813897412761)
    ·
      refine ⟨19008540339403360423059571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25344720452537813897412761 19008540339403360423059571)
      ·
        refine ⟨28512810509105040634589357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19008540339403360423059571 28512810509105040634589357)
        ·
          refine ⟨10692303940914390237971009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28512810509105040634589357 10692303940914390237971009)
          ·
            refine ⟨8019227955685792678478257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10692303940914390237971009 8019227955685792678478257)
            ·
              refine ⟨6014420966764344508858693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8019227955685792678478257 6014420966764344508858693)
              ·
                refine ⟨1127703931268314595411005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6014420966764344508858693 1127703931268314595411005)
                ·
                  refine ⟨422888974225617973279127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127703931268314595411005 422888974225617973279127)
                  ·
                    rfl

theorem cell20_926520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 3].length) (baseStart_926520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926520 prefixEnd_926520 := by exact prefixLift 926520
  have htrace : WordTrace (prefixWord ++ tailWord_926520) baseStart_926520 baseEnd_926520 := by
    simpa [prefixWord, tailWord_926520, baseEnd_926520] using wordTrace_append hprefix tailTrace_926520
  have hstable : (prefixWord ++ tailWord_926520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926520).length < 2 ^ (prefixWord ++ tailWord_926520).sum := by decide
  have hdescent : baseEnd_926520 < baseStart_926520 := by decide
  rcases family_descends (prefixWord ++ tailWord_926520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926537 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 3]
def baseStart_926537 : Nat := 118140960795 + 926537 * 2 ^ 59
def prefixEnd_926537 : Nat := 4983230072969 + 3 ^ 40 * 926537 * 2
def baseEnd_926537 : Nat := 422896733488841469712391

theorem tailTrace_926537 : CollatzResearch.WordTrace tailWord_926537 prefixEnd_926537 422896733488841469712391 := by
  unfold tailWord_926537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33793580644322163766585865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22529053762881442511057243 33793580644322163766585865)
  ·
    refine ⟨25345185483241622824939399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33793580644322163766585865 25345185483241622824939399)
    ·
      refine ⟨38017778224862434237409099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25345185483241622824939399 38017778224862434237409099)
      ·
        refine ⟨57026667337293651356113649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38017778224862434237409099 57026667337293651356113649)
        ·
          refine ⟨42770000502970238517085237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57026667337293651356113649 42770000502970238517085237)
          ·
            refine ⟨4009687547153459860976741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42770000502970238517085237 4009687547153459860976741)
            ·
              refine ⟨751816415091273723933139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4009687547153459860976741 751816415091273723933139)
              ·
                refine ⟨1127724622636910585899709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 751816415091273723933139 1127724622636910585899709)
                ·
                  refine ⟨422896733488841469712391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127724622636910585899709 422896733488841469712391)
                  ·
                    rfl

theorem cell20_926537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_926537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926537 prefixEnd_926537 := by exact prefixLift 926537
  have htrace : WordTrace (prefixWord ++ tailWord_926537) baseStart_926537 baseEnd_926537 := by
    simpa [prefixWord, tailWord_926537, baseEnd_926537] using wordTrace_append hprefix tailTrace_926537
  have hstable : (prefixWord ++ tailWord_926537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926537).length < 2 ^ (prefixWord ++ tailWord_926537).sum := by decide
  have hdescent : baseEnd_926537 < baseStart_926537 := by decide
  rcases family_descends (prefixWord ++ tailWord_926537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926574 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 2]
def baseStart_926574 : Nat := 118140960795 + 926574 * 2 ^ 59
def prefixEnd_926574 : Nat := 4983230072969 + 3 ^ 40 * 926574 * 2
def baseEnd_926574 : Nat := 422913621297033785478907

theorem tailTrace_926574 : CollatzResearch.WordTrace tailWord_926574 prefixEnd_926574 422913621297033785478907 := by
  unfold tailWord_926574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4224366268148514885710347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22529953430125412723788517 4224366268148514885710347)
  ·
    refine ⟨6336549402222772328565521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4224366268148514885710347 6336549402222772328565521)
    ·
      refine ⟨4752412051667079246424141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6336549402222772328565521 4752412051667079246424141)
      ·
        refine ⟨1782154519375154717409053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4752412051667079246424141 1782154519375154717409053)
        ·
          refine ⟨668307944765683019028395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1782154519375154717409053 668307944765683019028395)
          ·
            refine ⟨1002461917148524528542593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668307944765683019028395 1002461917148524528542593)
            ·
              refine ⟨751846437861393396406945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1002461917148524528542593 751846437861393396406945)
              ·
                refine ⟨563884828396045047305209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751846437861393396406945 563884828396045047305209)
                ·
                  refine ⟨422913621297033785478907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563884828396045047305209 422913621297033785478907)
                  ·
                    rfl

theorem cell20_926574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_926574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926574 prefixEnd_926574 := by exact prefixLift 926574
  have htrace : WordTrace (prefixWord ++ tailWord_926574) baseStart_926574 baseEnd_926574 := by
    simpa [prefixWord, tailWord_926574, baseEnd_926574] using wordTrace_append hprefix tailTrace_926574
  have hstable : (prefixWord ++ tailWord_926574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926574).length < 2 ^ (prefixWord ++ tailWord_926574).sum := by decide
  have hdescent : baseEnd_926574 < baseStart_926574 := by decide
  rcases family_descends (prefixWord ++ tailWord_926574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926579 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 5]
def baseStart_926579 : Nat := 118140960795 + 926579 * 2 ^ 59
def prefixEnd_926579 : Nat := 4983230072969 + 3 ^ 40 * 926579 * 2
def baseEnd_926579 : Nat := 422915903433275990312219

theorem tailTrace_926579 : CollatzResearch.WordTrace tailWord_926579 prefixEnd_926579 422915903433275990312219 := by
  unfold tailWord_926579
  simp only [CollatzResearch.WordTrace]
  refine ⟨33795112510170004939614791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22530075006780003293076527 33795112510170004939614791)
  ·
    refine ⟨50692668765255007409422187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33795112510170004939614791 50692668765255007409422187)
    ·
      refine ⟨76039003147882511114133281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50692668765255007409422187 76039003147882511114133281)
      ·
        refine ⟨57029252360911883335599961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76039003147882511114133281 57029252360911883335599961)
        ·
          refine ⟨42771939270683912501699971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57029252360911883335599961 42771939270683912501699971)
          ·
            refine ⟨64157908906025868752549957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42771939270683912501699971 64157908906025868752549957)
            ·
              refine ⟨12029607919879850391103117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64157908906025868752549957 12029607919879850391103117)
              ·
                refine ⟨4511102969954943896663669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12029607919879850391103117 4511102969954943896663669)
                ·
                  refine ⟨422915903433275990312219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511102969954943896663669 422915903433275990312219)
                  ·
                    rfl

theorem cell20_926579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_926579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926579 prefixEnd_926579 := by exact prefixLift 926579
  have htrace : WordTrace (prefixWord ++ tailWord_926579) baseStart_926579 baseEnd_926579 := by
    simpa [prefixWord, tailWord_926579, baseEnd_926579] using wordTrace_append hprefix tailTrace_926579
  have hstable : (prefixWord ++ tailWord_926579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926579).length < 2 ^ (prefixWord ++ tailWord_926579).sum := by decide
  have hdescent : baseEnd_926579 < baseStart_926579 := by decide
  rcases family_descends (prefixWord ++ tailWord_926579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926617 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_926617 : Nat := 118140960795 + 926617 * 2 ^ 59
def prefixEnd_926617 : Nat := 4983230072969 + 3 ^ 40 * 926617 * 2
def baseEnd_926617 : Nat := 422933247668716747045397

theorem tailTrace_926617 : CollatzResearch.WordTrace tailWord_926617 prefixEnd_926617 422933247668716747045397 := by
  unfold tailWord_926617
  simp only [CollatzResearch.WordTrace]
  refine ⟨33796498484032337429498105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22530998989354891619665403 33796498484032337429498105)
  ·
    refine ⟨25347373863024253072123579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33796498484032337429498105 25347373863024253072123579)
    ·
      refine ⟨38021060794536379608185369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25347373863024253072123579 38021060794536379608185369)
      ·
        refine ⟨28515795595902284706139027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38021060794536379608185369 28515795595902284706139027)
        ·
          refine ⟨42773693393853427059208541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28515795595902284706139027 42773693393853427059208541)
          ·
            refine ⟨16040135022695035147203203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42773693393853427059208541 16040135022695035147203203)
            ·
              refine ⟨24060202534042552720804805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16040135022695035147203203 24060202534042552720804805)
              ·
                refine ⟨4511287975132978635150901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24060202534042552720804805 4511287975132978635150901)
                ·
                  refine ⟨422933247668716747045397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4511287975132978635150901 422933247668716747045397)
                  ·
                    rfl

theorem cell20_926617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_926617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926617 prefixEnd_926617 := by exact prefixLift 926617
  have htrace : WordTrace (prefixWord ++ tailWord_926617) baseStart_926617 baseEnd_926617 := by
    simpa [prefixWord, tailWord_926617, baseEnd_926617] using wordTrace_append hprefix tailTrace_926617
  have hstable : (prefixWord ++ tailWord_926617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926617).length < 2 ^ (prefixWord ++ tailWord_926617).sum := by decide
  have hdescent : baseEnd_926617 < baseStart_926617 := by decide
  rcases family_descends (prefixWord ++ tailWord_926617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926696 : List Nat := [2, 1, 4, 1, 1, 1, 2, 6, 2]
def baseStart_926696 : Nat := 118140960795 + 926696 * 2 ^ 59
def prefixEnd_926696 : Nat := 4983230072969 + 3 ^ 40 * 926696 * 2
def baseEnd_926696 : Nat := 422969305421343583411741

theorem tailTrace_926696 : CollatzResearch.WordTrace tailWord_926696 prefixEnd_926696 422969305421343583411741 := by
  unfold tailWord_926696
  simp only [CollatzResearch.WordTrace]
  refine ⟨16899689925373066960811971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22532919900497422614415961 16899689925373066960811971)
  ·
    refine ⟨25349534888059600441217957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16899689925373066960811971 25349534888059600441217957)
    ·
      refine ⟨4753037791511175082728367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25349534888059600441217957 4753037791511175082728367)
      ·
        refine ⟨7129556687266762624092551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4753037791511175082728367 7129556687266762624092551)
        ·
          refine ⟨10694335030900143936138827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129556687266762624092551 10694335030900143936138827)
          ·
            refine ⟨16041502546350215904208241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10694335030900143936138827 16041502546350215904208241)
            ·
              refine ⟨12031126909762661928156181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16041502546350215904208241 12031126909762661928156181)
              ·
                refine ⟨563959073895124777882321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12031126909762661928156181 563959073895124777882321)
                ·
                  refine ⟨422969305421343583411741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563959073895124777882321 422969305421343583411741)
                  ·
                    rfl

theorem cell20_926696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_926696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926696 prefixEnd_926696 := by exact prefixLift 926696
  have htrace : WordTrace (prefixWord ++ tailWord_926696) baseStart_926696 baseEnd_926696 := by
    simpa [prefixWord, tailWord_926696, baseEnd_926696] using wordTrace_append hprefix tailTrace_926696
  have hstable : (prefixWord ++ tailWord_926696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926696).length < 2 ^ (prefixWord ++ tailWord_926696).sum := by decide
  have hdescent : baseEnd_926696 < baseStart_926696 := by decide
  rcases family_descends (prefixWord ++ tailWord_926696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926706 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 3]
def baseStart_926706 : Nat := 118140960795 + 926706 * 2 ^ 59
def prefixEnd_926706 : Nat := 4983230072969 + 3 ^ 40 * 926706 * 2
def baseEnd_926706 : Nat := 422973869693827993078367

theorem tailTrace_926706 : CollatzResearch.WordTrace tailWord_926706 prefixEnd_926706 422973869693827993078367 := by
  unfold tailWord_926706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8449936145177476407371993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22533163053806603752991981 8449936145177476407371993)
  ·
    refine ⟨6337452108883107305528995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8449936145177476407371993 6337452108883107305528995)
    ·
      refine ⟨9506178163324660958293493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6337452108883107305528995 9506178163324660958293493)
      ·
        refine ⟨891204202811686964840015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9506178163324660958293493 891204202811686964840015)
        ·
          refine ⟨1336806304217530447260023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891204202811686964840015 1336806304217530447260023)
          ·
            refine ⟨2005209456326295670890035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336806304217530447260023 2005209456326295670890035)
            ·
              refine ⟨3007814184489443506335053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005209456326295670890035 3007814184489443506335053)
              ·
                refine ⟨1127930319183541314875645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3007814184489443506335053 1127930319183541314875645)
                ·
                  refine ⟨422973869693827993078367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1127930319183541314875645 422973869693827993078367)
                  ·
                    rfl

theorem cell20_926706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_926706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926706 prefixEnd_926706 := by exact prefixLift 926706
  have htrace : WordTrace (prefixWord ++ tailWord_926706) baseStart_926706 baseEnd_926706 := by
    simpa [prefixWord, tailWord_926706, baseEnd_926706] using wordTrace_append hprefix tailTrace_926706
  have hstable : (prefixWord ++ tailWord_926706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926706).length < 2 ^ (prefixWord ++ tailWord_926706).sum := by decide
  have hdescent : baseEnd_926706 < baseStart_926706 := by decide
  rcases family_descends (prefixWord ++ tailWord_926706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926751 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 2]
def baseStart_926751 : Nat := 118140960795 + 926751 * 2 ^ 59
def prefixEnd_926751 : Nat := 4983230072969 + 3 ^ 40 * 926751 * 2
def baseEnd_926751 : Nat := 422994408920007836578183

theorem tailTrace_926751 : CollatzResearch.WordTrace tailWord_926751 prefixEnd_926751 422994408920007836578183 := by
  unfold tailWord_926751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33801385865546878314876107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22534257243697918876584071 33801385865546878314876107)
  ·
    refine ⟨50702078798320317472314161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33801385865546878314876107 50702078798320317472314161)
    ·
      refine ⟨38026559098740238104235621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50702078798320317472314161 38026559098740238104235621)
      ·
        refine ⟨7129979831013794644544179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38026559098740238104235621 7129979831013794644544179)
        ·
          refine ⟨10694969746520691966816269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7129979831013794644544179 10694969746520691966816269)
          ·
            refine ⟨4010613654945259487556101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10694969746520691966816269 4010613654945259487556101)
            ·
              refine ⟨751990060302236153916769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4010613654945259487556101 751990060302236153916769)
              ·
                refine ⟨563992545226677115437577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 751990060302236153916769 563992545226677115437577)
                ·
                  refine ⟨422994408920007836578183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 563992545226677115437577 422994408920007836578183)
                  ·
                    rfl

theorem cell20_926751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 2].length) (baseStart_926751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926751 prefixEnd_926751 := by exact prefixLift 926751
  have htrace : WordTrace (prefixWord ++ tailWord_926751) baseStart_926751 baseEnd_926751 := by
    simpa [prefixWord, tailWord_926751, baseEnd_926751] using wordTrace_append hprefix tailTrace_926751
  have hstable : (prefixWord ++ tailWord_926751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926751).length < 2 ^ (prefixWord ++ tailWord_926751).sum := by decide
  have hdescent : baseEnd_926751 < baseStart_926751 := by decide
  rcases family_descends (prefixWord ++ tailWord_926751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926772 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 6]
def baseStart_926772 : Nat := 118140960795 + 926772 * 2 ^ 59
def prefixEnd_926772 : Nat := 4983230072969 + 3 ^ 40 * 926772 * 2
def baseEnd_926772 : Nat := 423003993892225096878097

theorem tailTrace_926772 : CollatzResearch.WordTrace tailWord_926772 prefixEnd_926772 423003993892225096878097 := by
  unfold tailWord_926772
  simp only [CollatzResearch.WordTrace]
  refine ⟨16901075899235399450695285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22534767865647199267593713 16901075899235399450695285)
  ·
    refine ⟨1584475865553318698502683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16901075899235399450695285 1584475865553318698502683)
    ·
      refine ⟨2376713798329978047754025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1584475865553318698502683 2376713798329978047754025)
      ·
        refine ⟨1782535348747483535815519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2376713798329978047754025 1782535348747483535815519)
        ·
          refine ⟨2673803023121225303723279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1782535348747483535815519 2673803023121225303723279)
          ·
            refine ⟨4010704534681837955584919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2673803023121225303723279 4010704534681837955584919)
            ·
              refine ⟨6016056802022756933377379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4010704534681837955584919 6016056802022756933377379)
              ·
                refine ⟨9024085203034135400066069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6016056802022756933377379 9024085203034135400066069)
                ·
                  refine ⟨423003993892225096878097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9024085203034135400066069 423003993892225096878097)
                  ·
                    rfl

theorem cell20_926772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_926772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926772 prefixEnd_926772 := by exact prefixLift 926772
  have htrace : WordTrace (prefixWord ++ tailWord_926772) baseStart_926772 baseEnd_926772 := by
    simpa [prefixWord, tailWord_926772, baseEnd_926772] using wordTrace_append hprefix tailTrace_926772
  have hstable : (prefixWord ++ tailWord_926772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926772).length < 2 ^ (prefixWord ++ tailWord_926772).sum := by decide
  have hdescent : baseEnd_926772 < baseStart_926772 := by decide
  rcases family_descends (prefixWord ++ tailWord_926772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926806 : List Nat := [5, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_926806 : Nat := 118140960795 + 926806 * 2 ^ 59
def prefixEnd_926806 : Nat := 4983230072969 + 3 ^ 40 * 926806 * 2
def baseEnd_926806 : Nat := 423019512418672089744625

theorem tailTrace_926806 : CollatzResearch.WordTrace tailWord_926806 prefixEnd_926806 423019512418672089744625 := by
  unfold tailWord_926806
  simp only [CollatzResearch.WordTrace]
  refine ⟨2112711992521726419258017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22535594586898415138752181 2112711992521726419258017)
  ·
    refine ⟨1584533994391294814443513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2112711992521726419258017 1584533994391294814443513)
    ·
      refine ⟨1188400495793471110832635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1584533994391294814443513 1188400495793471110832635)
      ·
        refine ⟨1782600743690206666248953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188400495793471110832635 1782600743690206666248953)
        ·
          refine ⟨1336950557767654999686715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782600743690206666248953 1336950557767654999686715)
          ·
            refine ⟨2005425836651482499530073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1336950557767654999686715 2005425836651482499530073)
            ·
              refine ⟨1504069377488611874647555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2005425836651482499530073 1504069377488611874647555)
              ·
                refine ⟨2256104066232917811971333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1504069377488611874647555 2256104066232917811971333)
                ·
                  refine ⟨423019512418672089744625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256104066232917811971333 423019512418672089744625)
                  ·
                    rfl

theorem cell20_926806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_926806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926806 prefixEnd_926806 := by exact prefixLift 926806
  have htrace : WordTrace (prefixWord ++ tailWord_926806) baseStart_926806 baseEnd_926806 := by
    simpa [prefixWord, tailWord_926806, baseEnd_926806] using wordTrace_append hprefix tailTrace_926806
  have hstable : (prefixWord ++ tailWord_926806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926806).length < 2 ^ (prefixWord ++ tailWord_926806).sum := by decide
  have hdescent : baseEnd_926806 < baseStart_926806 := by decide
  rcases family_descends (prefixWord ++ tailWord_926806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926845 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_926845 : Nat := 118140960795 + 926845 * 2 ^ 59
def prefixEnd_926845 : Nat := 4983230072969 + 3 ^ 40 * 926845 * 2
def baseEnd_926845 : Nat := 423037313081361287444465

theorem tailTrace_926845 : CollatzResearch.WordTrace tailWord_926845 prefixEnd_926845 423037313081361287444465 := by
  unfold tailWord_926845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33804814327206332368797989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22536542884804221579198659 33804814327206332368797989)
  ·
    refine ⟨6338402686351187319149623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33804814327206332368797989 6338402686351187319149623)
    ·
      refine ⟨9507604029526780978724435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6338402686351187319149623 9507604029526780978724435)
      ·
        refine ⟨14261406044290171468086653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9507604029526780978724435 14261406044290171468086653)
        ·
          refine ⟨5348027266608814300532495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14261406044290171468086653 5348027266608814300532495)
          ·
            refine ⟨8022040899913221450798743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5348027266608814300532495 8022040899913221450798743)
            ·
              refine ⟨12033061349869832176198115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8022040899913221450798743 12033061349869832176198115)
              ·
                refine ⟨18049592024804748264297173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12033061349869832176198115 18049592024804748264297173)
                ·
                  refine ⟨423037313081361287444465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18049592024804748264297173 423037313081361287444465)
                  ·
                    rfl

theorem cell20_926845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_926845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926845 prefixEnd_926845 := by exact prefixLift 926845
  have htrace : WordTrace (prefixWord ++ tailWord_926845) baseStart_926845 baseEnd_926845 := by
    simpa [prefixWord, tailWord_926845, baseEnd_926845] using wordTrace_append hprefix tailTrace_926845
  have hstable : (prefixWord ++ tailWord_926845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926845).length < 2 ^ (prefixWord ++ tailWord_926845).sum := by decide
  have hdescent : baseEnd_926845 < baseStart_926845 := by decide
  rcases family_descends (prefixWord ++ tailWord_926845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926848 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 2]
def baseStart_926848 : Nat := 118140960795 + 926848 * 2 ^ 59
def prefixEnd_926848 : Nat := 4983230072969 + 3 ^ 40 * 926848 * 2
def baseEnd_926848 : Nat := 423038682363106610344453

theorem tailTrace_926848 : CollatzResearch.WordTrace tailWord_926848 prefixEnd_926848 423038682363106610344453 := by
  unfold tailWord_926848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902461873097731940578599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22536615830796975920771465 16902461873097731940578599)
  ·
    refine ⟨25353692809646597910867899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16902461873097731940578599 25353692809646597910867899)
    ·
      refine ⟨38030539214469896866301849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25353692809646597910867899 38030539214469896866301849)
      ·
        refine ⟨28522904410852422649726387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38030539214469896866301849 28522904410852422649726387)
        ·
          refine ⟨42784356616278633974589581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28522904410852422649726387 42784356616278633974589581)
          ·
            refine ⟨16044133731104487740471093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42784356616278633974589581 16044133731104487740471093)
            ·
              refine ⟨1504137537291045725669165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16044133731104487740471093 1504137537291045725669165)
              ·
                refine ⟨564051576484142147125937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1504137537291045725669165 564051576484142147125937)
                ·
                  refine ⟨423038682363106610344453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564051576484142147125937 423038682363106610344453)
                  ·
                    rfl

theorem cell20_926848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 2].length) (baseStart_926848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926848 prefixEnd_926848 := by exact prefixLift 926848
  have htrace : WordTrace (prefixWord ++ tailWord_926848) baseStart_926848 baseEnd_926848 := by
    simpa [prefixWord, tailWord_926848, baseEnd_926848] using wordTrace_append hprefix tailTrace_926848
  have hstable : (prefixWord ++ tailWord_926848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926848).length < 2 ^ (prefixWord ++ tailWord_926848).sum := by decide
  have hdescent : baseEnd_926848 < baseStart_926848 := by decide
  rcases family_descends (prefixWord ++ tailWord_926848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926862 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_926862 : Nat := 118140960795 + 926862 * 2 ^ 59
def prefixEnd_926862 : Nat := 4983230072969 + 3 ^ 40 * 926862 * 2
def baseEnd_926862 : Nat := 423045072344584783877729

theorem tailTrace_926862 : CollatzResearch.WordTrace tailWord_926862 prefixEnd_926862 423045072344584783877729 := by
  unfold tailWord_926862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4225679296018093034020855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22536956245429829514777893 4225679296018093034020855)
  ·
    refine ⟨6338518944027139551031283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4225679296018093034020855 6338518944027139551031283)
    ·
      refine ⟨9507778416040709326546925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6338518944027139551031283 9507778416040709326546925)
      ·
        refine ⟨3565416906015265997455097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9507778416040709326546925 3565416906015265997455097)
        ·
          refine ⟨2674062679511449498091323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3565416906015265997455097 2674062679511449498091323)
          ·
            refine ⟨4011094019267174247136985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2674062679511449498091323 4011094019267174247136985)
            ·
              refine ⟨3008320514450380685352739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4011094019267174247136985 3008320514450380685352739)
              ·
                refine ⟨4512480771675571028029109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3008320514450380685352739 4512480771675571028029109)
                ·
                  refine ⟨423045072344584783877729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4512480771675571028029109 423045072344584783877729)
                  ·
                    rfl

theorem cell20_926862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_926862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926862 prefixEnd_926862 := by exact prefixLift 926862
  have htrace : WordTrace (prefixWord ++ tailWord_926862) baseStart_926862 baseEnd_926862 := by
    simpa [prefixWord, tailWord_926862, baseEnd_926862] using wordTrace_append hprefix tailTrace_926862
  have hstable : (prefixWord ++ tailWord_926862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926862).length < 2 ^ (prefixWord ++ tailWord_926862).sum := by decide
  have hdescent : baseEnd_926862 < baseStart_926862 := by decide
  rcases family_descends (prefixWord ++ tailWord_926862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926876 : List Nat := [2, 2, 3, 2, 1, 2, 1, 7]
def baseStart_926876 : Nat := 118140960795 + 926876 * 2 ^ 59
def prefixEnd_926876 : Nat := 4983230072969 + 3 ^ 40 * 926876 * 2
def baseEnd_926876 : Nat := 141017154108687652470335

theorem tailTrace_926876 : CollatzResearch.WordTrace tailWord_926876 prefixEnd_926876 141017154108687652470335 := by
  unfold tailWord_926876
  simp only [CollatzResearch.WordTrace]
  refine ⟨16902972495047012331588241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22537296660062683108784321 16902972495047012331588241)
  ·
    refine ⟨12677229371285259248691181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16902972495047012331588241 12677229371285259248691181)
    ·
      refine ⟨4753961014231972218259193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12677229371285259248691181 4753961014231972218259193)
      ·
        refine ⟨3565470760673979163694395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4753961014231972218259193 3565470760673979163694395)
        ·
          refine ⟨5348206141010968745541593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3565470760673979163694395 5348206141010968745541593)
          ·
            refine ⟨4011154605758226559156195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5348206141010968745541593 4011154605758226559156195)
            ·
              refine ⟨6016731908637339838734293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4011154605758226559156195 6016731908637339838734293)
              ·
                refine ⟨141017154108687652470335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6016731908637339838734293 141017154108687652470335)
                ·
                  rfl

theorem cell20_926876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_926876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926876 prefixEnd_926876 := by exact prefixLift 926876
  have htrace : WordTrace (prefixWord ++ tailWord_926876) baseStart_926876 baseEnd_926876 := by
    simpa [prefixWord, tailWord_926876, baseEnd_926876] using wordTrace_append hprefix tailTrace_926876
  have hstable : (prefixWord ++ tailWord_926876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926876).length < 2 ^ (prefixWord ++ tailWord_926876).sum := by decide
  have hdescent : baseEnd_926876 < baseStart_926876 := by decide
  rcases family_descends (prefixWord ++ tailWord_926876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926879 : List Nat := [1, 1, 2, 6, 2, 1, 1, 3, 3]
def baseStart_926879 : Nat := 118140960795 + 926879 * 2 ^ 59
def prefixEnd_926879 : Nat := 4983230072969 + 3 ^ 40 * 926879 * 2
def baseEnd_926879 : Nat := 423052831607808280310993

theorem tailTrace_926879 : CollatzResearch.WordTrace tailWord_926879 prefixEnd_926879 423052831607808280310993 := by
  unfold tailWord_926879
  simp only [CollatzResearch.WordTrace]
  refine ⟨33806054409083156175535691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22537369606055437450357127 33806054409083156175535691)
  ·
    refine ⟨50709081613624734263303537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33806054409083156175535691 50709081613624734263303537)
    ·
      refine ⟨38031811210218550697477653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50709081613624734263303537 38031811210218550697477653)
      ·
        refine ⟨1782741150478994563944265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38031811210218550697477653 1782741150478994563944265)
        ·
          refine ⟨1337055862859245922958199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1782741150478994563944265 1337055862859245922958199)
          ·
            refine ⟨2005583794288868884437299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337055862859245922958199 2005583794288868884437299)
            ·
              refine ⟨3008375691433303326655949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005583794288868884437299 3008375691433303326655949)
              ·
                refine ⟨1128140884287488747495981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008375691433303326655949 1128140884287488747495981)
                ·
                  refine ⟨423052831607808280310993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128140884287488747495981 423052831607808280310993)
                  ·
                    rfl

theorem cell20_926879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 3].length) (baseStart_926879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926879 prefixEnd_926879 := by exact prefixLift 926879
  have htrace : WordTrace (prefixWord ++ tailWord_926879) baseStart_926879 baseEnd_926879 := by
    simpa [prefixWord, tailWord_926879, baseEnd_926879] using wordTrace_append hprefix tailTrace_926879
  have hstable : (prefixWord ++ tailWord_926879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926879).length < 2 ^ (prefixWord ++ tailWord_926879).sum := by decide
  have hdescent : baseEnd_926879 < baseStart_926879 := by decide
  rcases family_descends (prefixWord ++ tailWord_926879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926945 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_926945 : Nat := 118140960795 + 926945 * 2 ^ 59
def prefixEnd_926945 : Nat := 4983230072969 + 3 ^ 40 * 926945 * 2
def baseEnd_926945 : Nat := 423082955806205384110723

theorem tailTrace_926945 : CollatzResearch.WordTrace tailWord_926945 prefixEnd_926945 423082955806205384110723 := by
  unfold tailWord_926945
  simp only [CollatzResearch.WordTrace]
  refine ⟨33808461626844049447438289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22538974417896032964958859 33808461626844049447438289)
  ·
    refine ⟨25356346220133037085578717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33808461626844049447438289 25356346220133037085578717)
    ·
      refine ⟨9508629832549888907092019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25356346220133037085578717 9508629832549888907092019)
      ·
        refine ⟨14262944748824833360638029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508629832549888907092019 14262944748824833360638029)
        ·
          refine ⟨5348604280809312510239261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14262944748824833360638029 5348604280809312510239261)
          ·
            refine ⟨2005726605303492191339723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5348604280809312510239261 2005726605303492191339723)
            ·
              refine ⟨3008589907955238287009585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005726605303492191339723 3008589907955238287009585)
              ·
                refine ⟨2256442430966428715257189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3008589907955238287009585 2256442430966428715257189)
                ·
                  refine ⟨423082955806205384110723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2256442430966428715257189 423082955806205384110723)
                  ·
                    rfl

theorem cell20_926945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_926945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926945 prefixEnd_926945 := by exact prefixLift 926945
  have htrace : WordTrace (prefixWord ++ tailWord_926945) baseStart_926945 baseEnd_926945 := by
    simpa [prefixWord, tailWord_926945, baseEnd_926945] using wordTrace_append hprefix tailTrace_926945
  have hstable : (prefixWord ++ tailWord_926945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926945).length < 2 ^ (prefixWord ++ tailWord_926945).sum := by decide
  have hdescent : baseEnd_926945 < baseStart_926945 := by decide
  rcases family_descends (prefixWord ++ tailWord_926945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_926972 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_926972 : Nat := 118140960795 + 926972 * 2 ^ 59
def prefixEnd_926972 : Nat := 4983230072969 + 3 ^ 40 * 926972 * 2
def baseEnd_926972 : Nat := 423095279341913290210613

theorem tailTrace_926972 : CollatzResearch.WordTrace tailWord_926972 prefixEnd_926972 423095279341913290210613 := by
  unfold tailWord_926972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16904723198873116529335585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22539630931830822039114113 16904723198873116529335585)
  ·
    refine ⟨12678542399154837397001689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16904723198873116529335585 12678542399154837397001689)
    ·
      refine ⟨9508906799366128047751267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12678542399154837397001689 9508906799366128047751267)
      ·
        refine ⟨14263360199049192071626901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9508906799366128047751267 14263360199049192071626901)
        ·
          refine ⟨668595009330430878357511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14263360199049192071626901 668595009330430878357511)
          ·
            refine ⟨1002892513995646317536267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 668595009330430878357511 1002892513995646317536267)
            ·
              refine ⟨1504338770993469476304401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1002892513995646317536267 1504338770993469476304401)
              ·
                refine ⟨1128254078245102107228301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504338770993469476304401 1128254078245102107228301)
                ·
                  refine ⟨423095279341913290210613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128254078245102107228301 423095279341913290210613)
                  ·
                    rfl

theorem cell20_926972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_926972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_926972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_926972 prefixEnd_926972 := by exact prefixLift 926972
  have htrace : WordTrace (prefixWord ++ tailWord_926972) baseStart_926972 baseEnd_926972 := by
    simpa [prefixWord, tailWord_926972, baseEnd_926972] using wordTrace_append hprefix tailTrace_926972
  have hstable : (prefixWord ++ tailWord_926972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_926972).length < 2 ^ (prefixWord ++ tailWord_926972).sum := by decide
  have hdescent : baseEnd_926972 < baseStart_926972 := by decide
  rcases family_descends (prefixWord ++ tailWord_926972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927049 : List Nat := [1, 2, 1, 1, 2, 3, 3, 7]
def baseStart_927049 : Nat := 118140960795 + 927049 * 2 ^ 59
def prefixEnd_927049 : Nat := 4983230072969 + 3 ^ 40 * 927049 * 2
def baseEnd_927049 : Nat := 141043474746681081547877

theorem tailTrace_927049 : CollatzResearch.WordTrace tailWord_927049 prefixEnd_927049 141043474746681081547877 := by
  unfold tailWord_927049
  simp only [CollatzResearch.WordTrace]
  refine ⟨33812254818467275209224201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22541503212311516806149467 33812254818467275209224201)
  ·
    refine ⟨25359191113850456406918151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33812254818467275209224201 25359191113850456406918151)
    ·
      refine ⟨38038786670775684610377227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25359191113850456406918151 38038786670775684610377227)
      ·
        refine ⟨57058180006163526915565841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38038786670775684610377227 57058180006163526915565841)
        ·
          refine ⟨42793635004622645186674381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57058180006163526915565841 42793635004622645186674381)
          ·
            refine ⟨16047613126733491945002893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42793635004622645186674381 16047613126733491945002893)
            ·
              refine ⟨6017854922525059479376085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16047613126733491945002893 6017854922525059479376085)
              ·
                refine ⟨141043474746681081547877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6017854922525059479376085 141043474746681081547877)
                ·
                  rfl

theorem cell20_927049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_927049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927049 prefixEnd_927049 := by exact prefixLift 927049
  have htrace : WordTrace (prefixWord ++ tailWord_927049) baseStart_927049 baseEnd_927049 := by
    simpa [prefixWord, tailWord_927049, baseEnd_927049] using wordTrace_append hprefix tailTrace_927049
  have hstable : (prefixWord ++ tailWord_927049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927049).length < 2 ^ (prefixWord ++ tailWord_927049).sum := by decide
  have hdescent : baseEnd_927049 < baseStart_927049 := by decide
  rcases family_descends (prefixWord ++ tailWord_927049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927052 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_927052 : Nat := 118140960795 + 927052 * 2 ^ 59
def prefixEnd_927052 : Nat := 4983230072969 + 3 ^ 40 * 927052 * 2
def baseEnd_927052 : Nat := 423131793521788567543619

theorem tailTrace_927052 : CollatzResearch.WordTrace tailWord_927052 prefixEnd_927052 423131793521788567543619 := by
  unfold tailWord_927052
  simp only [CollatzResearch.WordTrace]
  refine ⟨16906182118728203360791705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22541576158304271147722273 16906182118728203360791705)
  ·
    refine ⟨12679636589046152520593779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16906182118728203360791705 12679636589046152520593779)
    ·
      refine ⟨19019454883569228780890669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12679636589046152520593779 19019454883569228780890669)
      ·
        refine ⟨7132295581338460792834001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19019454883569228780890669 7132295581338460792834001)
        ·
          refine ⟨5349221686003845594625501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7132295581338460792834001 5349221686003845594625501)
          ·
            refine ⟨2005958132251442097984563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5349221686003845594625501 2005958132251442097984563)
            ·
              refine ⟨3008937198377163146976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2005958132251442097984563 3008937198377163146976845)
              ·
                refine ⟨1128351449391436180116317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3008937198377163146976845 1128351449391436180116317)
                ·
                  refine ⟨423131793521788567543619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128351449391436180116317 423131793521788567543619)
                  ·
                    rfl

theorem cell20_927052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_927052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927052 prefixEnd_927052 := by exact prefixLift 927052
  have htrace : WordTrace (prefixWord ++ tailWord_927052) baseStart_927052 baseEnd_927052 := by
    simpa [prefixWord, tailWord_927052, baseEnd_927052] using wordTrace_append hprefix tailTrace_927052
  have hstable : (prefixWord ++ tailWord_927052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927052).length < 2 ^ (prefixWord ++ tailWord_927052).sum := by decide
  have hdescent : baseEnd_927052 < baseStart_927052 := by decide
  rcases family_descends (prefixWord ++ tailWord_927052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927086 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_927086 : Nat := 118140960795 + 927086 * 2 ^ 59
def prefixEnd_927086 : Nat := 4983230072969 + 3 ^ 40 * 927086 * 2
def baseEnd_927086 : Nat := 423147312048235560410147

theorem tailTrace_927086 : CollatzResearch.WordTrace tailWord_927086 prefixEnd_927086 423147312048235560410147 := by
  unfold tailWord_927086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4226700539916653816040139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22542402879555487018880741 4226700539916653816040139)
  ·
    refine ⟨6340050809874980724060209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4226700539916653816040139 6340050809874980724060209)
    ·
      refine ⟨4755038107406235543045157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6340050809874980724060209 4755038107406235543045157)
      ·
        refine ⟨891569645138669164320967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4755038107406235543045157 891569645138669164320967)
        ·
          refine ⟨1337354467708003746481451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891569645138669164320967 1337354467708003746481451)
          ·
            refine ⟨2006031701562005619722177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337354467708003746481451 2006031701562005619722177)
            ·
              refine ⟨1504523776171504214791633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2006031701562005619722177 1504523776171504214791633)
              ·
                refine ⟨1128392832128628161093725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504523776171504214791633 1128392832128628161093725)
                ·
                  refine ⟨423147312048235560410147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128392832128628161093725 423147312048235560410147)
                  ·
                    rfl

theorem cell20_927086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_927086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927086 prefixEnd_927086 := by exact prefixLift 927086
  have htrace : WordTrace (prefixWord ++ tailWord_927086) baseStart_927086 baseEnd_927086 := by
    simpa [prefixWord, tailWord_927086, baseEnd_927086] using wordTrace_append hprefix tailTrace_927086
  have hstable : (prefixWord ++ tailWord_927086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927086).length < 2 ^ (prefixWord ++ tailWord_927086).sum := by decide
  have hdescent : baseEnd_927086 < baseStart_927086 := by decide
  rcases family_descends (prefixWord ++ tailWord_927086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927090 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 3]
def baseStart_927090 : Nat := 118140960795 + 927090 * 2 ^ 59
def prefixEnd_927090 : Nat := 4983230072969 + 3 ^ 40 * 927090 * 2
def baseEnd_927090 : Nat := 423149137757229324276797

theorem tailTrace_927090 : CollatzResearch.WordTrace tailWord_927090 prefixEnd_927090 423149137757229324276797 := by
  unfold tailWord_927090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8453437552829684802866681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22542500140879159474311149 8453437552829684802866681)
  ·
    refine ⟨6340078164622263602150011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8453437552829684802866681 6340078164622263602150011)
    ·
      refine ⟨9510117246933395403225017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340078164622263602150011 9510117246933395403225017)
      ·
        refine ⟨7132587935200046552418763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9510117246933395403225017 7132587935200046552418763)
        ·
          refine ⟨10698881902800069828628145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7132587935200046552418763 10698881902800069828628145)
          ·
            refine ⟨8024161427100052371471109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10698881902800069828628145 8024161427100052371471109)
            ·
              refine ⟨1504530267581259819650833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8024161427100052371471109 1504530267581259819650833)
              ·
                refine ⟨1128397700685944864738125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1504530267581259819650833 1128397700685944864738125)
                ·
                  refine ⟨423149137757229324276797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128397700685944864738125 423149137757229324276797)
                  ·
                    rfl

theorem cell20_927090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_927090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927090 prefixEnd_927090 := by exact prefixLift 927090
  have htrace : WordTrace (prefixWord ++ tailWord_927090) baseStart_927090 baseEnd_927090 := by
    simpa [prefixWord, tailWord_927090, baseEnd_927090] using wordTrace_append hprefix tailTrace_927090
  have hstable : (prefixWord ++ tailWord_927090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927090).length < 2 ^ (prefixWord ++ tailWord_927090).sum := by decide
  have hdescent : baseEnd_927090 < baseStart_927090 := by decide
  rcases family_descends (prefixWord ++ tailWord_927090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927093 : List Nat := [1, 3, 4, 1, 3, 1, 1, 4, 2]
def baseStart_927093 : Nat := 118140960795 + 927093 * 2 ^ 59
def prefixEnd_927093 : Nat := 4983230072969 + 3 ^ 40 * 927093 * 2
def baseEnd_927093 : Nat := 423150507038974647176785

theorem tailTrace_927093 : CollatzResearch.WordTrace tailWord_927093 prefixEnd_927093 423150507038974647176785 := by
  unfold tailWord_927093
  simp only [CollatzResearch.WordTrace]
  refine ⟨33813859630307870723825933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22542573086871913815883955 33813859630307870723825933)
  ·
    refine ⟨12680197361365451521434725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33813859630307870723825933 12680197361365451521434725)
    ·
      refine ⟨2377537005256022160269011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12680197361365451521434725 2377537005256022160269011)
      ·
        refine ⟨3566305507884033240403517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2377537005256022160269011 3566305507884033240403517)
        ·
          refine ⟨1337364565456512465151319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3566305507884033240403517 1337364565456512465151319)
          ·
            refine ⟨2006046848184768697726979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337364565456512465151319 2006046848184768697726979)
            ·
              refine ⟨3009070272277153046590469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006046848184768697726979 3009070272277153046590469)
              ·
                refine ⟨564200676051966196235713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3009070272277153046590469 564200676051966196235713)
                ·
                  refine ⟨423150507038974647176785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564200676051966196235713 423150507038974647176785)
                  ·
                    rfl

theorem cell20_927093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_927093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927093 prefixEnd_927093 := by exact prefixLift 927093
  have htrace : WordTrace (prefixWord ++ tailWord_927093) baseStart_927093 baseEnd_927093 := by
    simpa [prefixWord, tailWord_927093, baseEnd_927093] using wordTrace_append hprefix tailTrace_927093
  have hstable : (prefixWord ++ tailWord_927093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927093).length < 2 ^ (prefixWord ++ tailWord_927093).sum := by decide
  have hdescent : baseEnd_927093 < baseStart_927093 := by decide
  rcases family_descends (prefixWord ++ tailWord_927093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927125 : List Nat := [1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_927125 : Nat := 118140960795 + 927125 * 2 ^ 59
def prefixEnd_927125 : Nat := 4983230072969 + 3 ^ 40 * 927125 * 2
def baseEnd_927125 : Nat := 141055037570308252703329

theorem tailTrace_927125 : CollatzResearch.WordTrace tailWord_927125 prefixEnd_927125 141055037570308252703329 := by
  unfold tailWord_927125
  simp only [CollatzResearch.WordTrace]
  refine ⟨33815026766191940188990829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22543351177461293459327219 33815026766191940188990829)
  ·
    refine ⟨12680635037321977570871561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33815026766191940188990829 12680635037321977570871561)
    ·
      refine ⟨9510476277991483178153671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12680635037321977570871561 9510476277991483178153671)
      ·
        refine ⟨14265714416987224767230507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9510476277991483178153671 14265714416987224767230507)
        ·
          refine ⟨21398571625480837150845761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14265714416987224767230507 21398571625480837150845761)
          ·
            refine ⟨16048928719110627863134321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21398571625480837150845761 16048928719110627863134321)
            ·
              refine ⟨12036696539332970897350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16048928719110627863134321 12036696539332970897350741)
              ·
                refine ⟨141055037570308252703329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12036696539332970897350741 141055037570308252703329)
                ·
                  rfl

theorem cell20_927125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_927125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927125 prefixEnd_927125 := by exact prefixLift 927125
  have htrace : WordTrace (prefixWord ++ tailWord_927125) baseStart_927125 baseEnd_927125 := by
    simpa [prefixWord, tailWord_927125, baseEnd_927125] using wordTrace_append hprefix tailTrace_927125
  have hstable : (prefixWord ++ tailWord_927125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927125).length < 2 ^ (prefixWord ++ tailWord_927125).sum := by decide
  have hdescent : baseEnd_927125 < baseStart_927125 := by decide
  rcases family_descends (prefixWord ++ tailWord_927125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927180 : List Nat := [2, 2, 1, 4, 2, 2, 1, 6]
def baseStart_927180 : Nat := 118140960795 + 927180 * 2 ^ 59
def prefixEnd_927180 : Nat := 4983230072969 + 3 ^ 40 * 927180 * 2
def baseEnd_927180 : Nat := 141063405403196337092143

theorem tailTrace_927180 : CollatzResearch.WordTrace tailWord_927180 prefixEnd_927180 141063405403196337092143 := by
  unfold tailWord_927180
  simp only [CollatzResearch.WordTrace]
  refine ⟨16908516390496342291121497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22544688520661789721495329 16908516390496342291121497)
  ·
    refine ⟨12681387292872256718341123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16908516390496342291121497 12681387292872256718341123)
    ·
      refine ⟨19022080939308385077511685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12681387292872256718341123 19022080939308385077511685)
      ·
        refine ⟨3566640176120322202033441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19022080939308385077511685 3566640176120322202033441)
        ·
          refine ⟨2674980132090241651525081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3566640176120322202033441 2674980132090241651525081)
          ·
            refine ⟨2006235099067681238643811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2674980132090241651525081 2006235099067681238643811)
            ·
              refine ⟨3009352648601521857965717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006235099067681238643811 3009352648601521857965717)
              ·
                refine ⟨141063405403196337092143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009352648601521857965717 141063405403196337092143)
                ·
                  rfl

theorem cell20_927180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 6].length) (baseStart_927180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927180 prefixEnd_927180 := by exact prefixLift 927180
  have htrace : WordTrace (prefixWord ++ tailWord_927180) baseStart_927180 baseEnd_927180 := by
    simpa [prefixWord, tailWord_927180, baseEnd_927180] using wordTrace_append hprefix tailTrace_927180
  have hstable : (prefixWord ++ tailWord_927180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927180).length < 2 ^ (prefixWord ++ tailWord_927180).sum := by decide
  have hdescent : baseEnd_927180 < baseStart_927180 := by decide
  rcases family_descends (prefixWord ++ tailWord_927180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927201 : List Nat := [1, 2, 3, 1, 2, 3, 8]
def baseStart_927201 : Nat := 118140960795 + 927201 * 2 ^ 59
def prefixEnd_927201 : Nat := 4983230072969 + 3 ^ 40 * 927201 * 2
def baseEnd_927201 : Nat := 47022200131311807952927

theorem tailTrace_927201 : CollatzResearch.WordTrace tailWord_927201 prefixEnd_927201 47022200131311807952927 := by
  unfold tailWord_927201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33817798713916605168757457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22545199142611070112504971 33817798713916605168757457)
  ·
    refine ⟨25363349035437453876568093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33817798713916605168757457 25363349035437453876568093)
    ·
      refine ⟨9511255888289045203713035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25363349035437453876568093 9511255888289045203713035)
      ·
        refine ⟨14266883832433567805569553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9511255888289045203713035 14266883832433567805569553)
        ·
          refine ⟨10700162874325175854177165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14266883832433567805569553 10700162874325175854177165)
          ·
            refine ⟨4012561077871940945316437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10700162874325175854177165 4012561077871940945316437)
            ·
              refine ⟨47022200131311807952927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4012561077871940945316437 47022200131311807952927)
              ·
                rfl

theorem cell20_927201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 8].length) (baseStart_927201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927201 prefixEnd_927201 := by exact prefixLift 927201
  have htrace : WordTrace (prefixWord ++ tailWord_927201) baseStart_927201 baseEnd_927201 := by
    simpa [prefixWord, tailWord_927201, baseEnd_927201] using wordTrace_append hprefix tailTrace_927201
  have hstable : (prefixWord ++ tailWord_927201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927201).length < 2 ^ (prefixWord ++ tailWord_927201).sum := by decide
  have hdescent : baseEnd_927201 < baseStart_927201 := by decide
  rcases family_descends (prefixWord ++ tailWord_927201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927207 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 2]
def baseStart_927207 : Nat := 118140960795 + 927207 * 2 ^ 59
def prefixEnd_927207 : Nat := 4983230072969 + 3 ^ 40 * 927207 * 2
def baseEnd_927207 : Nat := 423202539745296917376319

theorem tailTrace_927207 : CollatzResearch.WordTrace tailWord_927207 prefixEnd_927207 423202539745296917376319 := by
  unfold tailWord_927207
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818017551894868193475875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22545345034596578795650583 33818017551894868193475875)
  ·
    refine ⟨50727026327842302290213813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33818017551894868193475875 50727026327842302290213813)
    ·
      refine ⟨4755658718235215839707545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50727026327842302290213813 4755658718235215839707545)
      ·
        refine ⟨3566744038676411879780659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4755658718235215839707545 3566744038676411879780659)
        ·
          refine ⟨5350116058014617819670989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3566744038676411879780659 5350116058014617819670989)
          ·
            refine ⟨2006293521755481682376621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5350116058014617819670989 2006293521755481682376621)
            ·
              refine ⟨752360070658305630891233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2006293521755481682376621 752360070658305630891233)
              ·
                refine ⟨564270052993729223168425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752360070658305630891233 564270052993729223168425)
                ·
                  refine ⟨423202539745296917376319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564270052993729223168425 423202539745296917376319)
                  ·
                    rfl

theorem cell20_927207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 2].length) (baseStart_927207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927207 prefixEnd_927207 := by exact prefixLift 927207
  have htrace : WordTrace (prefixWord ++ tailWord_927207) baseStart_927207 baseEnd_927207 := by
    simpa [prefixWord, tailWord_927207, baseEnd_927207] using wordTrace_append hprefix tailTrace_927207
  have hstable : (prefixWord ++ tailWord_927207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927207).length < 2 ^ (prefixWord ++ tailWord_927207).sum := by decide
  have hdescent : baseEnd_927207 < baseStart_927207 := by decide
  rcases family_descends (prefixWord ++ tailWord_927207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927218 : List Nat := [3, 2, 1, 4, 1, 1, 1, 7]
def baseStart_927218 : Nat := 118140960795 + 927218 * 2 ^ 59
def prefixEnd_927218 : Nat := 4983230072969 + 3 ^ 40 * 927218 * 2
def baseEnd_927218 : Nat := 141069186815009922669869

theorem tailTrace_927218 : CollatzResearch.WordTrace tailWord_927218 prefixEnd_927218 141069186815009922669869 := by
  unfold tailWord_927218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8454604688713754268031577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22545612503236678048084205 8454604688713754268031577)
  ·
    refine ⟨6340953516535315701023683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8454604688713754268031577 6340953516535315701023683)
    ·
      refine ⟨9511430274802973551535525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6340953516535315701023683 9511430274802973551535525)
      ·
        refine ⟨1783393176525557540912911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9511430274802973551535525 1783393176525557540912911)
        ·
          refine ⟨2675089764788336311369367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783393176525557540912911 2675089764788336311369367)
          ·
            refine ⟨4012634647182504467054051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675089764788336311369367 4012634647182504467054051)
            ·
              refine ⟨6018951970773756700581077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4012634647182504467054051 6018951970773756700581077)
              ·
                refine ⟨141069186815009922669869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6018951970773756700581077 141069186815009922669869)
                ·
                  rfl

theorem cell20_927218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_927218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927218 prefixEnd_927218 := by exact prefixLift 927218
  have htrace : WordTrace (prefixWord ++ tailWord_927218) baseStart_927218 baseEnd_927218 := by
    simpa [prefixWord, tailWord_927218, baseEnd_927218] using wordTrace_append hprefix tailTrace_927218
  have hstable : (prefixWord ++ tailWord_927218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927218).length < 2 ^ (prefixWord ++ tailWord_927218).sum := by decide
  have hdescent : baseEnd_927218 < baseStart_927218 := by decide
  rcases family_descends (prefixWord ++ tailWord_927218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927221 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 3]
def baseStart_927221 : Nat := 118140960795 + 927221 * 2 ^ 59
def prefixEnd_927221 : Nat := 4983230072969 + 3 ^ 40 * 927221 * 2
def baseEnd_927221 : Nat := 423208929726775090909595

theorem tailTrace_927221 : CollatzResearch.WordTrace tailWord_927221 prefixEnd_927221 423208929726775090909595 := by
  unfold tailWord_927221
  simp only [CollatzResearch.WordTrace]
  refine ⟨33818528173844148584485517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22545685449229432389657011 33818528173844148584485517)
  ·
    refine ⟨12681948065191555719182069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33818528173844148584485517 12681948065191555719182069)
    ·
      refine ⟨1188932631111708348673319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12681948065191555719182069 1188932631111708348673319)
      ·
        refine ⟨1783398946667562523009979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1188932631111708348673319 1783398946667562523009979)
        ·
          refine ⟨2675098420001343784514969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783398946667562523009979 2675098420001343784514969)
          ·
            refine ⟨2006323815001007838386227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2675098420001343784514969 2006323815001007838386227)
            ·
              refine ⟨3009485722501511757579341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006323815001007838386227 3009485722501511757579341)
              ·
                refine ⟨1128557145938066909092253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3009485722501511757579341 1128557145938066909092253)
                ·
                  refine ⟨423208929726775090909595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128557145938066909092253 423208929726775090909595)
                  ·
                    rfl

theorem cell20_927221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_927221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927221 prefixEnd_927221 := by exact prefixLift 927221
  have htrace : WordTrace (prefixWord ++ tailWord_927221) baseStart_927221 baseEnd_927221 := by
    simpa [prefixWord, tailWord_927221, baseEnd_927221] using wordTrace_append hprefix tailTrace_927221
  have hstable : (prefixWord ++ tailWord_927221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927221).length < 2 ^ (prefixWord ++ tailWord_927221).sum := by decide
  have hdescent : baseEnd_927221 < baseStart_927221 := by decide
  rcases family_descends (prefixWord ++ tailWord_927221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927249 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 2]
def baseStart_927249 : Nat := 118140960795 + 927249 * 2 ^ 59
def prefixEnd_927249 : Nat := 4983230072969 + 3 ^ 40 * 927249 * 2
def baseEnd_927249 : Nat := 423221709689731437976147

theorem tailTrace_927249 : CollatzResearch.WordTrace tailWord_927249 prefixEnd_927249 423221709689731437976147 := by
  unfold tailWord_927249
  simp only [CollatzResearch.WordTrace]
  refine ⟨33819549417742709366504801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22546366278495139577669867 33819549417742709366504801)
  ·
    refine ⟨25364662063307032024878601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33819549417742709366504801 25364662063307032024878601)
    ·
      refine ⟨19023496547480274018658951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25364662063307032024878601 19023496547480274018658951)
      ·
        refine ⟨28535244821220411027988427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19023496547480274018658951 28535244821220411027988427)
        ·
          refine ⟨42802867231830616541982641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28535244821220411027988427 42802867231830616541982641)
          ·
            refine ⟨32102150423872962406486981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42802867231830616541982641 32102150423872962406486981)
            ·
              refine ⟨6019153204476180451216309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32102150423872962406486981 6019153204476180451216309)
              ·
                refine ⟨564295612919641917301529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6019153204476180451216309 564295612919641917301529)
                ·
                  refine ⟨423221709689731437976147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564295612919641917301529 423221709689731437976147)
                  ·
                    rfl

theorem cell20_927249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 2].length) (baseStart_927249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927249 prefixEnd_927249 := by exact prefixLift 927249
  have htrace : WordTrace (prefixWord ++ tailWord_927249) baseStart_927249 baseEnd_927249 := by
    simpa [prefixWord, tailWord_927249, baseEnd_927249] using wordTrace_append hprefix tailTrace_927249
  have hstable : (prefixWord ++ tailWord_927249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927249).length < 2 ^ (prefixWord ++ tailWord_927249).sum := by decide
  have hdescent : baseEnd_927249 < baseStart_927249 := by decide
  rcases family_descends (prefixWord ++ tailWord_927249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927256 : List Nat := [2, 1, 2, 3, 5, 7]
def baseStart_927256 : Nat := 118140960795 + 927256 * 2 ^ 59
def prefixEnd_927256 : Nat := 4983230072969 + 3 ^ 40 * 927256 * 2
def baseEnd_927256 : Nat := 15674996469647056471955

theorem tailTrace_927256 : CollatzResearch.WordTrace tailWord_927256 prefixEnd_927256 15674996469647056471955 := by
  unfold tailWord_927256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16909902364358674781004811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22546536485811566374673081 16909902364358674781004811)
  ·
    refine ⟨25364853546538012171507217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16909902364358674781004811 25364853546538012171507217)
    ·
      refine ⟨19023640159903509128630413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25364853546538012171507217 19023640159903509128630413)
      ·
        refine ⟨7133865059963815923236405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19023640159903509128630413 7133865059963815923236405)
        ·
          refine ⟨668799849371607742803413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7133865059963815923236405 668799849371607742803413)
          ·
            refine ⟨15674996469647056471955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 668799849371607742803413 15674996469647056471955)
            ·
              rfl

theorem cell20_927256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 7].length) (baseStart_927256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927256 prefixEnd_927256 := by exact prefixLift 927256
  have htrace : WordTrace (prefixWord ++ tailWord_927256) baseStart_927256 baseEnd_927256 := by
    simpa [prefixWord, tailWord_927256, baseEnd_927256] using wordTrace_append hprefix tailTrace_927256
  have hstable : (prefixWord ++ tailWord_927256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927256).length < 2 ^ (prefixWord ++ tailWord_927256).sum := by decide
  have hdescent : baseEnd_927256 < baseStart_927256 := by decide
  rcases family_descends (prefixWord ++ tailWord_927256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927263 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 3]
def baseStart_927263 : Nat := 118140960795 + 927263 * 2 ^ 59
def prefixEnd_927263 : Nat := 4983230072969 + 3 ^ 40 * 927263 * 2
def baseEnd_927263 : Nat := 423228099671209611509423

theorem tailTrace_927263 : CollatzResearch.WordTrace tailWord_927263 prefixEnd_927263 423228099671209611509423 := by
  unfold tailWord_927263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33820060039691989757514443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22546706693127993171676295 33820060039691989757514443)
  ·
    refine ⟨50730090059537984636271665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33820060039691989757514443 50730090059537984636271665)
    ·
      refine ⟨38047567544653488477203749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50730090059537984636271665 38047567544653488477203749)
      ·
        refine ⟨7133918914622529089475703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38047567544653488477203749 7133918914622529089475703)
        ·
          refine ⟨10700878371933793634213555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7133918914622529089475703 10700878371933793634213555)
          ·
            refine ⟨16051317557900690451320333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10700878371933793634213555 16051317557900690451320333)
            ·
              refine ⟨6019244084212758919245125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16051317557900690451320333 6019244084212758919245125)
              ·
                refine ⟨1128608265789892297358461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6019244084212758919245125 1128608265789892297358461)
                ·
                  refine ⟨423228099671209611509423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128608265789892297358461 423228099671209611509423)
                  ·
                    rfl

theorem cell20_927263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 3].length) (baseStart_927263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927263 prefixEnd_927263 := by exact prefixLift 927263
  have htrace : WordTrace (prefixWord ++ tailWord_927263) baseStart_927263 baseEnd_927263 := by
    simpa [prefixWord, tailWord_927263, baseEnd_927263] using wordTrace_append hprefix tailTrace_927263
  have hstable : (prefixWord ++ tailWord_927263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927263).length < 2 ^ (prefixWord ++ tailWord_927263).sum := by decide
  have hdescent : baseEnd_927263 < baseStart_927263 := by decide
  rcases family_descends (prefixWord ++ tailWord_927263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927349 : List Nat := [1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_927349 : Nat := 118140960795 + 927349 * 2 ^ 59
def prefixEnd_927349 : Nat := 4983230072969 + 3 ^ 40 * 927349 * 2
def baseEnd_927349 : Nat := 141089117471525178214135

theorem tailTrace_927349 : CollatzResearch.WordTrace tailWord_927349 prefixEnd_927349 141089117471525178214135 := by
  unfold tailWord_927349
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823196717380426445145101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22548797811586950963430067 33823196717380426445145101)
  ·
    refine ⟨12683698769017659916929413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33823196717380426445145101 12683698769017659916929413)
    ·
      refine ⟨2378193519190811234424265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12683698769017659916929413 2378193519190811234424265)
      ·
        refine ⟨1783645139393108425818199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2378193519190811234424265 1783645139393108425818199)
        ·
          refine ⟨2675467709089662638727299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1783645139393108425818199 2675467709089662638727299)
          ·
            refine ⟨4013201563634493958090949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2675467709089662638727299 4013201563634493958090949)
            ·
              refine ⟨752475293181467617142053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4013201563634493958090949 752475293181467617142053)
              ·
                refine ⟨141089117471525178214135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 752475293181467617142053 141089117471525178214135)
                ·
                  rfl

theorem cell20_927349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_927349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927349 prefixEnd_927349 := by exact prefixLift 927349
  have htrace : WordTrace (prefixWord ++ tailWord_927349) baseStart_927349 baseEnd_927349 := by
    simpa [prefixWord, tailWord_927349, baseEnd_927349] using wordTrace_append hprefix tailTrace_927349
  have hstable : (prefixWord ++ tailWord_927349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927349).length < 2 ^ (prefixWord ++ tailWord_927349).sum := by decide
  have hdescent : baseEnd_927349 < baseStart_927349 := by decide
  rcases family_descends (prefixWord ++ tailWord_927349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927353 : List Nat := [1, 2, 1, 3, 3, 1, 3, 6]
def baseStart_927353 : Nat := 118140960795 + 927353 * 2 ^ 59
def prefixEnd_927353 : Nat := 4983230072969 + 3 ^ 40 * 927353 * 2
def baseEnd_927353 : Nat := 141089726041189766169685

theorem tailTrace_927353 : CollatzResearch.WordTrace tailWord_927353 prefixEnd_927353 141089726041189766169685 := by
  unfold tailWord_927353
  simp only [CollatzResearch.WordTrace]
  refine ⟨33823342609365935128290713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22548895072910623418860475 33823342609365935128290713)
  ·
    refine ⟨25367506957024451346218035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33823342609365935128290713 25367506957024451346218035)
    ·
      refine ⟨38051260435536677019327053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25367506957024451346218035 38051260435536677019327053)
      ·
        refine ⟨14269222663326253882247645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38051260435536677019327053 14269222663326253882247645)
        ·
          refine ⟨5350958498747345205842867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14269222663326253882247645 5350958498747345205842867)
          ·
            refine ⟨8026437748121017808764301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5350958498747345205842867 8026437748121017808764301)
            ·
              refine ⟨3009914155545381678286613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8026437748121017808764301 3009914155545381678286613)
              ·
                refine ⟨141089726041189766169685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3009914155545381678286613 141089726041189766169685)
                ·
                  rfl

theorem cell20_927353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 6].length) (baseStart_927353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927353 prefixEnd_927353 := by exact prefixLift 927353
  have htrace : WordTrace (prefixWord ++ tailWord_927353) baseStart_927353 baseEnd_927353 := by
    simpa [prefixWord, tailWord_927353, baseEnd_927353] using wordTrace_append hprefix tailTrace_927353
  have hstable : (prefixWord ++ tailWord_927353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927353).length < 2 ^ (prefixWord ++ tailWord_927353).sum := by decide
  have hdescent : baseEnd_927353 < baseStart_927353 := by decide
  rcases family_descends (prefixWord ++ tailWord_927353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927360 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 7]
def baseStart_927360 : Nat := 118140960795 + 927360 * 2 ^ 59
def prefixEnd_927360 : Nat := 4983230072969 + 3 ^ 40 * 927360 * 2
def baseEnd_927360 : Nat := 423272373114308385275693

theorem tailTrace_927360 : CollatzResearch.WordTrace tailWord_927360 prefixEnd_927360 423272373114308385275693 := by
  unfold tailWord_927360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16911798960170287661897767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22549065280227050215863689 16911798960170287661897767)
  ·
    refine ⟨25367698440255431492846651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16911798960170287661897767 25367698440255431492846651)
    ·
      refine ⟨38051547660383147239269977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25367698440255431492846651 38051547660383147239269977)
      ·
        refine ⟨28538660745287360429452483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38051547660383147239269977 28538660745287360429452483)
        ·
          refine ⟨42807991117931040644178725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28538660745287360429452483 42807991117931040644178725)
          ·
            refine ⟨8026498334612070120783511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42807991117931040644178725 8026498334612070120783511)
            ·
              refine ⟨12039747501918105181175267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8026498334612070120783511 12039747501918105181175267)
              ·
                refine ⟨18059621252877157771762901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12039747501918105181175267 18059621252877157771762901)
                ·
                  refine ⟨423272373114308385275693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18059621252877157771762901 423272373114308385275693)
                  ·
                    rfl

theorem cell20_927360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_927360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927360 prefixEnd_927360 := by exact prefixLift 927360
  have htrace : WordTrace (prefixWord ++ tailWord_927360) baseStart_927360 baseEnd_927360 := by
    simpa [prefixWord, tailWord_927360, baseEnd_927360] using wordTrace_append hprefix tailTrace_927360
  have hstable : (prefixWord ++ tailWord_927360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927360).length < 2 ^ (prefixWord ++ tailWord_927360).sum := by decide
  have hdescent : baseEnd_927360 < baseStart_927360 := by decide
  rcases family_descends (prefixWord ++ tailWord_927360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927370 : List Nat := [3, 1, 2, 3, 2, 3, 6]
def baseStart_927370 : Nat := 118140960795 + 927370 * 2 ^ 59
def prefixEnd_927370 : Nat := 4983230072969 + 3 ^ 40 * 927370 * 2
def baseEnd_927370 : Nat := 47030770820754754993591

theorem tailTrace_927370 : CollatzResearch.WordTrace tailWord_927370 prefixEnd_927370 47030770820754754993591 := by
  unfold tailWord_927370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8455990662576086757914891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22549308433536231354439709 8455990662576086757914891)
  ·
    refine ⟨12683985993864130136872337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8455990662576086757914891 12683985993864130136872337)
    ·
      refine ⟨9512989495398097602654253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12683985993864130136872337 9512989495398097602654253)
      ·
        refine ⟨3567371060774286600995345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9512989495398097602654253 3567371060774286600995345)
        ·
          refine ⟨2675528295580714950746509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3567371060774286600995345 2675528295580714950746509)
          ·
            refine ⟨1003323110842768106529941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2675528295580714950746509 1003323110842768106529941)
            ·
              refine ⟨47030770820754754993591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1003323110842768106529941 47030770820754754993591)
              ·
                rfl

theorem cell20_927370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 6].length) (baseStart_927370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927370 prefixEnd_927370 := by exact prefixLift 927370
  have htrace : WordTrace (prefixWord ++ tailWord_927370) baseStart_927370 baseEnd_927370 := by
    simpa [prefixWord, tailWord_927370, baseEnd_927370] using wordTrace_append hprefix tailTrace_927370
  have hstable : (prefixWord ++ tailWord_927370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927370).length < 2 ^ (prefixWord ++ tailWord_927370).sum := by decide
  have hdescent : baseEnd_927370 < baseStart_927370 := by decide
  rcases family_descends (prefixWord ++ tailWord_927370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927390 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_927390 : Nat := 118140960795 + 927390 * 2 ^ 59
def prefixEnd_927390 : Nat := 4983230072969 + 3 ^ 40 * 927390 * 2
def baseEnd_927390 : Nat := 423286065931761614275571

theorem tailTrace_927390 : CollatzResearch.WordTrace tailWord_927390 prefixEnd_927390 423286065931761614275571 := by
  unfold tailWord_927390
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228086513778986305923453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22549794740154593631591749 4228086513778986305923453)
  ·
    refine ⟨1585532442667119864721295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4228086513778986305923453 1585532442667119864721295)
    ·
      refine ⟨2378298664000679797081943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1585532442667119864721295 2378298664000679797081943)
      ·
        refine ⟨3567447996001019695622915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2378298664000679797081943 3567447996001019695622915)
        ·
          refine ⟨5351171994001529543434373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3567447996001019695622915 5351171994001529543434373)
          ·
            refine ⟨1003344748875286789393945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5351171994001529543434373 1003344748875286789393945)
            ·
              refine ⟨752508561656465092045459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003344748875286789393945 752508561656465092045459)
              ·
                refine ⟨1128762842484697638068189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 752508561656465092045459 1128762842484697638068189)
                ·
                  refine ⟨423286065931761614275571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128762842484697638068189 423286065931761614275571)
                  ·
                    rfl

theorem cell20_927390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_927390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927390 prefixEnd_927390 := by exact prefixLift 927390
  have htrace : WordTrace (prefixWord ++ tailWord_927390) baseStart_927390 baseEnd_927390 := by
    simpa [prefixWord, tailWord_927390, baseEnd_927390] using wordTrace_append hprefix tailTrace_927390
  have hstable : (prefixWord ++ tailWord_927390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927390).length < 2 ^ (prefixWord ++ tailWord_927390).sum := by decide
  have hdescent : baseEnd_927390 < baseStart_927390 := by decide
  rcases family_descends (prefixWord ++ tailWord_927390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927460 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 4]
def baseStart_927460 : Nat := 118140960795 + 927460 * 2 ^ 59
def prefixEnd_927460 : Nat := 4983230072969 + 3 ^ 40 * 927460 * 2
def baseEnd_927460 : Nat := 423318015839152481941951

theorem tailTrace_927460 : CollatzResearch.WordTrace tailWord_927460 prefixEnd_927460 423318015839152481941951 := by
  unfold tailWord_927460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16913622609989146201217917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22551496813318861601623889 16913622609989146201217917)
  ·
    refine ⟨6342608478745929825456719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16913622609989146201217917 6342608478745929825456719)
    ·
      refine ⟨9513912718118894738185079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6342608478745929825456719 9513912718118894738185079)
      ·
        refine ⟨14270869077178342107277619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9513912718118894738185079 14270869077178342107277619)
        ·
          refine ⟨21406303615767513160916429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14270869077178342107277619 21406303615767513160916429)
          ·
            refine ⟨8027363855912817435343661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21406303615767513160916429 8027363855912817435343661)
            ·
              refine ⟨3010261445967306538253873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8027363855912817435343661 3010261445967306538253873)
              ·
                refine ⟨2257696084475479903690405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3010261445967306538253873 2257696084475479903690405)
                ·
                  refine ⟨423318015839152481941951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257696084475479903690405 423318015839152481941951)
                  ·
                    rfl

theorem cell20_927460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_927460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927460 prefixEnd_927460 := by exact prefixLift 927460
  have htrace : WordTrace (prefixWord ++ tailWord_927460) baseStart_927460 baseEnd_927460 := by
    simpa [prefixWord, tailWord_927460, baseEnd_927460] using wordTrace_append hprefix tailTrace_927460
  have hstable : (prefixWord ++ tailWord_927460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927460).length < 2 ^ (prefixWord ++ tailWord_927460).sum := by decide
  have hdescent : baseEnd_927460 < baseStart_927460 := by decide
  rcases family_descends (prefixWord ++ tailWord_927460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927491 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 3]
def baseStart_927491 : Nat := 118140960795 + 927491 * 2 ^ 59
def prefixEnd_927491 : Nat := 4983230072969 + 3 ^ 40 * 927491 * 2
def baseEnd_927491 : Nat := 423332165083854151908491

theorem tailTrace_927491 : CollatzResearch.WordTrace tailWord_927491 prefixEnd_927491 423332165083854151908491 := by
  unfold tailWord_927491
  simp only [CollatzResearch.WordTrace]
  refine ⟨33828375882865984696814327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22552250588577323131209551 33828375882865984696814327)
  ·
    refine ⟨50742563824298977045221491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33828375882865984696814327 50742563824298977045221491)
    ·
      refine ⟨76113845736448465567832237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50742563824298977045221491 76113845736448465567832237)
      ·
        refine ⟨28542692151168174587937089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76113845736448465567832237 28542692151168174587937089)
        ·
          refine ⟨21407019113376130940952817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28542692151168174587937089 21407019113376130940952817)
          ·
            refine ⟨16055264335032098205714613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21407019113376130940952817 16055264335032098205714613)
            ·
              refine ⟨1505181031409259206785745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16055264335032098205714613 1505181031409259206785745)
              ·
                refine ⟨1128885773556944405089309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505181031409259206785745 1128885773556944405089309)
                ·
                  refine ⟨423332165083854151908491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1128885773556944405089309 423332165083854151908491)
                  ·
                    rfl

theorem cell20_927491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 3].length) (baseStart_927491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927491 prefixEnd_927491 := by exact prefixLift 927491
  have htrace : WordTrace (prefixWord ++ tailWord_927491) baseStart_927491 baseEnd_927491 := by
    simpa [prefixWord, tailWord_927491, baseEnd_927491] using wordTrace_append hprefix tailTrace_927491
  have hstable : (prefixWord ++ tailWord_927491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927491).length < 2 ^ (prefixWord ++ tailWord_927491).sum := by decide
  have hdescent : baseEnd_927491 < baseStart_927491 := by decide
  rcases family_descends (prefixWord ++ tailWord_927491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927498 : List Nat := [3, 1, 2, 2, 1, 3, 1, 3, 4]
def baseStart_927498 : Nat := 118140960795 + 927498 * 2 ^ 59
def prefixEnd_927498 : Nat := 4983230072969 + 3 ^ 40 * 927498 * 2
def baseEnd_927498 : Nat := 423335360074593238675129

theorem tailTrace_927498 : CollatzResearch.WordTrace tailWord_927498 prefixEnd_927498 423335360074593238675129 := by
  unfold tailWord_927498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8457157798460156223079787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22552420795893749928212765 8457157798460156223079787)
  ·
    refine ⟨12685736697690234334619681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8457157798460156223079787 12685736697690234334619681)
    ·
      refine ⟨9514302523267675750964761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12685736697690234334619681 9514302523267675750964761)
      ·
        refine ⟨7135726892450756813223571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9514302523267675750964761 7135726892450756813223571)
        ·
          refine ⟨10703590338676135219835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7135726892450756813223571 10703590338676135219835357)
          ·
            refine ⟨4013846377003550707438259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10703590338676135219835357 4013846377003550707438259)
            ·
              refine ⟨6020769565505326061157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4013846377003550707438259 6020769565505326061157389)
              ·
                refine ⟨2257788587064497272934021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6020769565505326061157389 2257788587064497272934021)
                ·
                  refine ⟨423335360074593238675129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2257788587064497272934021 423335360074593238675129)
                  ·
                    rfl

theorem cell20_927498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_927498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927498 prefixEnd_927498 := by exact prefixLift 927498
  have htrace : WordTrace (prefixWord ++ tailWord_927498) baseStart_927498 baseEnd_927498 := by
    simpa [prefixWord, tailWord_927498, baseEnd_927498] using wordTrace_append hprefix tailTrace_927498
  have hstable : (prefixWord ++ tailWord_927498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927498).length < 2 ^ (prefixWord ++ tailWord_927498).sum := by decide
  have hdescent : baseEnd_927498 < baseStart_927498 := by decide
  rcases family_descends (prefixWord ++ tailWord_927498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927518 : List Nat := [4, 3, 2, 2, 1, 1, 1, 6]
def baseStart_927518 : Nat := 118140960795 + 927518 * 2 ^ 59
def prefixEnd_927518 : Nat := 4983230072969 + 3 ^ 40 * 927518 * 2
def baseEnd_927518 : Nat := 141114829539854019336127

theorem tailTrace_927518 : CollatzResearch.WordTrace tailWord_927518 prefixEnd_927518 141114829539854019336127 := by
  unfold tailWord_927518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228670081721021038505901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22552907102512112205364805 4228670081721021038505901)
  ·
    refine ⟨1585751280645382889439713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4228670081721021038505901 1585751280645382889439713)
    ·
      refine ⟨1189313460484037167079785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585751280645382889439713 1189313460484037167079785)
      ·
        refine ⟨891985095363027875309839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189313460484037167079785 891985095363027875309839)
        ·
          refine ⟨1337977643044541812964759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 891985095363027875309839 1337977643044541812964759)
          ·
            refine ⟨2006966464566812719447139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1337977643044541812964759 2006966464566812719447139)
            ·
              refine ⟨3010449696850219079170709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2006966464566812719447139 3010449696850219079170709)
              ·
                refine ⟨141114829539854019336127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3010449696850219079170709 141114829539854019336127)
                ·
                  rfl

theorem cell20_927518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_927518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927518 prefixEnd_927518 := by exact prefixLift 927518
  have htrace : WordTrace (prefixWord ++ tailWord_927518) baseStart_927518 baseEnd_927518 := by
    simpa [prefixWord, tailWord_927518, baseEnd_927518] using wordTrace_append hprefix tailTrace_927518
  have hstable : (prefixWord ++ tailWord_927518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927518).length < 2 ^ (prefixWord ++ tailWord_927518).sum := by decide
  have hdescent : baseEnd_927518 < baseStart_927518 := by decide
  rcases family_descends (prefixWord ++ tailWord_927518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927532 : List Nat := [2, 2, 1, 1, 1, 7, 1, 3, 2]
def baseStart_927532 : Nat := 118140960795 + 927532 * 2 ^ 59
def prefixEnd_927532 : Nat := 4983230072969 + 3 ^ 40 * 927532 * 2
def baseEnd_927532 : Nat := 423350878601040231541657

theorem tailTrace_927532 : CollatzResearch.WordTrace tailWord_927532 prefixEnd_927532 423350878601040231541657 := by
  unfold tailWord_927532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16914935637858724349528425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22553247517144965799371233 16914935637858724349528425)
  ·
    refine ⟨12686201728394043262146319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16914935637858724349528425 12686201728394043262146319)
    ·
      refine ⟨19029302592591064893219479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12686201728394043262146319 19029302592591064893219479)
      ·
        refine ⟨28543953888886597339829219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19029302592591064893219479 28543953888886597339829219)
        ·
          refine ⟨42815930833329896009743829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28543953888886597339829219 42815930833329896009743829)
          ·
            refine ⟨1003498378906169437728371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42815930833329896009743829 1003498378906169437728371)
            ·
              refine ⟨1505247568359254156592557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003498378906169437728371 1505247568359254156592557)
              ·
                refine ⟨564467838134720308722209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1505247568359254156592557 564467838134720308722209)
                ·
                  refine ⟨423350878601040231541657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564467838134720308722209 423350878601040231541657)
                  ·
                    rfl

theorem cell20_927532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 3, 2].length) (baseStart_927532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927532 prefixEnd_927532 := by exact prefixLift 927532
  have htrace : WordTrace (prefixWord ++ tailWord_927532) baseStart_927532 baseEnd_927532 := by
    simpa [prefixWord, tailWord_927532, baseEnd_927532] using wordTrace_append hprefix tailTrace_927532
  have hstable : (prefixWord ++ tailWord_927532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927532).length < 2 ^ (prefixWord ++ tailWord_927532).sum := by decide
  have hdescent : baseEnd_927532 < baseStart_927532 := by decide
  rcases family_descends (prefixWord ++ tailWord_927532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927549 : List Nat := [1, 4, 1, 4, 1, 2, 3, 2, 2]
def baseStart_927549 : Nat := 118140960795 + 927549 * 2 ^ 59
def prefixEnd_927549 : Nat := 4983230072969 + 3 ^ 40 * 927549 * 2
def baseEnd_927549 : Nat := 423358637864263727974921

theorem tailTrace_927549 : CollatzResearch.WordTrace tailWord_927549 prefixEnd_927549 423358637864263727974921 := by
  unfold tailWord_927549
  simp only [CollatzResearch.WordTrace]
  refine ⟨33830491316655860602425701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22553660877770573734950467 33830491316655860602425701)
  ·
    refine ⟨6343217121872973862954819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33830491316655860602425701 6343217121872973862954819)
    ·
      refine ⟨9514825682809460794432229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6343217121872973862954819 9514825682809460794432229)
      ·
        refine ⟨1784029815526773898956043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9514825682809460794432229 1784029815526773898956043)
        ·
          refine ⟨2676044723290160848434065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1784029815526773898956043 2676044723290160848434065)
          ·
            refine ⟨2007033542467620636325549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2676044723290160848434065 2007033542467620636325549)
            ·
              refine ⟨752637578425357738622081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2007033542467620636325549 752637578425357738622081)
              ·
                refine ⟨564478183819018303966561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752637578425357738622081 564478183819018303966561)
                ·
                  refine ⟨423358637864263727974921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564478183819018303966561 423358637864263727974921)
                  ·
                    rfl

theorem cell20_927549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_927549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927549 prefixEnd_927549 := by exact prefixLift 927549
  have htrace : WordTrace (prefixWord ++ tailWord_927549) baseStart_927549 baseEnd_927549 := by
    simpa [prefixWord, tailWord_927549, baseEnd_927549] using wordTrace_append hprefix tailTrace_927549
  have hstable : (prefixWord ++ tailWord_927549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927549).length < 2 ^ (prefixWord ++ tailWord_927549).sum := by decide
  have hdescent : baseEnd_927549 < baseStart_927549 := by decide
  rcases family_descends (prefixWord ++ tailWord_927549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927591 : List Nat := [1, 1, 5, 1, 2, 1, 2, 5, 2]
def baseStart_927591 : Nat := 118140960795 + 927591 * 2 ^ 59
def prefixEnd_927591 : Nat := 4983230072969 + 3 ^ 40 * 927591 * 2
def baseEnd_927591 : Nat := 423377807808698248574749

theorem tailTrace_927591 : CollatzResearch.WordTrace tailWord_927591 prefixEnd_927591 423377807808698248574749 := by
  unfold tailWord_927591
  simp only [CollatzResearch.WordTrace]
  refine ⟨33832023182503701775454627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22554682121669134516969751 33832023182503701775454627)
  ·
    refine ⟨50748034773755552663181941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33832023182503701775454627 50748034773755552663181941)
    ·
      refine ⟨4757628260039583062173307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50748034773755552663181941 4757628260039583062173307)
      ·
        refine ⟨7136442390059374593259961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4757628260039583062173307 7136442390059374593259961)
        ·
          refine ⟨5352331792544530944944971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7136442390059374593259961 5352331792544530944944971)
          ·
            refine ⟨8028497688816796417417457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5352331792544530944944971 8028497688816796417417457)
            ·
              refine ⟨6021373266612597313063093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8028497688816796417417457 6021373266612597313063093)
              ·
                refine ⟨564503743744930998099665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6021373266612597313063093 564503743744930998099665)
                ·
                  refine ⟨423377807808698248574749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564503743744930998099665 423377807808698248574749)
                  ·
                    rfl

theorem cell20_927591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 5, 2].length) (baseStart_927591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927591 prefixEnd_927591 := by exact prefixLift 927591
  have htrace : WordTrace (prefixWord ++ tailWord_927591) baseStart_927591 baseEnd_927591 := by
    simpa [prefixWord, tailWord_927591, baseEnd_927591] using wordTrace_append hprefix tailTrace_927591
  have hstable : (prefixWord ++ tailWord_927591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927591).length < 2 ^ (prefixWord ++ tailWord_927591).sum := by decide
  have hdescent : baseEnd_927591 < baseStart_927591 := by decide
  rcases family_descends (prefixWord ++ tailWord_927591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927619 : List Nat := [1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_927619 : Nat := 118140960795 + 927619 * 2 ^ 59
def prefixEnd_927619 : Nat := 4983230072969 + 3 ^ 40 * 927619 * 2
def baseEnd_927619 : Nat := 141130195923884865213767

theorem tailTrace_927619 : CollatzResearch.WordTrace tailWord_927619 prefixEnd_927619 141130195923884865213767 := by
  unfold tailWord_927619
  simp only [CollatzResearch.WordTrace]
  refine ⟨33833044426402262557473911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22555362950934841704982607 33833044426402262557473911)
  ·
    refine ⟨50749566639603393836210867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33833044426402262557473911 50749566639603393836210867)
    ·
      refine ⟨76124349959405090754316301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50749566639603393836210867 76124349959405090754316301)
      ·
        refine ⟨28546631234776909032868613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76124349959405090754316301 28546631234776909032868613)
        ·
          refine ⟨5352493356520670443662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28546631234776909032868613 5352493356520670443662865)
          ·
            refine ⟨4014370017390502832747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5352493356520670443662865 4014370017390502832747149)
            ·
              refine ⟨1505388756521438562280181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4014370017390502832747149 1505388756521438562280181)
              ·
                refine ⟨141130195923884865213767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505388756521438562280181 141130195923884865213767)
                ·
                  rfl

theorem cell20_927619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_927619 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927619 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927619 prefixEnd_927619 := by exact prefixLift 927619
  have htrace : WordTrace (prefixWord ++ tailWord_927619) baseStart_927619 baseEnd_927619 := by
    simpa [prefixWord, tailWord_927619, baseEnd_927619] using wordTrace_append hprefix tailTrace_927619
  have hstable : (prefixWord ++ tailWord_927619).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927619).length < 2 ^ (prefixWord ++ tailWord_927619).sum := by decide
  have hdescent : baseEnd_927619 < baseStart_927619 := by decide
  rcases family_descends (prefixWord ++ tailWord_927619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927633 : List Nat := [1, 2, 2, 1, 1, 1, 5, 1, 6]
def baseStart_927633 : Nat := 118140960795 + 927633 * 2 ^ 59
def prefixEnd_927633 : Nat := 4983230072969 + 3 ^ 40 * 927633 * 2
def baseEnd_927633 : Nat := 423396977753132769174577

theorem tailTrace_927633 : CollatzResearch.WordTrace tailWord_927633 prefixEnd_927633 423396977753132769174577 := by
  unfold tailWord_927633
  simp only [CollatzResearch.WordTrace]
  refine ⟨33833555048351542948483553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22555703365567695298989035 33833555048351542948483553)
  ·
    refine ⟨25375166286263657211362665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33833555048351542948483553 25375166286263657211362665)
    ·
      refine ⟨19031374714697742908521999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25375166286263657211362665 19031374714697742908521999)
      ·
        refine ⟨28547062072046614362782999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19031374714697742908521999 28547062072046614362782999)
        ·
          refine ⟨42820593108069921544174499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28547062072046614362782999 42820593108069921544174499)
          ·
            refine ⟨64230889662104882316261749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42820593108069921544174499 64230889662104882316261749)
            ·
              refine ⟨6021645905822332717149539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64230889662104882316261749 6021645905822332717149539)
              ·
                refine ⟨9032468858733499075724309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6021645905822332717149539 9032468858733499075724309)
                ·
                  refine ⟨423396977753132769174577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9032468858733499075724309 423396977753132769174577)
                  ·
                    rfl

theorem cell20_927633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_927633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927633 prefixEnd_927633 := by exact prefixLift 927633
  have htrace : WordTrace (prefixWord ++ tailWord_927633) baseStart_927633 baseEnd_927633 := by
    simpa [prefixWord, tailWord_927633, baseEnd_927633] using wordTrace_append hprefix tailTrace_927633
  have hstable : (prefixWord ++ tailWord_927633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927633).length < 2 ^ (prefixWord ++ tailWord_927633).sum := by decide
  have hdescent : baseEnd_927633 < baseStart_927633 := by decide
  rcases family_descends (prefixWord ++ tailWord_927633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927656 : List Nat := [2, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_927656 : Nat := 118140960795 + 927656 * 2 ^ 59
def prefixEnd_927656 : Nat := 4983230072969 + 3 ^ 40 * 927656 * 2
def baseEnd_927656 : Nat := 423407475579846911407817

theorem tailTrace_927656 : CollatzResearch.WordTrace tailWord_927656 prefixEnd_927656 423407475579846911407817 := by
  unfold tailWord_927656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917196963634108938285411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22556262618178811917713881 16917196963634108938285411)
  ·
    refine ⟨25375795445451163407428117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917196963634108938285411 25375795445451163407428117)
    ·
      refine ⟨1189490411505523284723193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25375795445451163407428117 1189490411505523284723193)
      ·
        refine ⟨892117808629142463542395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189490411505523284723193 892117808629142463542395)
        ·
          refine ⟨1338176712943713695313593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892117808629142463542395 1338176712943713695313593)
          ·
            refine ⟨1003632534707785271485195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338176712943713695313593 1003632534707785271485195)
            ·
              refine ⟨1505448802061677907227793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003632534707785271485195 1505448802061677907227793)
              ·
                refine ⟨1129086601546258430420845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1505448802061677907227793 1129086601546258430420845)
                ·
                  refine ⟨423407475579846911407817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129086601546258430420845 423407475579846911407817)
                  ·
                    rfl

theorem cell20_927656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_927656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927656 prefixEnd_927656 := by exact prefixLift 927656
  have htrace : WordTrace (prefixWord ++ tailWord_927656) baseStart_927656 baseEnd_927656 := by
    simpa [prefixWord, tailWord_927656, baseEnd_927656] using wordTrace_append hprefix tailTrace_927656
  have hstable : (prefixWord ++ tailWord_927656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927656).length < 2 ^ (prefixWord ++ tailWord_927656).sum := by decide
  have hdescent : baseEnd_927656 < baseStart_927656 := by decide
  rcases family_descends (prefixWord ++ tailWord_927656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927688 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_927688 : Nat := 118140960795 + 927688 * 2 ^ 59
def prefixEnd_927688 : Nat := 4983230072969 + 3 ^ 40 * 927688 * 2
def baseEnd_927688 : Nat := 423422081251797022341019

theorem tailTrace_927688 : CollatzResearch.WordTrace tailWord_927688 prefixEnd_927688 423422081251797022341019 := by
  unfold tailWord_927688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16917780531576143670867859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22557040708768191561157145 16917780531576143670867859)
  ·
    refine ⟨25376670797364215506301789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16917780531576143670867859 25376670797364215506301789)
    ·
      refine ⟨9516251549011580814863171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25376670797364215506301789 9516251549011580814863171)
      ·
        refine ⟨14274377323517371222294757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9516251549011580814863171 14274377323517371222294757)
        ·
          refine ⟨2676445748159507104180267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14274377323517371222294757 2676445748159507104180267)
          ·
            refine ⟨4014668622239260656270401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2676445748159507104180267 4014668622239260656270401)
            ·
              refine ⟨3011001466679445492202801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4014668622239260656270401 3011001466679445492202801)
              ·
                refine ⟨2258251100009584119152101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011001466679445492202801 2258251100009584119152101)
                ·
                  refine ⟨423422081251797022341019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258251100009584119152101 423422081251797022341019)
                  ·
                    rfl

theorem cell20_927688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_927688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927688 prefixEnd_927688 := by exact prefixLift 927688
  have htrace : WordTrace (prefixWord ++ tailWord_927688) baseStart_927688 baseEnd_927688 := by
    simpa [prefixWord, tailWord_927688, baseEnd_927688] using wordTrace_append hprefix tailTrace_927688
  have hstable : (prefixWord ++ tailWord_927688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927688).length < 2 ^ (prefixWord ++ tailWord_927688).sum := by decide
  have hdescent : baseEnd_927688 < baseStart_927688 := by decide
  rcases family_descends (prefixWord ++ tailWord_927688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927708 : List Nat := [2, 2, 6, 1, 1, 2, 6]
def baseStart_927708 : Nat := 118140960795 + 927708 * 2 ^ 59
def prefixEnd_927708 : Nat := 4983230072969 + 3 ^ 40 * 927708 * 2
def baseEnd_927708 : Nat := 47047912199640649074919

theorem tailTrace_927708 : CollatzResearch.WordTrace tailWord_927708 prefixEnd_927708 47047912199640649074919 := by
  unfold tailWord_927708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16918145261539915378731889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22557527015386553838309185 16918145261539915378731889)
  ·
    refine ⟨12688608946154936534048917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16918145261539915378731889 12688608946154936534048917)
    ·
      refine ⟨594778544351012650033543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12688608946154936534048917 594778544351012650033543)
      ·
        refine ⟨892167816526518975050315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594778544351012650033543 892167816526518975050315)
        ·
          refine ⟨1338251724789778462575473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892167816526518975050315 1338251724789778462575473)
          ·
            refine ⟨1003688793592333846931605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338251724789778462575473 1003688793592333846931605)
            ·
              refine ⟨47047912199640649074919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1003688793592333846931605 47047912199640649074919)
              ·
                rfl

theorem cell20_927708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 6].length) (baseStart_927708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927708 prefixEnd_927708 := by exact prefixLift 927708
  have htrace : WordTrace (prefixWord ++ tailWord_927708) baseStart_927708 baseEnd_927708 := by
    simpa [prefixWord, tailWord_927708, baseEnd_927708] using wordTrace_append hprefix tailTrace_927708
  have hstable : (prefixWord ++ tailWord_927708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927708).length < 2 ^ (prefixWord ++ tailWord_927708).sum := by decide
  have hdescent : baseEnd_927708 < baseStart_927708 := by decide
  rcases family_descends (prefixWord ++ tailWord_927708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927722 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_927722 : Nat := 118140960795 + 927722 * 2 ^ 59
def prefixEnd_927722 : Nat := 4983230072969 + 3 ^ 40 * 927722 * 2
def baseEnd_927722 : Nat := 423437599778244015207547

theorem tailTrace_927722 : CollatzResearch.WordTrace tailWord_927722 prefixEnd_927722 423437599778244015207547 := by
  unfold tailWord_927722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8459200286257277787118355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22557867430019407432315613 8459200286257277787118355)
  ·
    refine ⟨12688800429385916680677533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8459200286257277787118355 12688800429385916680677533)
    ·
      refine ⟨4758300161019718755254075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12688800429385916680677533 4758300161019718755254075)
      ·
        refine ⟨7137450241529578132881113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758300161019718755254075 7137450241529578132881113)
        ·
          refine ⟨5353087681147183599660835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7137450241529578132881113 5353087681147183599660835)
          ·
            refine ⟨8029631521720775399491253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353087681147183599660835 8029631521720775399491253)
            ·
              refine ⟨752777955161322693702305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8029631521720775399491253 752777955161322693702305)
              ·
                refine ⟨564583466370992020276729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752777955161322693702305 564583466370992020276729)
                ·
                  refine ⟨423437599778244015207547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564583466370992020276729 423437599778244015207547)
                  ·
                    rfl

theorem cell20_927722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_927722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927722 prefixEnd_927722 := by exact prefixLift 927722
  have htrace : WordTrace (prefixWord ++ tailWord_927722) baseStart_927722 baseEnd_927722 := by
    simpa [prefixWord, tailWord_927722, baseEnd_927722] using wordTrace_append hprefix tailTrace_927722
  have hstable : (prefixWord ++ tailWord_927722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927722).length < 2 ^ (prefixWord ++ tailWord_927722).sum := by decide
  have hdescent : baseEnd_927722 < baseStart_927722 := by decide
  rcases family_descends (prefixWord ++ tailWord_927722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927747 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 4]
def baseStart_927747 : Nat := 118140960795 + 927747 * 2 ^ 59
def prefixEnd_927747 : Nat := 4983230072969 + 3 ^ 40 * 927747 * 2
def baseEnd_927747 : Nat := 423449010459455039374111

theorem tailTrace_927747 : CollatzResearch.WordTrace tailWord_927747 prefixEnd_927747 423449010459455039374111 := by
  unfold tailWord_927747
  simp only [CollatzResearch.WordTrace]
  refine ⟨33837712969938540418133495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22558475313292360278755663 33837712969938540418133495)
  ·
    refine ⟨50756569454907810627200243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33837712969938540418133495 50756569454907810627200243)
    ·
      refine ⟨76134854182361715940800365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50756569454907810627200243 76134854182361715940800365)
      ·
        refine ⟨28550570318385643477800137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76134854182361715940800365 28550570318385643477800137)
        ·
          refine ⟨21412927738789232608350103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28550570318385643477800137 21412927738789232608350103)
          ·
            refine ⟨32119391608183848912525155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21412927738789232608350103 32119391608183848912525155)
            ·
              refine ⟨48179087412275773368787733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32119391608183848912525155 48179087412275773368787733)
              ·
                refine ⟨2258394722450426876661925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48179087412275773368787733 2258394722450426876661925)
                ·
                  refine ⟨423449010459455039374111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258394722450426876661925 423449010459455039374111)
                  ·
                    rfl

theorem cell20_927747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 4].length) (baseStart_927747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927747 prefixEnd_927747 := by exact prefixLift 927747
  have htrace : WordTrace (prefixWord ++ tailWord_927747) baseStart_927747 baseEnd_927747 := by
    simpa [prefixWord, tailWord_927747, baseEnd_927747] using wordTrace_append hprefix tailTrace_927747
  have hstable : (prefixWord ++ tailWord_927747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927747).length < 2 ^ (prefixWord ++ tailWord_927747).sum := by decide
  have hdescent : baseEnd_927747 < baseStart_927747 := by decide
  rcases family_descends (prefixWord ++ tailWord_927747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927777 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 2]
def baseStart_927777 : Nat := 118140960795 + 927777 * 2 ^ 59
def prefixEnd_927777 : Nat := 4983230072969 + 3 ^ 40 * 927777 * 2
def baseEnd_927777 : Nat := 423462703276908268373989

theorem tailTrace_927777 : CollatzResearch.WordTrace tailWord_927777 prefixEnd_927777 423462703276908268373989 := by
  unfold tailWord_927777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838807159829855541725585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22559204773219903694483723 33838807159829855541725585)
  ·
    refine ⟨25379105369872391656294189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33838807159829855541725585 25379105369872391656294189)
    ·
      refine ⟨9517164513702146871110321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25379105369872391656294189 9517164513702146871110321)
      ·
        refine ⟨7137873385276610153332741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9517164513702146871110321 7137873385276610153332741)
        ·
          refine ⟨1338351259739364403749889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7137873385276610153332741 1338351259739364403749889)
          ·
            refine ⟨1003763444804523302812417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338351259739364403749889 1003763444804523302812417)
            ·
              refine ⟨752822583603392477109313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1003763444804523302812417 752822583603392477109313)
              ·
                refine ⟨564616937702544357831985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752822583603392477109313 564616937702544357831985)
                ·
                  refine ⟨423462703276908268373989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564616937702544357831985 423462703276908268373989)
                  ·
                    rfl

theorem cell20_927777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_927777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927777 prefixEnd_927777 := by exact prefixLift 927777
  have htrace : WordTrace (prefixWord ++ tailWord_927777) baseStart_927777 baseEnd_927777 := by
    simpa [prefixWord, tailWord_927777, baseEnd_927777] using wordTrace_append hprefix tailTrace_927777
  have hstable : (prefixWord ++ tailWord_927777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927777).length < 2 ^ (prefixWord ++ tailWord_927777).sum := by decide
  have hdescent : baseEnd_927777 < baseStart_927777 := by decide
  rcases family_descends (prefixWord ++ tailWord_927777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927781 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 2]
def baseStart_927781 : Nat := 118140960795 + 927781 * 2 ^ 59
def prefixEnd_927781 : Nat := 4983230072969 + 3 ^ 40 * 927781 * 2
def baseEnd_927781 : Nat := 423464528985902032240639

theorem tailTrace_927781 : CollatzResearch.WordTrace tailWord_927781 prefixEnd_927781 423464528985902032240639 := by
  unfold tailWord_927781
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838953051815364224871197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22559302034543576149914131 33838953051815364224871197)
  ·
    refine ⟨12689607394430761584326699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33838953051815364224871197 12689607394430761584326699)
    ·
      refine ⟨19034411091646142376490049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12689607394430761584326699 19034411091646142376490049)
      ·
        refine ⟨14275808318734606782367537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19034411091646142376490049 14275808318734606782367537)
        ·
          refine ⟨10706856239050955086775653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14275808318734606782367537 10706856239050955086775653)
          ·
            refine ⟨2007535544822054078770435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10706856239050955086775653 2007535544822054078770435)
            ·
              refine ⟨3011303317233081118155653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007535544822054078770435 3011303317233081118155653)
              ·
                refine ⟨564619371981202709654185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3011303317233081118155653 564619371981202709654185)
                ·
                  refine ⟨423464528985902032240639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564619371981202709654185 423464528985902032240639)
                  ·
                    rfl

theorem cell20_927781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_927781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927781 prefixEnd_927781 := by exact prefixLift 927781
  have htrace : WordTrace (prefixWord ++ tailWord_927781) baseStart_927781 baseEnd_927781 := by
    simpa [prefixWord, tailWord_927781, baseEnd_927781] using wordTrace_append hprefix tailTrace_927781
  have hstable : (prefixWord ++ tailWord_927781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927781).length < 2 ^ (prefixWord ++ tailWord_927781).sum := by decide
  have hdescent : baseEnd_927781 < baseStart_927781 := by decide
  rcases family_descends (prefixWord ++ tailWord_927781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927784 : List Nat := [2, 1, 5, 3, 2, 1, 1, 5]
def baseStart_927784 : Nat := 118140960795 + 927784 * 2 ^ 59
def prefixEnd_927784 : Nat := 4983230072969 + 3 ^ 40 * 927784 * 2
def baseEnd_927784 : Nat := 141155299422549118380209

theorem tailTrace_927784 : CollatzResearch.WordTrace tailWord_927784 prefixEnd_927784 141155299422549118380209 := by
  unfold tailWord_927784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919531235402247868615203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22559374980536330491486937 16919531235402247868615203)
  ·
    refine ⟨25379296853103371802922805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16919531235402247868615203 25379296853103371802922805)
    ·
      refine ⟨2379309079978441106524013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25379296853103371802922805 2379309079978441106524013)
      ·
        refine ⟨892240904991915414946505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2379309079978441106524013 892240904991915414946505)
        ·
          refine ⟨669180678743936561209879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892240904991915414946505 669180678743936561209879)
          ·
            refine ⟨1003771018115904841814819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669180678743936561209879 1003771018115904841814819)
            ·
              refine ⟨1505656527173857262722229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003771018115904841814819 1505656527173857262722229)
              ·
                refine ⟨141155299422549118380209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505656527173857262722229 141155299422549118380209)
                ·
                  rfl

theorem cell20_927784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 5].length) (baseStart_927784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927784 prefixEnd_927784 := by exact prefixLift 927784
  have htrace : WordTrace (prefixWord ++ tailWord_927784) baseStart_927784 baseEnd_927784 := by
    simpa [prefixWord, tailWord_927784, baseEnd_927784] using wordTrace_append hprefix tailTrace_927784
  have hstable : (prefixWord ++ tailWord_927784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927784).length < 2 ^ (prefixWord ++ tailWord_927784).sum := by decide
  have hdescent : baseEnd_927784 < baseStart_927784 := by decide
  rcases family_descends (prefixWord ++ tailWord_927784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927840 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 4]
def baseStart_927840 : Nat := 118140960795 + 927840 * 2 ^ 59
def prefixEnd_927840 : Nat := 4983230072969 + 3 ^ 40 * 927840 * 2
def baseEnd_927840 : Nat := 423491458193560049273731

theorem tailTrace_927840 : CollatzResearch.WordTrace tailWord_927840 prefixEnd_927840 423491458193560049273731 := by
  unfold tailWord_927840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16920552479300808650634487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22560736639067744867512649 16920552479300808650634487)
  ·
    refine ⟨25380828718951212975951731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16920552479300808650634487 25380828718951212975951731)
    ·
      refine ⟨38071243078426819463927597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25380828718951212975951731 38071243078426819463927597)
      ·
        refine ⟨14276716154410057298972849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38071243078426819463927597 14276716154410057298972849)
        ·
          refine ⟨10707537115807542974229637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14276716154410057298972849 10707537115807542974229637)
          ·
            refine ⟨2007663209213914307668057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10707537115807542974229637 2007663209213914307668057)
            ·
              refine ⟨1505747406910435730751043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2007663209213914307668057 1505747406910435730751043)
              ·
                refine ⟨2258621110365653596126565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505747406910435730751043 2258621110365653596126565)
                ·
                  refine ⟨423491458193560049273731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258621110365653596126565 423491458193560049273731)
                  ·
                    rfl

theorem cell20_927840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 4].length) (baseStart_927840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927840 prefixEnd_927840 := by exact prefixLift 927840
  have htrace : WordTrace (prefixWord ++ tailWord_927840) baseStart_927840 baseEnd_927840 := by
    simpa [prefixWord, tailWord_927840, baseEnd_927840] using wordTrace_append hprefix tailTrace_927840
  have hstable : (prefixWord ++ tailWord_927840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927840).length < 2 ^ (prefixWord ++ tailWord_927840).sum := by decide
  have hdescent : baseEnd_927840 < baseStart_927840 := by decide
  rcases family_descends (prefixWord ++ tailWord_927840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927895 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_927895 : Nat := 118140960795 + 927895 * 2 ^ 59
def prefixEnd_927895 : Nat := 4983230072969 + 3 ^ 40 * 927895 * 2
def baseEnd_927895 : Nat := 423516561692224302440173

theorem tailTrace_927895 : CollatzResearch.WordTrace tailWord_927895 prefixEnd_927895 423516561692224302440173 := by
  unfold tailWord_927895
  simp only [CollatzResearch.WordTrace]
  refine ⟨33843110973402361694521139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22562073982268241129680759 33843110973402361694521139)
  ·
    refine ⟨50764666460103542541781709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33843110973402361694521139 50764666460103542541781709)
    ·
      refine ⟨19036749922538828453168141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50764666460103542541781709 19036749922538828453168141)
      ·
        refine ⟨7138781220952060669938053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19036749922538828453168141 7138781220952060669938053)
        ·
          refine ⟨1338521478928511375613385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7138781220952060669938053 1338521478928511375613385)
          ·
            refine ⟨1003891109196383531710039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1338521478928511375613385 1003891109196383531710039)
            ·
              refine ⟨1505836663794575297565059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003891109196383531710039 1505836663794575297565059)
              ·
                refine ⟨2258754995691862946347589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1505836663794575297565059 2258754995691862946347589)
                ·
                  refine ⟨423516561692224302440173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258754995691862946347589 423516561692224302440173)
                  ·
                    rfl

theorem cell20_927895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_927895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927895 prefixEnd_927895 := by exact prefixLift 927895
  have htrace : WordTrace (prefixWord ++ tailWord_927895) baseStart_927895 baseEnd_927895 := by
    simpa [prefixWord, tailWord_927895, baseEnd_927895] using wordTrace_append hprefix tailTrace_927895
  have hstable : (prefixWord ++ tailWord_927895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927895).length < 2 ^ (prefixWord ++ tailWord_927895).sum := by decide
  have hdescent : baseEnd_927895 < baseStart_927895 := by decide
  rcases family_descends (prefixWord ++ tailWord_927895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927950 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_927950 : Nat := 118140960795 + 927950 * 2 ^ 59
def prefixEnd_927950 : Nat := 4983230072969 + 3 ^ 40 * 927950 * 2
def baseEnd_927950 : Nat := 423541665190888555606615

theorem tailTrace_927950 : CollatzResearch.WordTrace tailWord_927950 prefixEnd_927950 423541665190888555606615 := by
  unfold tailWord_927950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4230639623525388260971663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22563411325468737391848869 4230639623525388260971663)
  ·
    refine ⟨6345959435288082391457495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4230639623525388260971663 6345959435288082391457495)
    ·
      refine ⟨9518939152932123587186243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6345959435288082391457495 9518939152932123587186243)
      ·
        refine ⟨14278408729398185380779365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518939152932123587186243 14278408729398185380779365)
        ·
          refine ⟨2677201636762159758896131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14278408729398185380779365 2677201636762159758896131)
          ·
            refine ⟨4015802455143239638344197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677201636762159758896131 4015802455143239638344197)
            ·
              refine ⟨752962960339357432189537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4015802455143239638344197 752962960339357432189537)
              ·
                refine ⟨564722220254518074142153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 752962960339357432189537 564722220254518074142153)
                ·
                  refine ⟨423541665190888555606615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564722220254518074142153 423541665190888555606615)
                  ·
                    rfl

theorem cell20_927950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_927950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927950 prefixEnd_927950 := by exact prefixLift 927950
  have htrace : WordTrace (prefixWord ++ tailWord_927950) baseStart_927950 baseEnd_927950 := by
    simpa [prefixWord, tailWord_927950, baseEnd_927950] using wordTrace_append hprefix tailTrace_927950
  have hstable : (prefixWord ++ tailWord_927950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927950).length < 2 ^ (prefixWord ++ tailWord_927950).sum := by decide
  have hdescent : baseEnd_927950 < baseStart_927950 := by decide
  rcases family_descends (prefixWord ++ tailWord_927950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927957 : List Nat := [1, 3, 2, 4, 3, 1, 1, 5]
def baseStart_927957 : Nat := 118140960795 + 927957 * 2 ^ 59
def prefixEnd_927957 : Nat := 4983230072969 + 3 ^ 40 * 927957 * 2
def baseEnd_927957 : Nat := 141181620060542547457751

theorem tailTrace_927957 : CollatzResearch.WordTrace tailWord_927957 prefixEnd_927957 141181620060542547457751 := by
  unfold tailWord_927957
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845372299177746283278125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22563581532785164188852083 33845372299177746283278125)
  ·
    refine ⟨12692014612191654856229297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33845372299177746283278125 12692014612191654856229297)
    ·
      refine ⟨9519010959143741142171973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12692014612191654856229297 9519010959143741142171973)
      ·
        refine ⟨1784814554839451464157245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9519010959143741142171973 1784814554839451464157245)
        ·
          refine ⟨669305458064794299058967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1784814554839451464157245 669305458064794299058967)
          ·
            refine ⟨1003958187097191448588451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669305458064794299058967 1003958187097191448588451)
            ·
              refine ⟨1505937280645787172882677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1003958187097191448588451 1505937280645787172882677)
              ·
                refine ⟨141181620060542547457751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1505937280645787172882677 141181620060542547457751)
                ·
                  rfl

theorem cell20_927957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 5].length) (baseStart_927957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927957 prefixEnd_927957 := by exact prefixLift 927957
  have htrace : WordTrace (prefixWord ++ tailWord_927957) baseStart_927957 baseEnd_927957 := by
    simpa [prefixWord, tailWord_927957, baseEnd_927957] using wordTrace_append hprefix tailTrace_927957
  have hstable : (prefixWord ++ tailWord_927957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927957).length < 2 ^ (prefixWord ++ tailWord_927957).sum := by decide
  have hdescent : baseEnd_927957 < baseStart_927957 := by decide
  rcases family_descends (prefixWord ++ tailWord_927957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927968 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_927968 : Nat := 118140960795 + 927968 * 2 ^ 59
def prefixEnd_927968 : Nat := 4983230072969 + 3 ^ 40 * 927968 * 2
def baseEnd_927968 : Nat := 423549880881360493006541

theorem tailTrace_927968 : CollatzResearch.WordTrace tailWord_927968 prefixEnd_927968 423549880881360493006541 := by
  unfold tailWord_927968
  simp only [CollatzResearch.WordTrace]
  refine ⟨16922886751068947580964279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22563849001425263441285705 16922886751068947580964279)
  ·
    refine ⟨25384330126603421371446419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16922886751068947580964279 25384330126603421371446419)
    ·
      refine ⟨38076495189905132057169629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25384330126603421371446419 38076495189905132057169629)
      ·
        refine ⟨14278685696214424521438611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38076495189905132057169629 14278685696214424521438611)
        ·
          refine ⟨21418028544321636782157917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278685696214424521438611 21418028544321636782157917)
          ·
            refine ⟨8031760704120613793309219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21418028544321636782157917 8031760704120613793309219)
            ·
              refine ⟨12047641056180920689963829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031760704120613793309219 12047641056180920689963829)
              ·
                refine ⟨1129466349016961314684109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12047641056180920689963829 1129466349016961314684109)
                ·
                  refine ⟨423549880881360493006541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129466349016961314684109 423549880881360493006541)
                  ·
                    rfl

theorem cell20_927968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_927968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927968 prefixEnd_927968 := by exact prefixLift 927968
  have htrace : WordTrace (prefixWord ++ tailWord_927968) baseStart_927968 baseEnd_927968 := by
    simpa [prefixWord, tailWord_927968, baseEnd_927968] using wordTrace_append hprefix tailTrace_927968
  have hstable : (prefixWord ++ tailWord_927968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927968).length < 2 ^ (prefixWord ++ tailWord_927968).sum := by decide
  have hdescent : baseEnd_927968 < baseStart_927968 := by decide
  rcases family_descends (prefixWord ++ tailWord_927968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_927971 : List Nat := [1, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_927971 : Nat := 118140960795 + 927971 * 2 ^ 59
def prefixEnd_927971 : Nat := 4983230072969 + 3 ^ 40 * 927971 * 2
def baseEnd_927971 : Nat := 423551250163105815906529

theorem tailTrace_927971 : CollatzResearch.WordTrace tailWord_927971 prefixEnd_927971 423551250163105815906529 := by
  unfold tailWord_927971
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845882921127026674287767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22563921947418017782858511 33845882921127026674287767)
  ·
    refine ⟨50768824381690540011431651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33845882921127026674287767 50768824381690540011431651)
    ·
      refine ⟨76153236572535810017147477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50768824381690540011431651 76153236572535810017147477)
      ·
        refine ⟨892420741084404023638447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 76153236572535810017147477 892420741084404023638447)
        ·
          refine ⟨1338631111626606035457671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892420741084404023638447 1338631111626606035457671)
          ·
            refine ⟨2007946667439909053186507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338631111626606035457671 2007946667439909053186507)
            ·
              refine ⟨3011920001159863579779761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2007946667439909053186507 3011920001159863579779761)
              ·
                refine ⟨2258940000869897684834821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3011920001159863579779761 2258940000869897684834821)
                ·
                  refine ⟨423551250163105815906529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2258940000869897684834821 423551250163105815906529)
                  ·
                    rfl

theorem cell20_927971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_927971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_927971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_927971 prefixEnd_927971 := by exact prefixLift 927971
  have htrace : WordTrace (prefixWord ++ tailWord_927971) baseStart_927971 baseEnd_927971 := by
    simpa [prefixWord, tailWord_927971, baseEnd_927971] using wordTrace_append hprefix tailTrace_927971
  have hstable : (prefixWord ++ tailWord_927971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_927971).length < 2 ^ (prefixWord ++ tailWord_927971).sum := by decide
  have hdescent : baseEnd_927971 < baseStart_927971 := by decide
  rcases family_descends (prefixWord ++ tailWord_927971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928002 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 3]
def baseStart_928002 : Nat := 118140960795 + 928002 * 2 ^ 59
def prefixEnd_928002 : Nat := 4983230072969 + 3 ^ 40 * 928002 * 2
def baseEnd_928002 : Nat := 423565399407807485873069

theorem tailTrace_928002 : CollatzResearch.WordTrace tailWord_928002 prefixEnd_928002 423565399407807485873069 := by
  unfold tailWord_928002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461753396003679742166565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22564675722676479312444173 8461753396003679742166565)
  ·
    refine ⟨1586578761750689951656231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8461753396003679742166565 1586578761750689951656231)
    ·
      refine ⟨2379868142626034927484347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1586578761750689951656231 2379868142626034927484347)
      ·
        refine ⟨3569802213939052391226521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2379868142626034927484347 3569802213939052391226521)
        ·
          refine ⟨2677351660454289293419891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3569802213939052391226521 2677351660454289293419891)
          ·
            refine ⟨4016027490681433940129837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2677351660454289293419891 4016027490681433940129837)
            ·
              refine ⟨1506010309005537727548689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4016027490681433940129837 1506010309005537727548689)
              ·
                refine ⟨1129507731754153295661517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1506010309005537727548689 1129507731754153295661517)
                ·
                  refine ⟨423565399407807485873069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1129507731754153295661517 423565399407807485873069)
                  ·
                    rfl

theorem cell20_928002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_928002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928002 prefixEnd_928002 := by exact prefixLift 928002
  have htrace : WordTrace (prefixWord ++ tailWord_928002) baseStart_928002 baseEnd_928002 := by
    simpa [prefixWord, tailWord_928002, baseEnd_928002] using wordTrace_append hprefix tailTrace_928002
  have hstable : (prefixWord ++ tailWord_928002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928002).length < 2 ^ (prefixWord ++ tailWord_928002).sum := by decide
  have hdescent : baseEnd_928002 < baseStart_928002 := by decide
  rcases family_descends (prefixWord ++ tailWord_928002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928037 : List Nat := [1, 3, 1, 2, 5, 1, 1, 6]
def baseStart_928037 : Nat := 118140960795 + 928037 * 2 ^ 59
def prefixEnd_928037 : Nat := 4983230072969 + 3 ^ 40 * 928037 * 2
def baseEnd_928037 : Nat := 141193791453834306568753

theorem tailTrace_928037 : CollatzResearch.WordTrace tailWord_928037 prefixEnd_928037 141193791453834306568753 := by
  unfold tailWord_928037
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848290138887919946190365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22565526759258613297460243 33848290138887919946190365)
  ·
    refine ⟨12693108802082969979821387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33848290138887919946190365 12693108802082969979821387)
    ·
      refine ⟨19039663203124454969732081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693108802082969979821387 19039663203124454969732081)
      ·
        refine ⟨14279747402343341227299061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19039663203124454969732081 14279747402343341227299061)
        ·
          refine ⟨1338726318969688240059287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14279747402343341227299061 1338726318969688240059287)
          ·
            refine ⟨2008089478454532360088931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1338726318969688240059287 2008089478454532360088931)
            ·
              refine ⟨3012134217681798540133397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008089478454532360088931 3012134217681798540133397)
              ·
                refine ⟨141193791453834306568753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3012134217681798540133397 141193791453834306568753)
                ·
                  rfl

theorem cell20_928037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 6].length) (baseStart_928037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928037 prefixEnd_928037 := by exact prefixLift 928037
  have htrace : WordTrace (prefixWord ++ tailWord_928037) baseStart_928037 baseEnd_928037 := by
    simpa [prefixWord, tailWord_928037, baseEnd_928037] using wordTrace_append hprefix tailTrace_928037
  have hstable : (prefixWord ++ tailWord_928037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928037).length < 2 ^ (prefixWord ++ tailWord_928037).sum := by decide
  have hdescent : baseEnd_928037 < baseStart_928037 := by decide
  rcases family_descends (prefixWord ++ tailWord_928037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928039 : List Nat := [1, 1, 8, 1, 2, 1, 1, 3, 2]
def baseStart_928039 : Nat := 118140960795 + 928039 * 2 ^ 59
def prefixEnd_928039 : Nat := 4983230072969 + 3 ^ 40 * 928039 * 2
def baseEnd_928039 : Nat := 423582287215999801639585

theorem tailTrace_928039 : CollatzResearch.WordTrace tailWord_928039 prefixEnd_928039 423582287215999801639585 := by
  unfold tailWord_928039
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848363084880674287763171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22565575389920449525175447 33848363084880674287763171)
  ·
    refine ⟨50772544627321011431644757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33848363084880674287763171 50772544627321011431644757)
    ·
      refine ⟨594990757351418102714587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 50772544627321011431644757 594990757351418102714587)
      ·
        refine ⟨892486136027127154071881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594990757351418102714587 892486136027127154071881)
        ·
          refine ⟨669364602020345365553911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 892486136027127154071881 669364602020345365553911)
          ·
            refine ⟨1004046903030518048330867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 669364602020345365553911 1004046903030518048330867)
            ·
              refine ⟨1506070354545777072496301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004046903030518048330867 1506070354545777072496301)
              ·
                refine ⟨564776382954666402186113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506070354545777072496301 564776382954666402186113)
                ·
                  refine ⟨423582287215999801639585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564776382954666402186113 423582287215999801639585)
                  ·
                    rfl

theorem cell20_928039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 3, 2].length) (baseStart_928039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928039 prefixEnd_928039 := by exact prefixLift 928039
  have htrace : WordTrace (prefixWord ++ tailWord_928039) baseStart_928039 baseEnd_928039 := by
    simpa [prefixWord, tailWord_928039, baseEnd_928039] using wordTrace_append hprefix tailTrace_928039
  have hstable : (prefixWord ++ tailWord_928039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928039).length < 2 ^ (prefixWord ++ tailWord_928039).sum := by decide
  have hdescent : baseEnd_928039 < baseStart_928039 := by decide
  rcases family_descends (prefixWord ++ tailWord_928039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928058 : List Nat := [3, 1, 1, 1, 4, 2, 8]
def baseStart_928058 : Nat := 118140960795 + 928058 * 2 ^ 59
def prefixEnd_928058 : Nat := 4983230072969 + 3 ^ 40 * 928058 * 2
def baseEnd_928058 : Nat := 47065662148191131111797

theorem tailTrace_928058 : CollatzResearch.WordTrace tailWord_928058 prefixEnd_928058 47065662148191131111797 := by
  unfold tailWord_928058
  simp only [CollatzResearch.WordTrace]
  refine ⟨8462264017952960133176207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22566037381207893688469885 8462264017952960133176207)
  ·
    refine ⟨12693396026929440199764311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8462264017952960133176207 12693396026929440199764311)
    ·
      refine ⟨19040094040394160299646467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693396026929440199764311 19040094040394160299646467)
      ·
        refine ⟨28560141060591240449469701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19040094040394160299646467 28560141060591240449469701)
        ·
          refine ⟨5355026448860857584275569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28560141060591240449469701 5355026448860857584275569)
          ·
            refine ⟨4016269836645643188206677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5355026448860857584275569 4016269836645643188206677)
            ·
              refine ⟨47065662148191131111797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4016269836645643188206677 47065662148191131111797)
              ·
                rfl

theorem cell20_928058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 8].length) (baseStart_928058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928058 prefixEnd_928058 := by exact prefixLift 928058
  have htrace : WordTrace (prefixWord ++ tailWord_928058) baseStart_928058 baseEnd_928058 := by
    simpa [prefixWord, tailWord_928058, baseEnd_928058] using wordTrace_append hprefix tailTrace_928058
  have hstable : (prefixWord ++ tailWord_928058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928058).length < 2 ^ (prefixWord ++ tailWord_928058).sum := by decide
  have hdescent : baseEnd_928058 < baseStart_928058 := by decide
  rcases family_descends (prefixWord ++ tailWord_928058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928123 : List Nat := [1, 1, 1, 1, 1, 7, 4, 2, 2]
def baseStart_928123 : Nat := 118140960795 + 928123 * 2 ^ 59
def prefixEnd_928123 : Nat := 4983230072969 + 3 ^ 40 * 928123 * 2
def baseEnd_928123 : Nat := 423620627104868842839241

theorem tailTrace_928123 : CollatzResearch.WordTrace tailWord_928123 prefixEnd_928123 423620627104868842839241 := by
  unfold tailWord_928123
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851426816576356633821023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22567617877717571089214015 33851426816576356633821023)
  ·
    refine ⟨50777140224864534950731535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33851426816576356633821023 50777140224864534950731535)
    ·
      refine ⟨76165710337296802426097303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50777140224864534950731535 76165710337296802426097303)
      ·
        refine ⟨114248565505945203639145955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76165710337296802426097303 114248565505945203639145955)
        ·
          refine ⟨171372848258917805458718933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114248565505945203639145955 171372848258917805458718933)
          ·
            refine ⟨4016551131068386065438725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 171372848258917805458718933 4016551131068386065438725)
            ·
              refine ⟨753103337075322387269761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4016551131068386065438725 753103337075322387269761)
              ·
                refine ⟨564827502806491790452321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 753103337075322387269761 564827502806491790452321)
                ·
                  refine ⟨423620627104868842839241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564827502806491790452321 423620627104868842839241)
                  ·
                    rfl

theorem cell20_928123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4, 2, 2].length) (baseStart_928123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928123 prefixEnd_928123 := by exact prefixLift 928123
  have htrace : WordTrace (prefixWord ++ tailWord_928123) baseStart_928123 baseEnd_928123 := by
    simpa [prefixWord, tailWord_928123, baseEnd_928123] using wordTrace_append hprefix tailTrace_928123
  have hstable : (prefixWord ++ tailWord_928123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928123).length < 2 ^ (prefixWord ++ tailWord_928123).sum := by decide
  have hdescent : baseEnd_928123 < baseStart_928123 := by decide
  rcases family_descends (prefixWord ++ tailWord_928123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928217 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 7]
def baseStart_928217 : Nat := 118140960795 + 928217 * 2 ^ 59
def prefixEnd_928217 : Nat := 4983230072969 + 3 ^ 40 * 928217 * 2
def baseEnd_928217 : Nat := 423663531266222293705523

theorem tailTrace_928217 : CollatzResearch.WordTrace tailWord_928217 prefixEnd_928217 423663531266222293705523 := by
  unfold tailWord_928217
  simp only [CollatzResearch.WordTrace]
  refine ⟨33854855278235810687742905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22569903518823873791828603 33854855278235810687742905)
  ·
    refine ⟨25391141458676858015807179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33854855278235810687742905 25391141458676858015807179)
    ·
      refine ⟨38086712188015287023710769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25391141458676858015807179 38086712188015287023710769)
      ·
        refine ⟨28565034141011465267783077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38086712188015287023710769 28565034141011465267783077)
        ·
          refine ⟨5355943901439649737709327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28565034141011465267783077 5355943901439649737709327)
          ·
            refine ⟨8033915852159474606563991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355943901439649737709327 8033915852159474606563991)
            ·
              refine ⟨12050873778239211909845987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033915852159474606563991 12050873778239211909845987)
              ·
                refine ⟨18076310667358817864768981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050873778239211909845987 18076310667358817864768981)
                ·
                  refine ⟨423663531266222293705523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18076310667358817864768981 423663531266222293705523)
                  ·
                    rfl

theorem cell20_928217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_928217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928217 prefixEnd_928217 := by exact prefixLift 928217
  have htrace : WordTrace (prefixWord ++ tailWord_928217) baseStart_928217 baseEnd_928217 := by
    simpa [prefixWord, tailWord_928217, baseEnd_928217] using wordTrace_append hprefix tailTrace_928217
  have hstable : (prefixWord ++ tailWord_928217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928217).length < 2 ^ (prefixWord ++ tailWord_928217).sum := by decide
  have hdescent : baseEnd_928217 < baseStart_928217 := by decide
  rcases family_descends (prefixWord ++ tailWord_928217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928227 : List Nat := [1, 1, 1, 6, 3, 2, 6]
def baseStart_928227 : Nat := 118140960795 + 928227 * 2 ^ 59
def prefixEnd_928227 : Nat := 4983230072969 + 3 ^ 40 * 928227 * 2
def baseEnd_928227 : Nat := 47074232837634078152461

theorem tailTrace_928227 : CollatzResearch.WordTrace tailWord_928227 prefixEnd_928227 47074232837634078152461 := by
  unfold tailWord_928227
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855220008199582395606935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22570146672133054930404623 33855220008199582395606935)
  ·
    refine ⟨50782830012299373593410403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33855220008199582395606935 50782830012299373593410403)
    ·
      refine ⟨76174245018449060390115605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50782830012299373593410403 76174245018449060390115605)
      ·
        refine ⟨3570667735239799705786669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76174245018449060390115605 3570667735239799705786669)
        ·
          refine ⟨1339000400714924889670001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3570667735239799705786669 1339000400714924889670001)
          ·
            refine ⟨1004250300536193667252501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339000400714924889670001 1004250300536193667252501)
            ·
              refine ⟨47074232837634078152461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1004250300536193667252501 47074232837634078152461)
              ·
                rfl

theorem cell20_928227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 6].length) (baseStart_928227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928227 prefixEnd_928227 := by exact prefixLift 928227
  have htrace : WordTrace (prefixWord ++ tailWord_928227) baseStart_928227 baseEnd_928227 := by
    simpa [prefixWord, tailWord_928227, baseEnd_928227] using wordTrace_append hprefix tailTrace_928227
  have hstable : (prefixWord ++ tailWord_928227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928227).length < 2 ^ (prefixWord ++ tailWord_928227).sum := by decide
  have hdescent : baseEnd_928227 < baseStart_928227 := by decide
  rcases family_descends (prefixWord ++ tailWord_928227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928234 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 5]
def baseStart_928234 : Nat := 118140960795 + 928234 * 2 ^ 59
def prefixEnd_928234 : Nat := 4983230072969 + 3 ^ 40 * 928234 * 2
def baseEnd_928234 : Nat := 423671290529445790138787

theorem tailTrace_928234 : CollatzResearch.WordTrace tailWord_928234 prefixEnd_928234 423671290529445790138787 := by
  unfold tailWord_928234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8463868829793555647777939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22570316879449481727407837 8463868829793555647777939)
  ·
    refine ⟨12695803244690333471666909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8463868829793555647777939 12695803244690333471666909)
    ·
      refine ⟨4760926216758875051875091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12695803244690333471666909 4760926216758875051875091)
      ·
        refine ⟨7141389325138312577812637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760926216758875051875091 7141389325138312577812637)
        ·
          refine ⟨2678020996926867216679739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7141389325138312577812637 2678020996926867216679739)
          ·
            refine ⟨4017031495390300825019609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678020996926867216679739 4017031495390300825019609)
            ·
              refine ⟨3012773621542725618764707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4017031495390300825019609 3012773621542725618764707)
              ·
                refine ⟨4519160432314088428147061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3012773621542725618764707 4519160432314088428147061)
                ·
                  refine ⟨423671290529445790138787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519160432314088428147061 423671290529445790138787)
                  ·
                    rfl

theorem cell20_928234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_928234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928234 prefixEnd_928234 := by exact prefixLift 928234
  have htrace : WordTrace (prefixWord ++ tailWord_928234) baseStart_928234 baseEnd_928234 := by
    simpa [prefixWord, tailWord_928234, baseEnd_928234] using wordTrace_append hprefix tailTrace_928234
  have hstable : (prefixWord ++ tailWord_928234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928234).length < 2 ^ (prefixWord ++ tailWord_928234).sum := by decide
  have hdescent : baseEnd_928234 < baseStart_928234 := by decide
  rcases family_descends (prefixWord ++ tailWord_928234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928237 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_928237 : Nat := 118140960795 + 928237 * 2 ^ 59
def prefixEnd_928237 : Nat := 4983230072969 + 3 ^ 40 * 928237 * 2
def baseEnd_928237 : Nat := 423672659811191113038775

theorem tailTrace_928237 : CollatzResearch.WordTrace tailWord_928237 prefixEnd_928237 423672659811191113038775 := by
  unfold tailWord_928237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33855584738163354103470965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22570389825442236068980643 33855584738163354103470965)
  ·
    refine ⟨3173961069202814447200403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33855584738163354103470965 3173961069202814447200403)
    ·
      refine ⟨4760941603804221670800605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3173961069202814447200403 4760941603804221670800605)
      ·
        refine ⟨1785353101426583126550227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4760941603804221670800605 1785353101426583126550227)
        ·
          refine ⟨2678029652139874689825341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785353101426583126550227 2678029652139874689825341)
          ·
            refine ⟨1004261119552453008684503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2678029652139874689825341 1004261119552453008684503)
            ·
              refine ⟨1506391679328679513026755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004261119552453008684503 1506391679328679513026755)
              ·
                refine ⟨2259587518993019269540133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506391679328679513026755 2259587518993019269540133)
                ·
                  refine ⟨423672659811191113038775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259587518993019269540133 423672659811191113038775)
                  ·
                    rfl

theorem cell20_928237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_928237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928237 prefixEnd_928237 := by exact prefixLift 928237
  have htrace : WordTrace (prefixWord ++ tailWord_928237) baseStart_928237 baseEnd_928237 := by
    simpa [prefixWord, tailWord_928237, baseEnd_928237] using wordTrace_append hprefix tailTrace_928237
  have hstable : (prefixWord ++ tailWord_928237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928237).length < 2 ^ (prefixWord ++ tailWord_928237).sum := by decide
  have hdescent : baseEnd_928237 < baseStart_928237 := by decide
  rcases family_descends (prefixWord ++ tailWord_928237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928248 : List Nat := [2, 1, 2, 1, 1, 4, 4, 5]
def baseStart_928248 : Nat := 118140960795 + 928248 * 2 ^ 59
def prefixEnd_928248 : Nat := 4983230072969 + 3 ^ 40 * 928248 * 2
def baseEnd_928248 : Nat := 141225893503641321224021

theorem tailTrace_928248 : CollatzResearch.WordTrace tailWord_928248 prefixEnd_928248 141225893503641321224021 := by
  unfold tailWord_928248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16927992970561751491060699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22570657294082335321414265 16927992970561751491060699)
  ·
    refine ⟨25391989455842627236591049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16927992970561751491060699 25391989455842627236591049)
    ·
      refine ⟨19043992091881970427443287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25391989455842627236591049 19043992091881970427443287)
      ·
        refine ⟨28565988137822955641164931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043992091881970427443287 28565988137822955641164931)
        ·
          refine ⟨42848982206734433461747397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28565988137822955641164931 42848982206734433461747397)
          ·
            refine ⟨8034184163762706274077637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42848982206734433461747397 8034184163762706274077637)
            ·
              refine ⟨1506409530705507426389557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8034184163762706274077637 1506409530705507426389557)
              ·
                refine ⟨141225893503641321224021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1506409530705507426389557 141225893503641321224021)
                ·
                  rfl

theorem cell20_928248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_928248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928248 prefixEnd_928248 := by exact prefixLift 928248
  have htrace : WordTrace (prefixWord ++ tailWord_928248) baseStart_928248 baseEnd_928248 := by
    simpa [prefixWord, tailWord_928248, baseEnd_928248] using wordTrace_append hprefix tailTrace_928248
  have hstable : (prefixWord ++ tailWord_928248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928248).length < 2 ^ (prefixWord ++ tailWord_928248).sum := by decide
  have hdescent : baseEnd_928248 < baseStart_928248 := by decide
  rcases family_descends (prefixWord ++ tailWord_928248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928292 : List Nat := [2, 3, 1, 5, 1, 1, 1, 4, 2]
def baseStart_928292 : Nat := 118140960795 + 928292 * 2 ^ 59
def prefixEnd_928292 : Nat := 4983230072969 + 3 ^ 40 * 928292 * 2
def baseEnd_928292 : Nat := 423697763309855366205217

theorem tailTrace_928292 : CollatzResearch.WordTrace tailWord_928292 prefixEnd_928292 423697763309855366205217 := by
  unfold tailWord_928292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928795376482049248361565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22571727168642732331148753 16928795376482049248361565)
  ·
    refine ⟨6348298266180768468135587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16928795376482049248361565 6348298266180768468135587)
    ·
      refine ⟨9522447399271152702203381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348298266180768468135587 9522447399271152702203381)
      ·
        refine ⟨892729443681670565831567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9522447399271152702203381 892729443681670565831567)
        ·
          refine ⟨1339094165522505848747351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892729443681670565831567 1339094165522505848747351)
          ·
            refine ⟨2008641248283758773121027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339094165522505848747351 2008641248283758773121027)
            ·
              refine ⟨3012961872425638159681541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2008641248283758773121027 3012961872425638159681541)
              ·
                refine ⟨564930351079807154940289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3012961872425638159681541 564930351079807154940289)
                ·
                  refine ⟨423697763309855366205217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564930351079807154940289 423697763309855366205217)
                  ·
                    rfl

theorem cell20_928292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 2].length) (baseStart_928292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928292 prefixEnd_928292 := by exact prefixLift 928292
  have htrace : WordTrace (prefixWord ++ tailWord_928292) baseStart_928292 baseEnd_928292 := by
    simpa [prefixWord, tailWord_928292, baseEnd_928292] using wordTrace_append hprefix tailTrace_928292
  have hstable : (prefixWord ++ tailWord_928292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928292).length < 2 ^ (prefixWord ++ tailWord_928292).sum := by decide
  have hdescent : baseEnd_928292 < baseStart_928292 := by decide
  rcases family_descends (prefixWord ++ tailWord_928292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928293 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 5]
def baseStart_928293 : Nat := 118140960795 + 928293 * 2 ^ 59
def prefixEnd_928293 : Nat := 4983230072969 + 3 ^ 40 * 928293 * 2
def baseEnd_928293 : Nat := 423698219737103807171879

theorem tailTrace_928293 : CollatzResearch.WordTrace tailWord_928293 prefixEnd_928293 423698219737103807171879 := by
  unfold tailWord_928293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33857627225960475667509533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22571751483973650445006355 33857627225960475667509533)
  ·
    refine ⟨12696610209735178375316075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33857627225960475667509533 12696610209735178375316075)
    ·
      refine ⟨19044915314602767562974113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12696610209735178375316075 19044915314602767562974113)
      ·
        refine ⟨14283686485952075672230585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19044915314602767562974113 14283686485952075672230585)
        ·
          refine ⟨10712764864464056754172939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283686485952075672230585 10712764864464056754172939)
          ·
            refine ⟨16069147296696085131259409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712764864464056754172939 16069147296696085131259409)
            ·
              refine ⟨12051860472522063848444557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16069147296696085131259409 12051860472522063848444557)
              ·
                refine ⟨4519447677195773943166709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12051860472522063848444557 4519447677195773943166709)
                ·
                  refine ⟨423698219737103807171879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519447677195773943166709 423698219737103807171879)
                  ·
                    rfl

theorem cell20_928293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_928293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928293 prefixEnd_928293 := by exact prefixLift 928293
  have htrace : WordTrace (prefixWord ++ tailWord_928293) baseStart_928293 baseEnd_928293 := by
    simpa [prefixWord, tailWord_928293, baseEnd_928293] using wordTrace_append hprefix tailTrace_928293
  have hstable : (prefixWord ++ tailWord_928293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928293).length < 2 ^ (prefixWord ++ tailWord_928293).sum := by decide
  have hdescent : baseEnd_928293 < baseStart_928293 := by decide
  rcases family_descends (prefixWord ++ tailWord_928293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928300 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_928300 : Nat := 118140960795 + 928300 * 2 ^ 59
def prefixEnd_928300 : Nat := 4983230072969 + 3 ^ 40 * 928300 * 2
def baseEnd_928300 : Nat := 423701414727842893938517

theorem tailTrace_928300 : CollatzResearch.WordTrace tailWord_928300 prefixEnd_928300 423701414727842893938517 := by
  unfold tailWord_928300
  simp only [CollatzResearch.WordTrace]
  refine ⟨16928941268467557931507177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22571921691290077242009569 16928941268467557931507177)
  ·
    refine ⟨12696705951350668448630383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16928941268467557931507177 12696705951350668448630383)
    ·
      refine ⟨19045058927026002672945575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12696705951350668448630383 19045058927026002672945575)
      ·
        refine ⟨28567588390539004009418363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19045058927026002672945575 28567588390539004009418363)
        ·
          refine ⟨42851382585808506014127545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28567588390539004009418363 42851382585808506014127545)
          ·
            refine ⟨32138536939356379510595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42851382585808506014127545 32138536939356379510595659)
            ·
              refine ⟨48207805409034569265893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32138536939356379510595659 48207805409034569265893489)
              ·
                refine ⟨36155854056775926949420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48207805409034569265893489 36155854056775926949420117)
                ·
                  refine ⟨423701414727842893938517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36155854056775926949420117 423701414727842893938517)
                  ·
                    rfl

theorem cell20_928300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_928300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928300 prefixEnd_928300 := by exact prefixLift 928300
  have htrace : WordTrace (prefixWord ++ tailWord_928300) baseStart_928300 baseEnd_928300 := by
    simpa [prefixWord, tailWord_928300, baseEnd_928300] using wordTrace_append hprefix tailTrace_928300
  have hstable : (prefixWord ++ tailWord_928300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928300).length < 2 ^ (prefixWord ++ tailWord_928300).sum := by decide
  have hdescent : baseEnd_928300 < baseStart_928300 := by decide
  rcases family_descends (prefixWord ++ tailWord_928300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928317 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 6]
def baseStart_928317 : Nat := 118140960795 + 928317 * 2 ^ 59
def prefixEnd_928317 : Nat := 4983230072969 + 3 ^ 40 * 928317 * 2
def baseEnd_928317 : Nat := 423709173991066390371781

theorem tailTrace_928317 : CollatzResearch.WordTrace tailWord_928317 prefixEnd_928317 423709173991066390371781 := by
  unfold tailWord_928317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858502577873527766383205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22572335051915685177588803 33858502577873527766383205)
  ·
    refine ⟨6348469233351286456196851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33858502577873527766383205 6348469233351286456196851)
    ·
      refine ⟨9522703850026929684295277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348469233351286456196851 9522703850026929684295277)
      ·
        refine ⟨3571013943760098631610729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9522703850026929684295277 3571013943760098631610729)
        ·
          refine ⟨2678260457820073973708047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3571013943760098631610729 2678260457820073973708047)
          ·
            refine ⟨4017390686730110960562071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2678260457820073973708047 4017390686730110960562071)
            ·
              refine ⟨6026086030095166440843107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4017390686730110960562071 6026086030095166440843107)
              ·
                refine ⟨9039129045142749661264661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026086030095166440843107 9039129045142749661264661)
                ·
                  refine ⟨423709173991066390371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9039129045142749661264661 423709173991066390371781)
                  ·
                    rfl

theorem cell20_928317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_928317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928317 prefixEnd_928317 := by exact prefixLift 928317
  have htrace : WordTrace (prefixWord ++ tailWord_928317) baseStart_928317 baseEnd_928317 := by
    simpa [prefixWord, tailWord_928317, baseEnd_928317] using wordTrace_append hprefix tailTrace_928317
  have hstable : (prefixWord ++ tailWord_928317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928317).length < 2 ^ (prefixWord ++ tailWord_928317).sum := by decide
  have hdescent : baseEnd_928317 < baseStart_928317 := by decide
  rcases family_descends (prefixWord ++ tailWord_928317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928334 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_928334 : Nat := 118140960795 + 928334 * 2 ^ 59
def prefixEnd_928334 : Nat := 4983230072969 + 3 ^ 40 * 928334 * 2
def baseEnd_928334 : Nat := 423716933254289886805045

theorem tailTrace_928334 : CollatzResearch.WordTrace tailWord_928334 prefixEnd_928334 423716933254289886805045 := by
  unfold tailWord_928334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232390327351492458719007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22572748412541293113168037 4232390327351492458719007)
  ·
    refine ⟨6348585491027238688078511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4232390327351492458719007 6348585491027238688078511)
    ·
      refine ⟨9522878236540858032117767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6348585491027238688078511 9522878236540858032117767)
      ·
        refine ⟨14284317354811287048176651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9522878236540858032117767 14284317354811287048176651)
        ·
          refine ⟨21426476032216930572264977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14284317354811287048176651 21426476032216930572264977)
          ·
            refine ⟨16069857024162697929198733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21426476032216930572264977 16069857024162697929198733)
            ·
              refine ⟨6026196384061011723449525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16069857024162697929198733 6026196384061011723449525)
              ·
                refine ⟨564955911005719849073393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6026196384061011723449525 564955911005719849073393)
                ·
                  refine ⟨423716933254289886805045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564955911005719849073393 423716933254289886805045)
                  ·
                    rfl

theorem cell20_928334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_928334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928334 prefixEnd_928334 := by exact prefixLift 928334
  have htrace : WordTrace (prefixWord ++ tailWord_928334) baseStart_928334 baseEnd_928334 := by
    simpa [prefixWord, tailWord_928334, baseEnd_928334] using wordTrace_append hprefix tailTrace_928334
  have hstable : (prefixWord ++ tailWord_928334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928334).length < 2 ^ (prefixWord ++ tailWord_928334).sum := by decide
  have hdescent : baseEnd_928334 < baseStart_928334 := by decide
  rcases family_descends (prefixWord ++ tailWord_928334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928355 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 4]
def baseStart_928355 : Nat := 118140960795 + 928355 * 2 ^ 59
def prefixEnd_928355 : Nat := 4983230072969 + 3 ^ 40 * 928355 * 2
def baseEnd_928355 : Nat := 423726518226507147104959

theorem tailTrace_928355 : CollatzResearch.WordTrace tailWord_928355 prefixEnd_928355 423726518226507147104959 := by
  unfold tailWord_928355
  simp only [CollatzResearch.WordTrace]
  refine ⟨33859888551735860256266519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22573259034490573504177679 33859888551735860256266519)
  ·
    refine ⟨50789832827603790384399779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33859888551735860256266519 50789832827603790384399779)
    ·
      refine ⟨76184749241405685576599669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50789832827603790384399779 76184749241405685576599669)
      ·
        refine ⟨7142320241381783022806219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76184749241405685576599669 7142320241381783022806219)
        ·
          refine ⟨10713480362072674534209329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142320241381783022806219 10713480362072674534209329)
          ·
            refine ⟨8035110271554505900656997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10713480362072674534209329 8035110271554505900656997)
            ·
              refine ⟨1506583175916469856373187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8035110271554505900656997 1506583175916469856373187)
              ·
                refine ⟨2259874763874704784559781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1506583175916469856373187 2259874763874704784559781)
                ·
                  refine ⟨423726518226507147104959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2259874763874704784559781 423726518226507147104959)
                  ·
                    rfl

theorem cell20_928355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_928355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928355 prefixEnd_928355 := by exact prefixLift 928355
  have htrace : WordTrace (prefixWord ++ tailWord_928355) baseStart_928355 baseEnd_928355 := by
    simpa [prefixWord, tailWord_928355, baseEnd_928355] using wordTrace_append hprefix tailTrace_928355
  have hstable : (prefixWord ++ tailWord_928355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928355).length < 2 ^ (prefixWord ++ tailWord_928355).sum := by decide
  have hdescent : baseEnd_928355 < baseStart_928355 := by decide
  rcases family_descends (prefixWord ++ tailWord_928355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928362 : List Nat := [3, 1, 3, 2, 1, 1, 2, 7]
def baseStart_928362 : Nat := 118140960795 + 928362 * 2 ^ 59
def prefixEnd_928362 : Nat := 4983230072969 + 3 ^ 40 * 928362 * 2
def baseEnd_928362 : Nat := 141243237739082077957199

theorem tailTrace_928362 : CollatzResearch.WordTrace tailWord_928362 prefixEnd_928362 141243237739082077957199 := by
  unfold tailWord_928362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465035965677625112942835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22573429241807000301180893 8465035965677625112942835)
  ·
    refine ⟨12697553948516437669414253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465035965677625112942835 12697553948516437669414253)
    ·
      refine ⟨4761582730693664126030345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12697553948516437669414253 4761582730693664126030345)
      ·
        refine ⟨3571187048020248094522759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4761582730693664126030345 3571187048020248094522759)
        ·
          refine ⟨5356780572030372141784139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571187048020248094522759 5356780572030372141784139)
          ·
            refine ⟨8035170858045558212676209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356780572030372141784139 8035170858045558212676209)
            ·
              refine ⟨6026378143534168659507157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035170858045558212676209 6026378143534168659507157)
              ·
                refine ⟨141243237739082077957199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6026378143534168659507157 141243237739082077957199)
                ·
                  rfl

theorem cell20_928362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_928362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928362 prefixEnd_928362 := by exact prefixLift 928362
  have htrace : WordTrace (prefixWord ++ tailWord_928362) baseStart_928362 baseEnd_928362 := by
    simpa [prefixWord, tailWord_928362, baseEnd_928362] using wordTrace_append hprefix tailTrace_928362
  have hstable : (prefixWord ++ tailWord_928362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928362).length < 2 ^ (prefixWord ++ tailWord_928362).sum := by decide
  have hdescent : baseEnd_928362 < baseStart_928362 := by decide
  rcases family_descends (prefixWord ++ tailWord_928362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928389 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 2]
def baseStart_928389 : Nat := 118140960795 + 928389 * 2 ^ 59
def prefixEnd_928389 : Nat := 4983230072969 + 3 ^ 40 * 928389 * 2
def baseEnd_928389 : Nat := 423742036752954139971487

theorem tailTrace_928389 : CollatzResearch.WordTrace tailWord_928389 prefixEnd_928389 423742036752954139971487 := by
  unfold tailWord_928389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861128633612684063004221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22574085755741789375336147 33861128633612684063004221)
  ·
    refine ⟨12697923237604756523626583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33861128633612684063004221 12697923237604756523626583)
    ·
      refine ⟨19046884856407134785439875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12697923237604756523626583 19046884856407134785439875)
      ·
        refine ⟨28570327284610702178159813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046884856407134785439875 28570327284610702178159813)
        ·
          refine ⟨5356936365864506658404965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28570327284610702178159813 5356936365864506658404965)
          ·
            refine ⟨1004425568599594998450931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5356936365864506658404965 1004425568599594998450931)
            ·
              refine ⟨1506638352899392497676397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004425568599594998450931 1506638352899392497676397)
              ·
                refine ⟨564989382337272186628649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506638352899392497676397 564989382337272186628649)
                ·
                  refine ⟨423742036752954139971487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 564989382337272186628649 423742036752954139971487)
                  ·
                    rfl

theorem cell20_928389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_928389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928389 prefixEnd_928389 := by exact prefixLift 928389
  have htrace : WordTrace (prefixWord ++ tailWord_928389) baseStart_928389 baseEnd_928389 := by
    simpa [prefixWord, tailWord_928389, baseEnd_928389] using wordTrace_append hprefix tailTrace_928389
  have hstable : (prefixWord ++ tailWord_928389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928389).length < 2 ^ (prefixWord ++ tailWord_928389).sum := by decide
  have hdescent : baseEnd_928389 < baseStart_928389 := by decide
  rcases family_descends (prefixWord ++ tailWord_928389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928407 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 5]
def baseStart_928407 : Nat := 118140960795 + 928407 * 2 ^ 59
def prefixEnd_928407 : Nat := 4983230072969 + 3 ^ 40 * 928407 * 2
def baseEnd_928407 : Nat := 423750252443426077371413

theorem tailTrace_928407 : CollatzResearch.WordTrace tailWord_928407 prefixEnd_928407 423750252443426077371413 := by
  unfold tailWord_928407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861785147547473137159475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22574523431698315424772983 33861785147547473137159475)
  ·
    refine ⟨50792677721321209705739213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861785147547473137159475 50792677721321209705739213)
    ·
      refine ⟨19047254145495453639652205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50792677721321209705739213 19047254145495453639652205)
      ·
        refine ⟨7142720304560795114869577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19047254145495453639652205 7142720304560795114869577)
        ·
          refine ⟨5357040228420596336152183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7142720304560795114869577 5357040228420596336152183)
          ·
            refine ⟨8035560342630894504228275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357040228420596336152183 8035560342630894504228275)
            ·
              refine ⟨12053340513946341756342413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035560342630894504228275 12053340513946341756342413)
              ·
                refine ⟨4520002692729878158628405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12053340513946341756342413 4520002692729878158628405)
                ·
                  refine ⟨423750252443426077371413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520002692729878158628405 423750252443426077371413)
                  ·
                    rfl

theorem cell20_928407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_928407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928407 prefixEnd_928407 := by exact prefixLift 928407
  have htrace : WordTrace (prefixWord ++ tailWord_928407) baseStart_928407 baseEnd_928407 := by
    simpa [prefixWord, tailWord_928407, baseEnd_928407] using wordTrace_append hprefix tailTrace_928407
  have hstable : (prefixWord ++ tailWord_928407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928407).length < 2 ^ (prefixWord ++ tailWord_928407).sum := by decide
  have hdescent : baseEnd_928407 < baseStart_928407 := by decide
  rcases family_descends (prefixWord ++ tailWord_928407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928417 : List Nat := [1, 2, 3, 3, 3, 1, 2, 5]
def baseStart_928417 : Nat := 118140960795 + 928417 * 2 ^ 59
def prefixEnd_928417 : Nat := 4983230072969 + 3 ^ 40 * 928417 * 2
def baseEnd_928417 : Nat := 141251605571970162346013

theorem tailTrace_928417 : CollatzResearch.WordTrace tailWord_928417 prefixEnd_928417 141251605571970162346013 := by
  unfold tailWord_928417
  simp only [CollatzResearch.WordTrace]
  refine ⟨33862149877511244845023505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22574766585007496563349003 33862149877511244845023505)
  ·
    refine ⟨25396612408133433633767629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33862149877511244845023505 25396612408133433633767629)
    ·
      refine ⟨9523729653050037612662861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25396612408133433633767629 9523729653050037612662861)
      ·
        refine ⟨3571398619893764104748573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9523729653050037612662861 3571398619893764104748573)
        ·
          refine ⟨1339274482460161539280715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3571398619893764104748573 1339274482460161539280715)
          ·
            refine ⟨2008911723690242308921073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339274482460161539280715 2008911723690242308921073)
            ·
              refine ⟨1506683792767681731690805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2008911723690242308921073 1506683792767681731690805)
              ·
                refine ⟨141251605571970162346013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1506683792767681731690805 141251605571970162346013)
                ·
                  rfl

theorem cell20_928417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_928417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928417 prefixEnd_928417 := by exact prefixLift 928417
  have htrace : WordTrace (prefixWord ++ tailWord_928417) baseStart_928417 baseEnd_928417 := by
    simpa [prefixWord, tailWord_928417, baseEnd_928417] using wordTrace_append hprefix tailTrace_928417
  have hstable : (prefixWord ++ tailWord_928417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928417).length < 2 ^ (prefixWord ++ tailWord_928417).sum := by decide
  have hdescent : baseEnd_928417 < baseStart_928417 := by decide
  rcases family_descends (prefixWord ++ tailWord_928417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928462 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_928462 : Nat := 118140960795 + 928462 * 2 ^ 59
def prefixEnd_928462 : Nat := 4983230072969 + 3 ^ 40 * 928462 * 2
def baseEnd_928462 : Nat := 423775355942090330537855

theorem tailTrace_928462 : CollatzResearch.WordTrace tailWord_928462 prefixEnd_928462 423775355942090330537855 := by
  unfold tailWord_928462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4232973895293527191301455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22575860774898811686941093 4232973895293527191301455)
  ·
    refine ⟨6349460842940290786952183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4232973895293527191301455 6349460842940290786952183)
    ·
      refine ⟨9524191264410436180428275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349460842940290786952183 9524191264410436180428275)
      ·
        refine ⟨14286286896615654270642413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524191264410436180428275 14286286896615654270642413)
        ·
          refine ⟨5357357586230870351490905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14286286896615654270642413 5357357586230870351490905)
          ·
            refine ⟨4018018189673152763618179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5357357586230870351490905 4018018189673152763618179)
            ·
              refine ⟨6027027284509729145427269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4018018189673152763618179 6027027284509729145427269)
              ·
                refine ⟨1130067615845574214767613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6027027284509729145427269 1130067615845574214767613)
                ·
                  refine ⟨423775355942090330537855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130067615845574214767613 423775355942090330537855)
                  ·
                    rfl

theorem cell20_928462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_928462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928462 prefixEnd_928462 := by exact prefixLift 928462
  have htrace : WordTrace (prefixWord ++ tailWord_928462) baseStart_928462 baseEnd_928462 := by
    simpa [prefixWord, tailWord_928462, baseEnd_928462] using wordTrace_append hprefix tailTrace_928462
  have hstable : (prefixWord ++ tailWord_928462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928462).length < 2 ^ (prefixWord ++ tailWord_928462).sum := by decide
  have hdescent : baseEnd_928462 < baseStart_928462 := by decide
  rcases family_descends (prefixWord ++ tailWord_928462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928493 : List Nat := [1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_928493 : Nat := 118140960795 + 928493 * 2 ^ 59
def prefixEnd_928493 : Nat := 4983230072969 + 3 ^ 40 * 928493 * 2
def baseEnd_928493 : Nat := 141263168395597333501465

theorem tailTrace_928493 : CollatzResearch.WordTrace tailWord_928493 prefixEnd_928493 141263168395597333501465 := by
  unfold tailWord_928493
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864921825235909824790133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22576614550157273216526755 33864921825235909824790133)
  ·
    refine ⟨3174836421115866546074075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33864921825235909824790133 3174836421115866546074075)
    ·
      refine ⟨4762254631673799819111113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3174836421115866546074075 4762254631673799819111113)
      ·
        refine ⟨3571690973755349864333335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4762254631673799819111113 3571690973755349864333335)
        ·
          refine ⟨5357536460633024796500003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571690973755349864333335 5357536460633024796500003)
          ·
            refine ⟨8036304690949537194750005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357536460633024796500003 8036304690949537194750005)
            ·
              refine ⟨753403564776519112007813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8036304690949537194750005 753403564776519112007813)
              ·
                refine ⟨141263168395597333501465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753403564776519112007813 141263168395597333501465)
                ·
                  rfl

theorem cell20_928493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_928493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928493 prefixEnd_928493 := by exact prefixLift 928493
  have htrace : WordTrace (prefixWord ++ tailWord_928493) baseStart_928493 baseEnd_928493 := by
    simpa [prefixWord, tailWord_928493, baseEnd_928493] using wordTrace_append hprefix tailTrace_928493
  have hstable : (prefixWord ++ tailWord_928493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928493).length < 2 ^ (prefixWord ++ tailWord_928493).sum := by decide
  have hdescent : baseEnd_928493 < baseStart_928493 := by decide
  rcases family_descends (prefixWord ++ tailWord_928493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928548 : List Nat := [2, 3, 1, 3, 3, 2, 2, 4]
def baseStart_928548 : Nat := 118140960795 + 928548 * 2 ^ 59
def prefixEnd_928548 : Nat := 4983230072969 + 3 ^ 40 * 928548 * 2
def baseEnd_928548 : Nat := 141271536228485417890279

theorem tailTrace_928548 : CollatzResearch.WordTrace tailWord_928548 prefixEnd_928548 141271536228485417890279 := by
  unfold tailWord_928548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933463920018327109021149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22577951893357769478694865 16933463920018327109021149)
  ·
    refine ⟨6350048970006872665882931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16933463920018327109021149 6350048970006872665882931)
    ·
      refine ⟨9525073455010308998824397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350048970006872665882931 9525073455010308998824397)
      ·
        refine ⟨3571902545628865874559149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9525073455010308998824397 3571902545628865874559149)
        ·
          refine ⟨1339463454610824702959681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3571902545628865874559149 1339463454610824702959681)
          ·
            refine ⟨1004597590958118527219761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339463454610824702959681 1004597590958118527219761)
            ·
              refine ⟨753448193218588895414821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004597590958118527219761 753448193218588895414821)
              ·
                refine ⟨141271536228485417890279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 753448193218588895414821 141271536228485417890279)
                ·
                  rfl

theorem cell20_928548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 4].length) (baseStart_928548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928548 prefixEnd_928548 := by exact prefixLift 928548
  have htrace : WordTrace (prefixWord ++ tailWord_928548) baseStart_928548 baseEnd_928548 := by
    simpa [prefixWord, tailWord_928548, baseEnd_928548] using wordTrace_append hprefix tailTrace_928548
  have hstable : (prefixWord ++ tailWord_928548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928548).length < 2 ^ (prefixWord ++ tailWord_928548).sum := by decide
  have hdescent : baseEnd_928548 < baseStart_928548 := by decide
  rcases family_descends (prefixWord ++ tailWord_928548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928552 : List Nat := [2, 1, 5, 1, 1, 1, 3, 6]
def baseStart_928552 : Nat := 118140960795 + 928552 * 2 ^ 59
def prefixEnd_928552 : Nat := 4983230072969 + 3 ^ 40 * 928552 * 2
def baseEnd_928552 : Nat := 141272144798150005845829

theorem tailTrace_928552 : CollatzResearch.WordTrace tailWord_928552 prefixEnd_928552 141272144798150005845829 := by
  unfold tailWord_928552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16933536866011081450593955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22578049154681441934125273 16933536866011081450593955)
  ·
    refine ⟨25400305299016622175890933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16933536866011081450593955 25400305299016622175890933)
    ·
      refine ⟨2381278621782808328989775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25400305299016622175890933 2381278621782808328989775)
      ·
        refine ⟨3571917932674212493484663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2381278621782808328989775 3571917932674212493484663)
        ·
          refine ⟨5357876899011318740226995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3571917932674212493484663 5357876899011318740226995)
          ·
            refine ⟨8036815348516978110340493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357876899011318740226995 8036815348516978110340493)
            ·
              refine ⟨3013805755693866791377685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8036815348516978110340493 3013805755693866791377685)
              ·
                refine ⟨141272144798150005845829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3013805755693866791377685 141272144798150005845829)
                ·
                  rfl

theorem cell20_928552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_928552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928552 prefixEnd_928552 := by exact prefixLift 928552
  have htrace : WordTrace (prefixWord ++ tailWord_928552) baseStart_928552 baseEnd_928552 := by
    simpa [prefixWord, tailWord_928552, baseEnd_928552] using wordTrace_append hprefix tailTrace_928552
  have hstable : (prefixWord ++ tailWord_928552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928552).length < 2 ^ (prefixWord ++ tailWord_928552).sum := by decide
  have hdescent : baseEnd_928552 < baseStart_928552 := by decide
  rcases family_descends (prefixWord ++ tailWord_928552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928558 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_928558 : Nat := 118140960795 + 928558 * 2 ^ 59
def prefixEnd_928558 : Nat := 4983230072969 + 3 ^ 40 * 928558 * 2
def baseEnd_928558 : Nat := 423819172957940663337463

theorem tailTrace_928558 : CollatzResearch.WordTrace tailWord_928558 prefixEnd_928558 423819172957940663337463 := by
  unfold tailWord_928558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233411571250053240738291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22578195046666950617270885 4233411571250053240738291)
  ·
    refine ⟨6350117356875079861107437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4233411571250053240738291 6350117356875079861107437)
    ·
      refine ⟨2381294008828154947915289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6350117356875079861107437 2381294008828154947915289)
      ·
        refine ⟨1785970506621116210936467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381294008828154947915289 1785970506621116210936467)
        ·
          refine ⟨2678955759931674316404701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1785970506621116210936467 2678955759931674316404701)
          ·
            refine ⟨1004608409974377868651763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2678955759931674316404701 1004608409974377868651763)
            ·
              refine ⟨1506912614961566802977645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1004608409974377868651763 1506912614961566802977645)
              ·
                refine ⟨565092230610587551116617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1506912614961566802977645 565092230610587551116617)
                ·
                  refine ⟨423819172957940663337463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565092230610587551116617 423819172957940663337463)
                  ·
                    rfl

theorem cell20_928558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_928558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928558 prefixEnd_928558 := by exact prefixLift 928558
  have htrace : WordTrace (prefixWord ++ tailWord_928558) baseStart_928558 baseEnd_928558 := by
    simpa [prefixWord, tailWord_928558, baseEnd_928558] using wordTrace_append hprefix tailTrace_928558
  have hstable : (prefixWord ++ tailWord_928558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928558).length < 2 ^ (prefixWord ++ tailWord_928558).sum := by decide
  have hdescent : baseEnd_928558 < baseStart_928558 := by decide
  rcases family_descends (prefixWord ++ tailWord_928558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928589 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 3]
def baseStart_928589 : Nat := 118140960795 + 928589 * 2 ^ 59
def prefixEnd_928589 : Nat := 4983230072969 + 3 ^ 40 * 928589 * 2
def baseEnd_928589 : Nat := 423833322202642333304003

theorem tailTrace_928589 : CollatzResearch.WordTrace tailWord_928589 prefixEnd_928589 423833322202642333304003 := by
  unfold tailWord_928589
  simp only [CollatzResearch.WordTrace]
  refine ⟨33868423232888118220284821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22578948821925412146856547 33868423232888118220284821)
  ·
    refine ⟨1587582339041630541575851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33868423232888118220284821 1587582339041630541575851)
    ·
      refine ⟨2381373508562445812363777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1587582339041630541575851 2381373508562445812363777)
      ·
        refine ⟨1786030131421834359272833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381373508562445812363777 1786030131421834359272833)
        ·
          refine ⟨1339522598566375769454625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1786030131421834359272833 1339522598566375769454625)
          ·
            refine ⟨1004641948924781827090969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1339522598566375769454625 1004641948924781827090969)
            ·
              refine ⟨753481461693586370318227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1004641948924781827090969 753481461693586370318227)
              ·
                refine ⟨1130222192540379555477341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753481461693586370318227 1130222192540379555477341)
                ·
                  refine ⟨423833322202642333304003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130222192540379555477341 423833322202642333304003)
                  ·
                    rfl

theorem cell20_928589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_928589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928589 prefixEnd_928589 := by exact prefixLift 928589
  have htrace : WordTrace (prefixWord ++ tailWord_928589) baseStart_928589 baseEnd_928589 := by
    simpa [prefixWord, tailWord_928589, baseEnd_928589] using wordTrace_append hprefix tailTrace_928589
  have hstable : (prefixWord ++ tailWord_928589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928589).length < 2 ^ (prefixWord ++ tailWord_928589).sum := by decide
  have hdescent : baseEnd_928589 < baseStart_928589 := by decide
  rcases family_descends (prefixWord ++ tailWord_928589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928635 : List Nat := [1, 1, 1, 1, 1, 5, 3, 4, 3]
def baseStart_928635 : Nat := 118140960795 + 928635 * 2 ^ 59
def prefixEnd_928635 : Nat := 4983230072969 + 3 ^ 40 * 928635 * 2
def baseEnd_928635 : Nat := 423854317856070617770481

theorem tailTrace_928635 : CollatzResearch.WordTrace tailWord_928635 prefixEnd_928635 423854317856070617770481 := by
  unfold tailWord_928635
  simp only [CollatzResearch.WordTrace]
  refine ⟨33870100990721468076459359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22580067327147645384306239 33870100990721468076459359)
  ·
    refine ⟨50805151486082202114689039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33870100990721468076459359 50805151486082202114689039)
    ·
      refine ⟨76207727229123303172033559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50805151486082202114689039 76207727229123303172033559)
      ·
        refine ⟨114311590843684954758050339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76207727229123303172033559 114311590843684954758050339)
        ·
          refine ⟨171467386265527432137075509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114311590843684954758050339 171467386265527432137075509)
          ·
            refine ⟨16075067462393196762850829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171467386265527432137075509 16075067462393196762850829)
            ·
              refine ⟨6028150298397448786069061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16075067462393196762850829 6028150298397448786069061)
              ·
                refine ⟨1130278180949521647387949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6028150298397448786069061 1130278180949521647387949)
                ·
                  refine ⟨423854317856070617770481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130278180949521647387949 423854317856070617770481)
                  ·
                    rfl

theorem cell20_928635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 4, 3].length) (baseStart_928635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928635 prefixEnd_928635 := by exact prefixLift 928635
  have htrace : WordTrace (prefixWord ++ tailWord_928635) baseStart_928635 baseEnd_928635 := by
    simpa [prefixWord, tailWord_928635, baseEnd_928635] using wordTrace_append hprefix tailTrace_928635
  have hstable : (prefixWord ++ tailWord_928635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928635).length < 2 ^ (prefixWord ++ tailWord_928635).sum := by decide
  have hdescent : baseEnd_928635 < baseStart_928635 := by decide
  rcases family_descends (prefixWord ++ tailWord_928635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928676 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 2]
def baseStart_928676 : Nat := 118140960795 + 928676 * 2 ^ 59
def prefixEnd_928676 : Nat := 4983230072969 + 3 ^ 40 * 928676 * 2
def baseEnd_928676 : Nat := 423873031373256697403647

theorem tailTrace_928676 : CollatzResearch.WordTrace tailWord_928676 prefixEnd_928676 423873031373256697403647 := by
  unfold tailWord_928676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16935798191786466039350941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22581064255715288052467921 16935798191786466039350941)
  ·
    refine ⟨6350924321919924764756603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16935798191786466039350941 6350924321919924764756603)
    ·
      refine ⟨9526386482879887147134905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6350924321919924764756603 9526386482879887147134905)
      ·
        refine ⟨7144789862159915360351179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9526386482879887147134905 7144789862159915360351179)
        ·
          refine ⟨10717184793239873040526769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7144789862159915360351179 10717184793239873040526769)
          ·
            refine ⟨8037888594929904780395077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10717184793239873040526769 8037888594929904780395077)
            ·
              refine ⟨1507104111549357146324077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8037888594929904780395077 1507104111549357146324077)
              ·
                refine ⟨565164041831008929871529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507104111549357146324077 565164041831008929871529)
                ·
                  refine ⟨423873031373256697403647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565164041831008929871529 423873031373256697403647)
                  ·
                    rfl

theorem cell20_928676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_928676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928676 prefixEnd_928676 := by exact prefixLift 928676
  have htrace : WordTrace (prefixWord ++ tailWord_928676) baseStart_928676 baseEnd_928676 := by
    simpa [prefixWord, tailWord_928676, baseEnd_928676] using wordTrace_append hprefix tailTrace_928676
  have hstable : (prefixWord ++ tailWord_928676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928676).length < 2 ^ (prefixWord ++ tailWord_928676).sum := by decide
  have hdescent : baseEnd_928676 < baseStart_928676 := by decide
  rcases family_descends (prefixWord ++ tailWord_928676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928697 : List Nat := [1, 2, 1, 4, 2, 3, 2, 1, 4]
def baseStart_928697 : Nat := 118140960795 + 928697 * 2 ^ 59
def prefixEnd_928697 : Nat := 4983230072969 + 3 ^ 40 * 928697 * 2
def baseEnd_928697 : Nat := 423882616345473957703561

theorem tailTrace_928697 : CollatzResearch.WordTrace tailWord_928697 prefixEnd_928697 423882616345473957703561 := by
  unfold tailWord_928697
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872362316496852665216345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22581574877664568443477563 33872362316496852665216345)
  ·
    refine ⟨25404271737372639498912259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33872362316496852665216345 25404271737372639498912259)
    ·
      refine ⟨38106407606058959248368389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25404271737372639498912259 38106407606058959248368389)
      ·
        refine ⟨7144951426136054859069073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38106407606058959248368389 7144951426136054859069073)
        ·
          refine ⟨5358713569602041144301805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7144951426136054859069073 5358713569602041144301805)
          ·
            refine ⟨2009517588600765429113177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5358713569602041144301805 2009517588600765429113177)
            ·
              refine ⟨1507138191450574071834883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009517588600765429113177 1507138191450574071834883)
              ·
                refine ⟨2260707287175861107752325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507138191450574071834883 2260707287175861107752325)
                ·
                  refine ⟨423882616345473957703561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2260707287175861107752325 423882616345473957703561)
                  ·
                    rfl

theorem cell20_928697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_928697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928697 prefixEnd_928697 := by exact prefixLift 928697
  have htrace : WordTrace (prefixWord ++ tailWord_928697) baseStart_928697 baseEnd_928697 := by
    simpa [prefixWord, tailWord_928697, baseEnd_928697] using wordTrace_append hprefix tailTrace_928697
  have hstable : (prefixWord ++ tailWord_928697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928697).length < 2 ^ (prefixWord ++ tailWord_928697).sum := by decide
  have hdescent : baseEnd_928697 < baseStart_928697 := by decide
  rcases family_descends (prefixWord ++ tailWord_928697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928711 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 3]
def baseStart_928711 : Nat := 118140960795 + 928711 * 2 ^ 59
def prefixEnd_928711 : Nat := 4983230072969 + 3 ^ 40 * 928711 * 2
def baseEnd_928711 : Nat := 423889006326952131236837

theorem tailTrace_928711 : CollatzResearch.WordTrace tailWord_928711 prefixEnd_928711 423889006326952131236837 := by
  unfold tailWord_928711
  simp only [CollatzResearch.WordTrace]
  refine ⟨33872872938446133056225987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22581915292297422037483991 33872872938446133056225987)
  ·
    refine ⟨50809309407669199584338981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33872872938446133056225987 50809309407669199584338981)
    ·
      refine ⟨9526745513937974922063559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50809309407669199584338981 9526745513937974922063559)
      ·
        refine ⟨14290118270906962383095339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9526745513937974922063559 14290118270906962383095339)
        ·
          refine ⟨21435177406360443574643009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14290118270906962383095339 21435177406360443574643009)
          ·
            refine ⟨16076383054770332680982257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21435177406360443574643009 16076383054770332680982257)
            ·
              refine ⟨12057287291077749510736693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16076383054770332680982257 12057287291077749510736693)
              ·
                refine ⟨1130370683538539016631565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12057287291077749510736693 1130370683538539016631565)
                ·
                  refine ⟨423889006326952131236837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130370683538539016631565 423889006326952131236837)
                  ·
                    rfl

theorem cell20_928711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 3].length) (baseStart_928711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928711 prefixEnd_928711 := by exact prefixLift 928711
  have htrace : WordTrace (prefixWord ++ tailWord_928711) baseStart_928711 baseEnd_928711 := by
    simpa [prefixWord, tailWord_928711, baseEnd_928711] using wordTrace_append hprefix tailTrace_928711
  have hstable : (prefixWord ++ tailWord_928711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928711).length < 2 ^ (prefixWord ++ tailWord_928711).sum := by decide
  have hdescent : baseEnd_928711 < baseStart_928711 := by decide
  rcases family_descends (prefixWord ++ tailWord_928711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928717 : List Nat := [1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_928717 : Nat := 118140960795 + 928717 * 2 ^ 59
def prefixEnd_928717 : Nat := 4983230072969 + 3 ^ 40 * 928717 * 2
def baseEnd_928717 : Nat := 141297248296814259012271

theorem tailTrace_928717 : CollatzResearch.WordTrace tailWord_928717 prefixEnd_928717 141297248296814259012271 := by
  unfold tailWord_928717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33873091776424396080944405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22582061184282930720629603 33873091776424396080944405)
  ·
    refine ⟨1587801177019893566294269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33873091776424396080944405 1587801177019893566294269)
    ·
      refine ⟨595425441382460087360351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1587801177019893566294269 595425441382460087360351)
      ·
        refine ⟨893138162073690131040527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595425441382460087360351 893138162073690131040527)
        ·
          refine ⟨1339707243110535196560791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893138162073690131040527 1339707243110535196560791)
          ·
            refine ⟨2009560864665802794841187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1339707243110535196560791 2009560864665802794841187)
            ·
              refine ⟨3014341296998704192261781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009560864665802794841187 3014341296998704192261781)
              ·
                refine ⟨141297248296814259012271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3014341296998704192261781 141297248296814259012271)
                ·
                  rfl

theorem cell20_928717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_928717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928717 prefixEnd_928717 := by exact prefixLift 928717
  have htrace : WordTrace (prefixWord ++ tailWord_928717) baseStart_928717 baseEnd_928717 := by
    simpa [prefixWord, tailWord_928717, baseEnd_928717] using wordTrace_append hprefix tailTrace_928717
  have hstable : (prefixWord ++ tailWord_928717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928717).length < 2 ^ (prefixWord ++ tailWord_928717).sum := by decide
  have hdescent : baseEnd_928717 < baseStart_928717 := by decide
  rcases family_descends (prefixWord ++ tailWord_928717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928801 : List Nat := [1, 2, 3, 2, 3, 9]
def baseStart_928801 : Nat := 118140960795 + 928801 * 2 ^ 59
def prefixEnd_928801 : Nat := 4983230072969 + 3 ^ 40 * 928801 * 2
def baseEnd_928801 : Nat := 15701114251085622897647

theorem tailTrace_928801 : CollatzResearch.WordTrace tailWord_928801 prefixEnd_928801 15701114251085622897647 := by
  unfold tailWord_928801
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876155508120078427002257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22584103672080052284668171 33876155508120078427002257)
  ·
    refine ⟨25407116631090058820251693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33876155508120078427002257 25407116631090058820251693)
    ·
      refine ⟨9527668736658772057594385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25407116631090058820251693 9527668736658772057594385)
      ·
        refine ⟨7145751552494079043195789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9527668736658772057594385 7145751552494079043195789)
        ·
          refine ⟨2679656832185279641198421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7145751552494079043195789 2679656832185279641198421)
          ·
            refine ⟨15701114251085622897647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2679656832185279641198421 15701114251085622897647)
            ·
              rfl

theorem cell20_928801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 9].length) (baseStart_928801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928801 prefixEnd_928801 := by exact prefixLift 928801
  have htrace : WordTrace (prefixWord ++ tailWord_928801) baseStart_928801 baseEnd_928801 := by
    simpa [prefixWord, tailWord_928801, baseEnd_928801] using wordTrace_append hprefix tailTrace_928801
  have hstable : (prefixWord ++ tailWord_928801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928801).length < 2 ^ (prefixWord ++ tailWord_928801).sum := by decide
  have hdescent : baseEnd_928801 < baseStart_928801 := by decide
  rcases family_descends (prefixWord ++ tailWord_928801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928804 : List Nat := [2, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_928804 : Nat := 118140960795 + 928804 * 2 ^ 59
def prefixEnd_928804 : Nat := 4983230072969 + 3 ^ 40 * 928804 * 2
def baseEnd_928804 : Nat := 423931454061057141136457

theorem tailTrace_928804 : CollatzResearch.WordTrace tailWord_928804 prefixEnd_928804 423931454061057141136457 := by
  unfold tailWord_928804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938132463554604969680733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22584176618072806626240977 16938132463554604969680733)
  ·
    refine ⟨6351799673832976863630275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16938132463554604969680733 6351799673832976863630275)
    ·
      refine ⟨9527699510749465295445413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6351799673832976863630275 9527699510749465295445413)
      ·
        refine ⟨1786443658265524742896015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9527699510749465295445413 1786443658265524742896015)
        ·
          refine ⟨2679665487398287114344023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786443658265524742896015 2679665487398287114344023)
          ·
            refine ⟨4019498231097430671516035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679665487398287114344023 4019498231097430671516035)
            ·
              refine ⟨6029247346646146007274053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4019498231097430671516035 6029247346646146007274053)
              ·
                refine ⟨1130483877496152376363885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6029247346646146007274053 1130483877496152376363885)
                ·
                  refine ⟨423931454061057141136457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130483877496152376363885 423931454061057141136457)
                  ·
                    rfl

theorem cell20_928804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_928804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928804 prefixEnd_928804 := by exact prefixLift 928804
  have htrace : WordTrace (prefixWord ++ tailWord_928804) baseStart_928804 baseEnd_928804 := by
    simpa [prefixWord, tailWord_928804, baseEnd_928804] using wordTrace_append hprefix tailTrace_928804
  have hstable : (prefixWord ++ tailWord_928804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928804).length < 2 ^ (prefixWord ++ tailWord_928804).sum := by decide
  have hdescent : baseEnd_928804 < baseStart_928804 := by decide
  rcases family_descends (prefixWord ++ tailWord_928804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928807 : List Nat := [1, 1, 7, 1, 1, 2, 1, 4, 2]
def baseStart_928807 : Nat := 118140960795 + 928807 * 2 ^ 59
def prefixEnd_928807 : Nat := 4983230072969 + 3 ^ 40 * 928807 * 2
def baseEnd_928807 : Nat := 423932823342802464036445

theorem tailTrace_928807 : CollatzResearch.WordTrace tailWord_928807 prefixEnd_928807 423932823342802464036445 := by
  unfold tailWord_928807
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876374346098341451720675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22584249564065560967813783 33876374346098341451720675)
  ·
    refine ⟨50814561519147512177581013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33876374346098341451720675 50814561519147512177581013)
    ·
      refine ⟨1190966285605019816662055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50814561519147512177581013 1190966285605019816662055)
      ·
        refine ⟨1786449428407529724993083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1190966285605019816662055 1786449428407529724993083)
        ·
          refine ⟨2679674142611294587489625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786449428407529724993083 2679674142611294587489625)
          ·
            refine ⟨2009755606958470940617219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679674142611294587489625 2009755606958470940617219)
            ·
              refine ⟨3014633410437706410925829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2009755606958470940617219 3014633410437706410925829)
              ·
                refine ⟨565243764457069952048593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3014633410437706410925829 565243764457069952048593)
                ·
                  refine ⟨423932823342802464036445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565243764457069952048593 423932823342802464036445)
                  ·
                    rfl

theorem cell20_928807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 2].length) (baseStart_928807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928807 prefixEnd_928807 := by exact prefixLift 928807
  have htrace : WordTrace (prefixWord ++ tailWord_928807) baseStart_928807 baseEnd_928807 := by
    simpa [prefixWord, tailWord_928807, baseEnd_928807] using wordTrace_append hprefix tailTrace_928807
  have hstable : (prefixWord ++ tailWord_928807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928807).length < 2 ^ (prefixWord ++ tailWord_928807).sum := by decide
  have hdescent : baseEnd_928807 < baseStart_928807 := by decide
  rcases family_descends (prefixWord ++ tailWord_928807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928811 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 2]
def baseStart_928811 : Nat := 118140960795 + 928811 * 2 ^ 59
def prefixEnd_928811 : Nat := 4983230072969 + 3 ^ 40 * 928811 * 2
def baseEnd_928811 : Nat := 423934649051796227903095

theorem tailTrace_928811 : CollatzResearch.WordTrace tailWord_928811 prefixEnd_928811 423934649051796227903095 := by
  unfold tailWord_928811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33876520238083850134866287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22584346825389233423244191 33876520238083850134866287)
  ·
    refine ⟨50814780357125775202299431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33876520238083850134866287 50814780357125775202299431)
    ·
      refine ⟨76222170535688662803449147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50814780357125775202299431 76222170535688662803449147)
      ·
        refine ⟨114333255803532994205173721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76222170535688662803449147 114333255803532994205173721)
        ·
          refine ⟨85749941852649745653880291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114333255803532994205173721 85749941852649745653880291)
          ·
            refine ⟨128624912778974618480820437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85749941852649745653880291 128624912778974618480820437)
            ·
              refine ⟨3014646393257217620644229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 128624912778974618480820437 3014646393257217620644229)
              ·
                refine ⟨565246198735728303870793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3014646393257217620644229 565246198735728303870793)
                ·
                  refine ⟨423934649051796227903095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565246198735728303870793 423934649051796227903095)
                  ·
                    rfl

theorem cell20_928811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 2].length) (baseStart_928811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928811 prefixEnd_928811 := by exact prefixLift 928811
  have htrace : WordTrace (prefixWord ++ tailWord_928811) baseStart_928811 baseEnd_928811 := by
    simpa [prefixWord, tailWord_928811, baseEnd_928811] using wordTrace_append hprefix tailTrace_928811
  have hstable : (prefixWord ++ tailWord_928811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928811).length < 2 ^ (prefixWord ++ tailWord_928811).sum := by decide
  have hdescent : baseEnd_928811 < baseStart_928811 := by decide
  rcases family_descends (prefixWord ++ tailWord_928811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928832 : List Nat := [2, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_928832 : Nat := 118140960795 + 928832 * 2 ^ 59
def prefixEnd_928832 : Nat := 4983230072969 + 3 ^ 40 * 928832 * 2
def baseEnd_928832 : Nat := 423944234024013488203009

theorem tailTrace_928832 : CollatzResearch.WordTrace tailWord_928832 prefixEnd_928832 423944234024013488203009 := by
  unfold tailWord_928832
  simp only [CollatzResearch.WordTrace]
  refine ⟨16938643085503885360690375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22584857447338513814253833 16938643085503885360690375)
  ·
    refine ⟨25407964628255828041035563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16938643085503885360690375 25407964628255828041035563)
    ·
      refine ⟨38111946942383742061553345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25407964628255828041035563 38111946942383742061553345)
      ·
        refine ⟨28583960206787806546165009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38111946942383742061553345 28583960206787806546165009)
        ·
          refine ⟨21437970155090854909623757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28583960206787806546165009 21437970155090854909623757)
          ·
            refine ⟨8039238808159070591108909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21437970155090854909623757 8039238808159070591108909)
            ·
              refine ⟨3014714553059651471665841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8039238808159070591108909 3014714553059651471665841)
              ·
                refine ⟨2261035914794738603749381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3014714553059651471665841 2261035914794738603749381)
                ·
                  refine ⟨423944234024013488203009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261035914794738603749381 423944234024013488203009)
                  ·
                    rfl

theorem cell20_928832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_928832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928832 prefixEnd_928832 := by exact prefixLift 928832
  have htrace : WordTrace (prefixWord ++ tailWord_928832) baseStart_928832 baseEnd_928832 := by
    simpa [prefixWord, tailWord_928832, baseEnd_928832] using wordTrace_append hprefix tailTrace_928832
  have hstable : (prefixWord ++ tailWord_928832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928832).length < 2 ^ (prefixWord ++ tailWord_928832).sum := by decide
  have hdescent : baseEnd_928832 < baseStart_928832 := by decide
  rcases family_descends (prefixWord ++ tailWord_928832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928845 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 2]
def baseStart_928845 : Nat := 118140960795 + 928845 * 2 ^ 59
def prefixEnd_928845 : Nat := 4983230072969 + 3 ^ 40 * 928845 * 2
def baseEnd_928845 : Nat := 423950167578243220769623

theorem tailTrace_928845 : CollatzResearch.WordTrace tailWord_928845 prefixEnd_928845 423950167578243220769623 := by
  unfold tailWord_928845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877760319960673941603989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22585173546640449294402659 33877760319960673941603989)
  ·
    refine ⟨1588020014998156591012687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33877760319960673941603989 1588020014998156591012687)
    ·
      refine ⟨2382030022497234886519031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1588020014998156591012687 2382030022497234886519031)
      ·
        refine ⟨3573045033745852329778547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2382030022497234886519031 3573045033745852329778547)
        ·
          refine ⟨5359567550618778494667821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573045033745852329778547 5359567550618778494667821)
          ·
            refine ⟨2009837831482041935500433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5359567550618778494667821 2009837831482041935500433)
            ·
              refine ⟨1507378373611531451625325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009837831482041935500433 1507378373611531451625325)
              ·
                refine ⟨565266890104324294359497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1507378373611531451625325 565266890104324294359497)
                ·
                  refine ⟨423950167578243220769623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565266890104324294359497 423950167578243220769623)
                  ·
                    rfl

theorem cell20_928845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_928845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928845 prefixEnd_928845 := by exact prefixLift 928845
  have htrace : WordTrace (prefixWord ++ tailWord_928845) baseStart_928845 baseEnd_928845 := by
    simpa [prefixWord, tailWord_928845, baseEnd_928845] using wordTrace_append hprefix tailTrace_928845
  have hstable : (prefixWord ++ tailWord_928845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928845).length < 2 ^ (prefixWord ++ tailWord_928845).sum := by decide
  have hdescent : baseEnd_928845 < baseStart_928845 := by decide
  rcases family_descends (prefixWord ++ tailWord_928845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928849 : List Nat := [1, 2, 2, 1, 3, 1, 3, 5, 2]
def baseStart_928849 : Nat := 118140960795 + 928849 * 2 ^ 59
def prefixEnd_928849 : Nat := 4983230072969 + 3 ^ 40 * 928849 * 2
def baseEnd_928849 : Nat := 423951993287236984636273

theorem tailTrace_928849 : CollatzResearch.WordTrace tailWord_928849 prefixEnd_928849 423951993287236984636273 := by
  unfold tailWord_928849
  simp only [CollatzResearch.WordTrace]
  refine ⟨33877906211946182624749601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22585270807964121749833067 33877906211946182624749601)
  ·
    refine ⟨25408429658959636968562201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33877906211946182624749601 25408429658959636968562201)
    ·
      refine ⟨19056322244219727726421651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25408429658959636968562201 19056322244219727726421651)
      ·
        refine ⟨28584483366329591589632477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19056322244219727726421651 28584483366329591589632477)
        ·
          refine ⟨10719181262373596846112179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28584483366329591589632477 10719181262373596846112179)
          ·
            refine ⟨16078771893560395269168269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10719181262373596846112179 16078771893560395269168269)
            ·
              refine ⟨6029539460085148225938101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16078771893560395269168269 6029539460085148225938101)
              ·
                refine ⟨565269324382982646181697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6029539460085148225938101 565269324382982646181697)
                ·
                  refine ⟨423951993287236984636273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565269324382982646181697 423951993287236984636273)
                  ·
                    rfl

theorem cell20_928849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_928849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928849 prefixEnd_928849 := by exact prefixLift 928849
  have htrace : WordTrace (prefixWord ++ tailWord_928849) baseStart_928849 baseEnd_928849 := by
    simpa [prefixWord, tailWord_928849, baseEnd_928849] using wordTrace_append hprefix tailTrace_928849
  have hstable : (prefixWord ++ tailWord_928849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928849).length < 2 ^ (prefixWord ++ tailWord_928849).sum := by decide
  have hdescent : baseEnd_928849 < baseStart_928849 := by decide
  rcases family_descends (prefixWord ++ tailWord_928849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928862 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_928862 : Nat := 118140960795 + 928862 * 2 ^ 59
def prefixEnd_928862 : Nat := 4983230072969 + 3 ^ 40 * 928862 * 2
def baseEnd_928862 : Nat := 423957926841466717202887

theorem tailTrace_928862 : CollatzResearch.WordTrace tailWord_928862 prefixEnd_928862 423957926841466717202887 := by
  unfold tailWord_928862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4234797545112385730621605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22585586907266057229981893 4234797545112385730621605)
  ·
    refine ⟨794024539708572324491551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4234797545112385730621605 794024539708572324491551)
    ·
      refine ⟨1191036809562858486737327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 794024539708572324491551 1191036809562858486737327)
      ·
        refine ⟨1786555214344287730105991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1191036809562858486737327 1786555214344287730105991)
        ·
          refine ⟨2679832821516431595158987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786555214344287730105991 2679832821516431595158987)
          ·
            refine ⟨4019749232274647392738481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2679832821516431595158987 4019749232274647392738481)
            ·
              refine ⟨3014811924205985544553861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4019749232274647392738481 3014811924205985544553861)
              ·
                refine ⟨565277235788622289603849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3014811924205985544553861 565277235788622289603849)
                ·
                  refine ⟨423957926841466717202887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565277235788622289603849 423957926841466717202887)
                  ·
                    rfl

theorem cell20_928862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_928862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928862 prefixEnd_928862 := by exact prefixLift 928862
  have htrace : WordTrace (prefixWord ++ tailWord_928862) baseStart_928862 baseEnd_928862 := by
    simpa [prefixWord, tailWord_928862, baseEnd_928862] using wordTrace_append hprefix tailTrace_928862
  have hstable : (prefixWord ++ tailWord_928862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928862).length < 2 ^ (prefixWord ++ tailWord_928862).sum := by decide
  have hdescent : baseEnd_928862 < baseStart_928862 := by decide
  rcases family_descends (prefixWord ++ tailWord_928862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928866 : List Nat := [3, 3, 2, 2, 1, 2, 2, 1, 4]
def baseStart_928866 : Nat := 118140960795 + 928866 * 2 ^ 59
def prefixEnd_928866 : Nat := 4983230072969 + 3 ^ 40 * 928866 * 2
def baseEnd_928866 : Nat := 423959752550460481069537

theorem tailTrace_928866 : CollatzResearch.WordTrace tailWord_928866 prefixEnd_928866 423959752550460481069537 := by
  unfold tailWord_928866
  simp only [CollatzResearch.WordTrace]
  refine ⟨8469631563221148632029613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22585684168589729685412301 8469631563221148632029613)
  ·
    refine ⟨3176111836207930737011105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8469631563221148632029613 3176111836207930737011105)
    ·
      refine ⟨2382083877155948052758329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3176111836207930737011105 2382083877155948052758329)
      ·
        refine ⟨1786562907866961039568747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2382083877155948052758329 1786562907866961039568747)
        ·
          refine ⟨2679844361800441559353121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786562907866961039568747 2679844361800441559353121)
          ·
            refine ⟨2009883271350331169514841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679844361800441559353121 2009883271350331169514841)
            ·
              refine ⟨1507412453512748377136131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2009883271350331169514841 1507412453512748377136131)
              ·
                refine ⟨2261118680269122565704197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1507412453512748377136131 2261118680269122565704197)
                ·
                  refine ⟨423959752550460481069537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261118680269122565704197 423959752550460481069537)
                  ·
                    rfl

theorem cell20_928866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_928866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928866 prefixEnd_928866 := by exact prefixLift 928866
  have htrace : WordTrace (prefixWord ++ tailWord_928866) baseStart_928866 baseEnd_928866 := by
    simpa [prefixWord, tailWord_928866, baseEnd_928866] using wordTrace_append hprefix tailTrace_928866
  have hstable : (prefixWord ++ tailWord_928866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928866).length < 2 ^ (prefixWord ++ tailWord_928866).sum := by decide
  have hdescent : baseEnd_928866 < baseStart_928866 := by decide
  rcases family_descends (prefixWord ++ tailWord_928866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928880 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_928880 : Nat := 118140960795 + 928880 * 2 ^ 59
def prefixEnd_928880 : Nat := 4983230072969 + 3 ^ 40 * 928880 * 2
def baseEnd_928880 : Nat := 423966142531938654602813

theorem tailTrace_928880 : CollatzResearch.WordTrace tailWord_928880 prefixEnd_928880 423966142531938654602813 := by
  unfold tailWord_928880
  simp only [CollatzResearch.WordTrace]
  refine ⟨16939518437416937459564047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22586024583222583279418729 16939518437416937459564047)
  ·
    refine ⟨25409277656125406189346071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16939518437416937459564047 25409277656125406189346071)
    ·
      refine ⟨38113916484188109284019107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25409277656125406189346071 38113916484188109284019107)
      ·
        refine ⟨57170874726282163926028661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38113916484188109284019107 57170874726282163926028661)
        ·
          refine ⟨5359769505588952868065187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57170874726282163926028661 5359769505588952868065187)
          ·
            refine ⟨8039654258383429302097781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5359769505588952868065187 8039654258383429302097781)
            ·
              refine ⟨753717586723446497071667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8039654258383429302097781 753717586723446497071667)
              ·
                refine ⟨1130576380085169745607501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753717586723446497071667 1130576380085169745607501)
                ·
                  refine ⟨423966142531938654602813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130576380085169745607501 423966142531938654602813)
                  ·
                    rfl

theorem cell20_928880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_928880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928880 prefixEnd_928880 := by exact prefixLift 928880
  have htrace : WordTrace (prefixWord ++ tailWord_928880) baseStart_928880 baseEnd_928880 := by
    simpa [prefixWord, tailWord_928880, baseEnd_928880] using wordTrace_append hprefix tailTrace_928880
  have hstable : (prefixWord ++ tailWord_928880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928880).length < 2 ^ (prefixWord ++ tailWord_928880).sum := by decide
  have hdescent : baseEnd_928880 < baseStart_928880 := by decide
  rcases family_descends (prefixWord ++ tailWord_928880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928932 : List Nat := [2, 3, 1, 2, 3, 2, 2, 5]
def baseStart_928932 : Nat := 118140960795 + 928932 * 2 ^ 59
def prefixEnd_928932 : Nat := 4983230072969 + 3 ^ 40 * 928932 * 2
def baseEnd_928932 : Nat := 141329958916285861623089

theorem tailTrace_928932 : CollatzResearch.WordTrace tailWord_928932 prefixEnd_928932 141329958916285861623089 := by
  unfold tailWord_928932
  simp only [CollatzResearch.WordTrace]
  refine ⟨16940466735322743900010525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22587288980430325200014033 16940466735322743900010525)
  ·
    refine ⟨6352675025746028962503947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16940466735322743900010525 6352675025746028962503947)
    ·
      refine ⟨9529012538619043443755921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6352675025746028962503947 9529012538619043443755921)
      ·
        refine ⟨7146759403964282582816941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9529012538619043443755921 7146759403964282582816941)
        ·
          refine ⟨2680034776486605968556353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7146759403964282582816941 2680034776486605968556353)
          ·
            refine ⟨2010026082364954476417265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680034776486605968556353 2010026082364954476417265)
            ·
              refine ⟨1507519561773715857312949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010026082364954476417265 1507519561773715857312949)
              ·
                refine ⟨141329958916285861623089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507519561773715857312949 141329958916285861623089)
                ·
                  rfl

theorem cell20_928932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 5].length) (baseStart_928932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928932 prefixEnd_928932 := by exact prefixLift 928932
  have htrace : WordTrace (prefixWord ++ tailWord_928932) baseStart_928932 baseEnd_928932 := by
    simpa [prefixWord, tailWord_928932, baseEnd_928932] using wordTrace_append hprefix tailTrace_928932
  have hstable : (prefixWord ++ tailWord_928932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928932).length < 2 ^ (prefixWord ++ tailWord_928932).sum := by decide
  have hdescent : baseEnd_928932 < baseStart_928932 := by decide
  rcases family_descends (prefixWord ++ tailWord_928932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928935 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 3]
def baseStart_928935 : Nat := 118140960795 + 928935 * 2 ^ 59
def prefixEnd_928935 : Nat := 4983230072969 + 3 ^ 40 * 928935 * 2
def baseEnd_928935 : Nat := 423991246030602907769255

theorem tailTrace_928935 : CollatzResearch.WordTrace tailWord_928935 prefixEnd_928935 423991246030602907769255 := by
  unfold tailWord_928935
  simp only [CollatzResearch.WordTrace]
  refine ⟨33881042889634619312380259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22587361926423079541586839 33881042889634619312380259)
  ·
    refine ⟨50821564334451928968570389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33881042889634619312380259 50821564334451928968570389)
    ·
      refine ⟨2382260828177434170401737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50821564334451928968570389 2382260828177434170401737)
      ·
        refine ⟨1786695621133075627801303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2382260828177434170401737 1786695621133075627801303)
        ·
          refine ⟨2680043431699613441701955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786695621133075627801303 2680043431699613441701955)
          ·
            refine ⟨4020065147549420162552933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2680043431699613441701955 4020065147549420162552933)
            ·
              refine ⟨753762215165516280478675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4020065147549420162552933 753762215165516280478675)
              ·
                refine ⟨1130643322748274420718013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 753762215165516280478675 1130643322748274420718013)
                ·
                  refine ⟨423991246030602907769255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1130643322748274420718013 423991246030602907769255)
                  ·
                    rfl

theorem cell20_928935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 3].length) (baseStart_928935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928935 prefixEnd_928935 := by exact prefixLift 928935
  have htrace : WordTrace (prefixWord ++ tailWord_928935) baseStart_928935 baseEnd_928935 := by
    simpa [prefixWord, tailWord_928935, baseEnd_928935] using wordTrace_append hprefix tailTrace_928935
  have hstable : (prefixWord ++ tailWord_928935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928935).length < 2 ^ (prefixWord ++ tailWord_928935).sum := by decide
  have hdescent : baseEnd_928935 < baseStart_928935 := by decide
  rcases family_descends (prefixWord ++ tailWord_928935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928953 : List Nat := [1, 2, 1, 4, 1, 3, 2, 6]
def baseStart_928953 : Nat := 118140960795 + 928953 * 2 ^ 59
def prefixEnd_928953 : Nat := 4983230072969 + 3 ^ 40 * 928953 * 2
def baseEnd_928953 : Nat := 141333153907024948389727

theorem tailTrace_928953 : CollatzResearch.WordTrace tailWord_928953 prefixEnd_928953 141333153907024948389727 := by
  unfold tailWord_928953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33881699403569408386535513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22587799602379605591023675 33881699403569408386535513)
  ·
    refine ⟨25411274552677056289901635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33881699403569408386535513 25411274552677056289901635)
    ·
      refine ⟨38116911829015584434852453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25411274552677056289901635 38116911829015584434852453)
      ·
        refine ⟨7146920967940422081534835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38116911829015584434852453 7146920967940422081534835)
        ·
          refine ⟨10720381451910633122302253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7146920967940422081534835 10720381451910633122302253)
          ·
            refine ⟨4020143044466487420863345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10720381451910633122302253 4020143044466487420863345)
            ·
              refine ⟨3015107283349865565647509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4020143044466487420863345 3015107283349865565647509)
              ·
                refine ⟨141333153907024948389727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3015107283349865565647509 141333153907024948389727)
                ·
                  rfl

theorem cell20_928953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 6].length) (baseStart_928953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928953 prefixEnd_928953 := by exact prefixLift 928953
  have htrace : WordTrace (prefixWord ++ tailWord_928953) baseStart_928953 baseEnd_928953 := by
    simpa [prefixWord, tailWord_928953, baseEnd_928953] using wordTrace_append hprefix tailTrace_928953
  have hstable : (prefixWord ++ tailWord_928953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928953).length < 2 ^ (prefixWord ++ tailWord_928953).sum := by decide
  have hdescent : baseEnd_928953 < baseStart_928953 := by decide
  rcases family_descends (prefixWord ++ tailWord_928953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928966 : List Nat := [6, 1, 2, 2, 1, 8]
def baseStart_928966 : Nat := 118140960795 + 928966 * 2 ^ 59
def prefixEnd_928966 : Nat := 4983230072969 + 3 ^ 40 * 928966 * 2
def baseEnd_928966 : Nat := 15703903528714984360585

theorem tailTrace_928966 : CollatzResearch.WordTrace tailWord_928966 prefixEnd_928966 15703903528714984360585 := by
  unfold tailWord_928966
  simp only [CollatzResearch.WordTrace]
  refine ⟨1058817923516322237711211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22588115701681541071172501 1058817923516322237711211)
  ·
    refine ⟨1588226885274483356566817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1058817923516322237711211 1588226885274483356566817)
    ·
      refine ⟨1191170163955862517425113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1588226885274483356566817 1191170163955862517425113)
      ·
        refine ⟨893377622966896888068835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1191170163955862517425113 893377622966896888068835)
        ·
          refine ⟨1340066434450345332103253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893377622966896888068835 1340066434450345332103253)
          ·
            refine ⟨15703903528714984360585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1340066434450345332103253 15703903528714984360585)
            ·
              rfl

theorem cell20_928966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 8].length) (baseStart_928966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928966 prefixEnd_928966 := by exact prefixLift 928966
  have htrace : WordTrace (prefixWord ++ tailWord_928966) baseStart_928966 baseEnd_928966 := by
    simpa [prefixWord, tailWord_928966, baseEnd_928966] using wordTrace_append hprefix tailTrace_928966
  have hstable : (prefixWord ++ tailWord_928966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928966).length < 2 ^ (prefixWord ++ tailWord_928966).sum := by decide
  have hdescent : baseEnd_928966 < baseStart_928966 := by decide
  rcases family_descends (prefixWord ++ tailWord_928966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_928991 : List Nat := [1, 1, 2, 3, 2, 1, 5, 5]
def baseStart_928991 : Nat := 118140960795 + 928991 * 2 ^ 59
def prefixEnd_928991 : Nat := 4983230072969 + 3 ^ 40 * 928991 * 2
def baseEnd_928991 : Nat := 141338935318838533967453

theorem tailTrace_928991 : CollatzResearch.WordTrace tailWord_928991 prefixEnd_928991 141338935318838533967453 := by
  unfold tailWord_928991
  simp only [CollatzResearch.WordTrace]
  refine ⟨33883085377431740876418827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22588723584954493917612551 33883085377431740876418827)
  ·
    refine ⟨50824628066147611314628241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33883085377431740876418827 50824628066147611314628241)
    ·
      refine ⟨38118471049610708485971181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50824628066147611314628241 38118471049610708485971181)
      ·
        refine ⟨14294426643604015682239193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38118471049610708485971181 14294426643604015682239193)
        ·
          refine ⟨10720819982703011761679395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14294426643604015682239193 10720819982703011761679395)
          ·
            refine ⟨16081229974054517642519093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10720819982703011761679395 16081229974054517642519093)
            ·
              refine ⟨1507615310067611028986165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16081229974054517642519093 1507615310067611028986165)
              ·
                refine ⟨141338935318838533967453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507615310067611028986165 141338935318838533967453)
                ·
                  rfl

theorem cell20_928991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 5].length) (baseStart_928991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_928991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_928991 prefixEnd_928991 := by exact prefixLift 928991
  have htrace : WordTrace (prefixWord ++ tailWord_928991) baseStart_928991 baseEnd_928991 := by
    simpa [prefixWord, tailWord_928991, baseEnd_928991] using wordTrace_append hprefix tailTrace_928991
  have hstable : (prefixWord ++ tailWord_928991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_928991).length < 2 ^ (prefixWord ++ tailWord_928991).sum := by decide
  have hdescent : baseEnd_928991 < baseStart_928991 := by decide
  rcases family_descends (prefixWord ++ tailWord_928991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929060 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_929060 : Nat := 118140960795 + 929060 * 2 ^ 59
def prefixEnd_929060 : Nat := 4983230072969 + 3 ^ 40 * 929060 * 2
def baseEnd_929060 : Nat := 424048299436658028602077

theorem tailTrace_929060 : CollatzResearch.WordTrace tailWord_929060 prefixEnd_929060 424048299436658028602077 := by
  unfold tailWord_929060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16942801007090882830340317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22590401342787843773787089 16942801007090882830340317)
  ·
    refine ⟨6353550377659081061377619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16942801007090882830340317 6353550377659081061377619)
    ·
      refine ⟨9530325566488621592066429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6353550377659081061377619 9530325566488621592066429)
      ·
        refine ⟨3573872087433233097024911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9530325566488621592066429 3573872087433233097024911)
        ·
          refine ⟨5360808131149849645537367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3573872087433233097024911 5360808131149849645537367)
          ·
            refine ⟨8041212196724774468306051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5360808131149849645537367 8041212196724774468306051)
            ·
              refine ⟨12061818295087161702459077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8041212196724774468306051 12061818295087161702459077)
              ·
                refine ⟨2261590930328842819211077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12061818295087161702459077 2261590930328842819211077)
                ·
                  refine ⟨424048299436658028602077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261590930328842819211077 424048299436658028602077)
                  ·
                    rfl

theorem cell20_929060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_929060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929060 prefixEnd_929060 := by exact prefixLift 929060
  have htrace : WordTrace (prefixWord ++ tailWord_929060) baseStart_929060 baseEnd_929060 := by
    simpa [prefixWord, tailWord_929060, baseEnd_929060] using wordTrace_append hprefix tailTrace_929060
  have hstable : (prefixWord ++ tailWord_929060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929060).length < 2 ^ (prefixWord ++ tailWord_929060).sum := by decide
  have hdescent : baseEnd_929060 < baseStart_929060 := by decide
  rcases family_descends (prefixWord ++ tailWord_929060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929105 : List Nat := [1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_929105 : Nat := 118140960795 + 929105 * 2 ^ 59
def prefixEnd_929105 : Nat := 4983230072969 + 3 ^ 40 * 929105 * 2
def baseEnd_929105 : Nat := 141356279554279290700631

theorem tailTrace_929105 : CollatzResearch.WordTrace tailWord_929105 prefixEnd_929105 141356279554279290700631 := by
  unfold tailWord_929105
  simp only [CollatzResearch.WordTrace]
  refine ⟨33887243299018738346068769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22591495532679158897379179 33887243299018738346068769)
  ·
    refine ⟨25415432474264053759551577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33887243299018738346068769 25415432474264053759551577)
    ·
      refine ⟨19061574355698040319663683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25415432474264053759551577 19061574355698040319663683)
      ·
        refine ⟨28592361533547060479495525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19061574355698040319663683 28592361533547060479495525)
        ·
          refine ⟨5361067787540073839905411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28592361533547060479495525 5361067787540073839905411)
          ·
            refine ⟨8041601681310110759858117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5361067787540073839905411 8041601681310110759858117)
            ·
              refine ⟨1507800315245645767473397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8041601681310110759858117 1507800315245645767473397)
              ·
                refine ⟨141356279554279290700631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507800315245645767473397 141356279554279290700631)
                ·
                  rfl

theorem cell20_929105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_929105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929105 prefixEnd_929105 := by exact prefixLift 929105
  have htrace : WordTrace (prefixWord ++ tailWord_929105) baseStart_929105 baseEnd_929105 := by
    simpa [prefixWord, tailWord_929105, baseEnd_929105] using wordTrace_append hprefix tailTrace_929105
  have hstable : (prefixWord ++ tailWord_929105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929105).length < 2 ^ (prefixWord ++ tailWord_929105).sum := by decide
  have hdescent : baseEnd_929105 < baseStart_929105 := by decide
  rcases family_descends (prefixWord ++ tailWord_929105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929119 : List Nat := [1, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_929119 : Nat := 118140960795 + 929119 * 2 ^ 59
def prefixEnd_929119 : Nat := 4983230072969 + 3 ^ 40 * 929119 * 2
def baseEnd_929119 : Nat := 424075228644316045635169

theorem tailTrace_929119 : CollatzResearch.WordTrace tailWord_929119 prefixEnd_929119 424075228644316045635169 := by
  unfold tailWord_929119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33887753920968018737078411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22591835947312012491385607 33887753920968018737078411)
  ·
    refine ⟨50831630881452028105617617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33887753920968018737078411 50831630881452028105617617)
    ·
      refine ⟨38123723161089021079213213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50831630881452028105617617 38123723161089021079213213)
      ·
        refine ⟨14296396185408382904704955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38123723161089021079213213 14296396185408382904704955)
        ·
          refine ⟨21444594278112574357057433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14296396185408382904704955 21444594278112574357057433)
          ·
            refine ⟨16083445708584430767793075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21444594278112574357057433 16083445708584430767793075)
            ·
              refine ⟨24125168562876646151689613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16083445708584430767793075 24125168562876646151689613)
              ·
                refine ⟨9046938211078742306883605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24125168562876646151689613 9046938211078742306883605)
                ·
                  refine ⟨424075228644316045635169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9046938211078742306883605 424075228644316045635169)
                  ·
                    rfl

theorem cell20_929119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_929119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929119 prefixEnd_929119 := by exact prefixLift 929119
  have htrace : WordTrace (prefixWord ++ tailWord_929119) baseStart_929119 baseEnd_929119 := by
    simpa [prefixWord, tailWord_929119, baseEnd_929119] using wordTrace_append hprefix tailTrace_929119
  have hstable : (prefixWord ++ tailWord_929119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929119).length < 2 ^ (prefixWord ++ tailWord_929119).sum := by decide
  have hdescent : baseEnd_929119 < baseStart_929119 := by decide
  rcases family_descends (prefixWord ++ tailWord_929119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929160 : List Nat := [2, 1, 3, 3, 1, 4, 1, 5]
def baseStart_929160 : Nat := 118140960795 + 929160 * 2 ^ 59
def prefixEnd_929160 : Nat := 4983230072969 + 3 ^ 40 * 929160 * 2
def baseEnd_929160 : Nat := 141364647387167375089445

theorem tailTrace_929160 : CollatzResearch.WordTrace tailWord_929160 prefixEnd_929160 141364647387167375089445 := by
  unfold tailWord_929160
  simp only [CollatzResearch.WordTrace]
  refine ⟨16944624656909741369660467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22592832875879655159547289 16944624656909741369660467)
  ·
    refine ⟨25416936985364612054490701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16944624656909741369660467 25416936985364612054490701)
    ·
      refine ⟨9531351369511729520434013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25416936985364612054490701 9531351369511729520434013)
      ·
        refine ⟨3574256763566898570162755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9531351369511729520434013 3574256763566898570162755)
        ·
          refine ⟨5361385145350347855244133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3574256763566898570162755 5361385145350347855244133)
          ·
            refine ⟨1005259714753190222858275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5361385145350347855244133 1005259714753190222858275)
            ·
              refine ⟨1507889572129785334287413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005259714753190222858275 1507889572129785334287413)
              ·
                refine ⟨141364647387167375089445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1507889572129785334287413 141364647387167375089445)
                ·
                  rfl

theorem cell20_929160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 5].length) (baseStart_929160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929160 prefixEnd_929160 := by exact prefixLift 929160
  have htrace : WordTrace (prefixWord ++ tailWord_929160) baseStart_929160 baseEnd_929160 := by
    simpa [prefixWord, tailWord_929160, baseEnd_929160] using wordTrace_append hprefix tailTrace_929160
  have hstable : (prefixWord ++ tailWord_929160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929160).length < 2 ^ (prefixWord ++ tailWord_929160).sum := by decide
  have hdescent : baseEnd_929160 < baseStart_929160 := by decide
  rcases family_descends (prefixWord ++ tailWord_929160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929170 : List Nat := [3, 2, 3, 3, 1, 1, 1, 2, 4]
def baseStart_929170 : Nat := 118140960795 + 929170 * 2 ^ 59
def prefixEnd_929170 : Nat := 4983230072969 + 3 ^ 40 * 929170 * 2
def baseEnd_929170 : Nat := 424098506433986534934961

theorem tailTrace_929170 : CollatzResearch.WordTrace tailWord_929170 prefixEnd_929170 424098506433986534934961 := by
  unfold tailWord_929170
  simp only [CollatzResearch.WordTrace]
  refine ⟨8472403510945813611796241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22593076029188836298123309 8472403510945813611796241)
  ·
    refine ⟨6354302633209360208847181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8472403510945813611796241 6354302633209360208847181)
    ·
      refine ⟨2382863487453510078317693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6354302633209360208847181 2382863487453510078317693)
      ·
        refine ⟨893573807795066279369135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2382863487453510078317693 893573807795066279369135)
        ·
          refine ⟨1340360711692599419053703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893573807795066279369135 1340360711692599419053703)
          ·
            refine ⟨2010541067538899128580555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340360711692599419053703 2010541067538899128580555)
            ·
              refine ⟨3015811601308348692870833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010541067538899128580555 3015811601308348692870833)
              ·
                refine ⟨2261858700981261519653125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3015811601308348692870833 2261858700981261519653125)
                ·
                  refine ⟨424098506433986534934961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2261858700981261519653125 424098506433986534934961)
                  ·
                    rfl

theorem cell20_929170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_929170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929170 prefixEnd_929170 := by exact prefixLift 929170
  have htrace : WordTrace (prefixWord ++ tailWord_929170) baseStart_929170 baseEnd_929170 := by
    simpa [prefixWord, tailWord_929170, baseEnd_929170] using wordTrace_append hprefix tailTrace_929170
  have hstable : (prefixWord ++ tailWord_929170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929170).length < 2 ^ (prefixWord ++ tailWord_929170).sum := by decide
  have hdescent : baseEnd_929170 < baseStart_929170 := by decide
  rcases family_descends (prefixWord ++ tailWord_929170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929188 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 5]
def baseStart_929188 : Nat := 118140960795 + 929188 * 2 ^ 59
def prefixEnd_929188 : Nat := 4983230072969 + 3 ^ 40 * 929188 * 2
def baseEnd_929188 : Nat := 424106722124458472334887

theorem tailTrace_929188 : CollatzResearch.WordTrace tailWord_929188 prefixEnd_929188 424106722124458472334887 := by
  unfold tailWord_929188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16945135278859021760670109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22593513705145362347560145 16945135278859021760670109)
  ·
    refine ⟨6354425729572133160251291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16945135278859021760670109 6354425729572133160251291)
    ·
      refine ⟨9531638594358199740376937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6354425729572133160251291 9531638594358199740376937)
      ·
        refine ⟨7148728945768649805282703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9531638594358199740376937 7148728945768649805282703)
        ·
          refine ⟨10723093418652974707924055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7148728945768649805282703 10723093418652974707924055)
          ·
            refine ⟨16084640127979462061886083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10723093418652974707924055 16084640127979462061886083)
            ·
              refine ⟨24126960191969193092829125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16084640127979462061886083 24126960191969193092829125)
              ·
                refine ⟨4523805035994223704905461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24126960191969193092829125 4523805035994223704905461)
                ·
                  refine ⟨424106722124458472334887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4523805035994223704905461 424106722124458472334887)
                  ·
                    rfl

theorem cell20_929188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_929188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929188 prefixEnd_929188 := by exact prefixLift 929188
  have htrace : WordTrace (prefixWord ++ tailWord_929188) baseStart_929188 baseEnd_929188 := by
    simpa [prefixWord, tailWord_929188, baseEnd_929188] using wordTrace_append hprefix tailTrace_929188
  have hstable : (prefixWord ++ tailWord_929188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929188).length < 2 ^ (prefixWord ++ tailWord_929188).sum := by decide
  have hdescent : baseEnd_929188 < baseStart_929188 := by decide
  rcases family_descends (prefixWord ++ tailWord_929188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929205 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 5]
def baseStart_929205 : Nat := 118140960795 + 929205 * 2 ^ 59
def prefixEnd_929205 : Nat := 4983230072969 + 3 ^ 40 * 929205 * 2
def baseEnd_929205 : Nat := 424114481387681968768151

theorem tailTrace_929205 : CollatzResearch.WordTrace tailWord_929205 prefixEnd_929205 424114481387681968768151 := by
  unfold tailWord_929205
  simp only [CollatzResearch.WordTrace]
  refine ⟨33890890598656455424709069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22593927065770970283139379 33890890598656455424709069)
  ·
    refine ⟨12709083974496170784265901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33890890598656455424709069 12709083974496170784265901)
    ·
      refine ⟨4765906490436064044099713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12709083974496170784265901 4765906490436064044099713)
      ·
        refine ⟨3574429867827048033074785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4765906490436064044099713 3574429867827048033074785)
        ·
          refine ⟨2680822400870286024806089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3574429867827048033074785 2680822400870286024806089)
          ·
            refine ⟨2010616800652714518604567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2680822400870286024806089 2010616800652714518604567)
            ·
              refine ⟨3015925200979071777906851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010616800652714518604567 3015925200979071777906851)
              ·
                refine ⟨4523887801468607666860277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3015925200979071777906851 4523887801468607666860277)
                ·
                  refine ⟨424114481387681968768151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4523887801468607666860277 424114481387681968768151)
                  ·
                    rfl

theorem cell20_929205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_929205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929205 prefixEnd_929205 := by exact prefixLift 929205
  have htrace : WordTrace (prefixWord ++ tailWord_929205) baseStart_929205 baseEnd_929205 := by
    simpa [prefixWord, tailWord_929205, baseEnd_929205] using wordTrace_append hprefix tailTrace_929205
  have hstable : (prefixWord ++ tailWord_929205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929205).length < 2 ^ (prefixWord ++ tailWord_929205).sum := by decide
  have hdescent : baseEnd_929205 < baseStart_929205 := by decide
  rcases family_descends (prefixWord ++ tailWord_929205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929236 : List Nat := [2, 4, 1, 2, 3, 1, 1, 6]
def baseStart_929236 : Nat := 118140960795 + 929236 * 2 ^ 59
def prefixEnd_929236 : Nat := 4983230072969 + 3 ^ 40 * 929236 * 2
def baseEnd_929236 : Nat := 141376210210794546244897

theorem tailTrace_929236 : CollatzResearch.WordTrace tailWord_929236 prefixEnd_929236 141376210210794546244897 := by
  unfold tailWord_929236
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946010630772073859543781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22594680841029431812725041 16946010630772073859543781)
  ·
    refine ⟨3177376993269763848664459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16946010630772073859543781 3177376993269763848664459)
    ·
      refine ⟨4766065489904645772996689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177376993269763848664459 4766065489904645772996689)
      ·
        refine ⟨3574549117428484329747517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4766065489904645772996689 3574549117428484329747517)
        ·
          refine ⟨1340455919035681623655319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3574549117428484329747517 1340455919035681623655319)
          ·
            refine ⟨2010683878553522435482979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340455919035681623655319 2010683878553522435482979)
            ·
              refine ⟨3016025817830283653224469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2010683878553522435482979 3016025817830283653224469)
              ·
                refine ⟨141376210210794546244897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3016025817830283653224469 141376210210794546244897)
                ·
                  rfl

theorem cell20_929236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_929236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929236 prefixEnd_929236 := by exact prefixLift 929236
  have htrace : WordTrace (prefixWord ++ tailWord_929236) baseStart_929236 baseEnd_929236 := by
    simpa [prefixWord, tailWord_929236, baseEnd_929236] using wordTrace_append hprefix tailTrace_929236
  have hstable : (prefixWord ++ tailWord_929236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929236).length < 2 ^ (prefixWord ++ tailWord_929236).sum := by decide
  have hdescent : baseEnd_929236 < baseStart_929236 := by decide
  rcases family_descends (prefixWord ++ tailWord_929236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929264 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_929264 : Nat := 118140960795 + 929264 * 2 ^ 59
def prefixEnd_929264 : Nat := 4983230072969 + 3 ^ 40 * 929264 * 2
def baseEnd_929264 : Nat := 424141410595339985801243

theorem tailTrace_929264 : CollatzResearch.WordTrace tailWord_929264 prefixEnd_929264 424141410595339985801243 := by
  unfold tailWord_929264
  simp only [CollatzResearch.WordTrace]
  refine ⟨16946521252721354250553423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22595361670295139000737897 16946521252721354250553423)
  ·
    refine ⟨25419781879082031375830135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16946521252721354250553423 25419781879082031375830135)
    ·
      refine ⟨38129672818623047063745203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25419781879082031375830135 38129672818623047063745203)
      ·
        refine ⟨57194509227934570595617805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38129672818623047063745203 57194509227934570595617805)
        ·
          refine ⟨21447940960475463973356677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57194509227934570595617805 21447940960475463973356677)
          ·
            refine ⟨4021488930089149495004377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21447940960475463973356677 4021488930089149495004377)
            ·
              refine ⟨3016116697566862121253283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021488930089149495004377 3016116697566862121253283)
              ·
                refine ⟨4524175046350293181879925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3016116697566862121253283 4524175046350293181879925)
                ·
                  refine ⟨424141410595339985801243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4524175046350293181879925 424141410595339985801243)
                  ·
                    rfl

theorem cell20_929264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_929264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929264 prefixEnd_929264 := by exact prefixLift 929264
  have htrace : WordTrace (prefixWord ++ tailWord_929264) baseStart_929264 baseEnd_929264 := by
    simpa [prefixWord, tailWord_929264, baseEnd_929264] using wordTrace_append hprefix tailTrace_929264
  have hstable : (prefixWord ++ tailWord_929264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929264).length < 2 ^ (prefixWord ++ tailWord_929264).sum := by decide
  have hdescent : baseEnd_929264 < baseStart_929264 := by decide
  rcases family_descends (prefixWord ++ tailWord_929264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929271 : List Nat := [1, 1, 3, 1, 1, 1, 1, 7, 4]
def baseStart_929271 : Nat := 118140960795 + 929271 * 2 ^ 59
def prefixEnd_929271 : Nat := 4983230072969 + 3 ^ 40 * 929271 * 2
def baseEnd_929271 : Nat := 424144605586079072567881

theorem tailTrace_929271 : CollatzResearch.WordTrace tailWord_929271 prefixEnd_929271 424144605586079072567881 := by
  unfold tailWord_929271
  simp only [CollatzResearch.WordTrace]
  refine ⟨33893297816417348696611667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22595531877611565797741111 33893297816417348696611667)
  ·
    refine ⟨50839946724626023044917501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33893297816417348696611667 50839946724626023044917501)
    ·
      refine ⟨19064980021734758641844063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50839946724626023044917501 19064980021734758641844063)
      ·
        refine ⟨28597470032602137962766095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19064980021734758641844063 28597470032602137962766095)
        ·
          refine ⟨42896205048903206944149143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28597470032602137962766095 42896205048903206944149143)
          ·
            refine ⟨64344307573354810416223715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42896205048903206944149143 64344307573354810416223715)
            ·
              refine ⟨96516461360032215624335573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64344307573354810416223715 96516461360032215624335573)
              ·
                refine ⟨2262104563125755053695365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 96516461360032215624335573 2262104563125755053695365)
                ·
                  refine ⟨424144605586079072567881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262104563125755053695365 424144605586079072567881)
                  ·
                    rfl

theorem cell20_929271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_929271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929271 prefixEnd_929271 := by exact prefixLift 929271
  have htrace : WordTrace (prefixWord ++ tailWord_929271) baseStart_929271 baseEnd_929271 := by
    simpa [prefixWord, tailWord_929271, baseEnd_929271] using wordTrace_append hprefix tailTrace_929271
  have hstable : (prefixWord ++ tailWord_929271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929271).length < 2 ^ (prefixWord ++ tailWord_929271).sum := by decide
  have hdescent : baseEnd_929271 < baseStart_929271 := by decide
  rcases family_descends (prefixWord ++ tailWord_929271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929316 : List Nat := [2, 3, 1, 14]
def baseStart_929316 : Nat := 118140960795 + 929316 * 2 ^ 59
def prefixEnd_929316 : Nat := 4983230072969 + 3 ^ 40 * 929316 * 2
def baseEnd_929316 : Nat := 1745535575359090189579

theorem tailTrace_929316 : CollatzResearch.WordTrace tailWord_929316 prefixEnd_929316 1745535575359090189579 := by
  unfold tailWord_929316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16947469550627160690999901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22596626067502880921333201 16947469550627160690999901)
  ·
    refine ⟨6355301081485185259124963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16947469550627160690999901 6355301081485185259124963)
    ·
      refine ⟨9532951622227777888687445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6355301081485185259124963 9532951622227777888687445)
      ·
        refine ⟨1745535575359090189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 9532951622227777888687445 1745535575359090189579)
        ·
          rfl

theorem cell20_929316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 14].length) (baseStart_929316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929316 prefixEnd_929316 := by exact prefixLift 929316
  have htrace : WordTrace (prefixWord ++ tailWord_929316) baseStart_929316 baseEnd_929316 := by
    simpa [prefixWord, tailWord_929316, baseEnd_929316] using wordTrace_append hprefix tailTrace_929316
  have hstable : (prefixWord ++ tailWord_929316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929316).length < 2 ^ (prefixWord ++ tailWord_929316).sum := by decide
  have hdescent : baseEnd_929316 < baseStart_929316 := by decide
  rcases family_descends (prefixWord ++ tailWord_929316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929333 : List Nat := [1, 3, 3, 1, 1, 3, 3, 5]
def baseStart_929333 : Nat := 118140960795 + 929333 * 2 ^ 59
def prefixEnd_929333 : Nat := 4983230072969 + 3 ^ 40 * 929333 * 2
def baseEnd_929333 : Nat := 141390968025160804166987

theorem tailTrace_929333 : CollatzResearch.WordTrace tailWord_929333 prefixEnd_929333 141390968025160804166987 := by
  unfold tailWord_929333
  simp only [CollatzResearch.WordTrace]
  refine ⟨33895559142192733285368653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22597039428128488856912435 33895559142192733285368653)
  ·
    refine ⟨12710834678322274982013245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33895559142192733285368653 12710834678322274982013245)
    ·
      refine ⟨4766563004370853118254967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12710834678322274982013245 4766563004370853118254967)
      ·
        refine ⟨7149844506556279677382451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4766563004370853118254967 7149844506556279677382451)
        ·
          refine ⟨10724766759834419516073677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7149844506556279677382451 10724766759834419516073677)
          ·
            refine ⟨4021787534937907318527629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10724766759834419516073677 4021787534937907318527629)
            ·
              refine ⟨1508170325601715244447861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4021787534937907318527629 1508170325601715244447861)
              ·
                refine ⟨141390968025160804166987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1508170325601715244447861 141390968025160804166987)
                ·
                  rfl

theorem cell20_929333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_929333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929333 prefixEnd_929333 := by exact prefixLift 929333
  have htrace : WordTrace (prefixWord ++ tailWord_929333) baseStart_929333 baseEnd_929333 := by
    simpa [prefixWord, tailWord_929333, baseEnd_929333] using wordTrace_append hprefix tailTrace_929333
  have hstable : (prefixWord ++ tailWord_929333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929333).length < 2 ^ (prefixWord ++ tailWord_929333).sum := by decide
  have hdescent : baseEnd_929333 < baseStart_929333 := by decide
  rcases family_descends (prefixWord ++ tailWord_929333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929381 : List Nat := [1, 3, 1, 3, 3, 1, 2, 4, 2]
def baseStart_929381 : Nat := 118140960795 + 929381 * 2 ^ 59
def prefixEnd_929381 : Nat := 4983230072969 + 3 ^ 40 * 929381 * 2
def baseEnd_929381 : Nat := 424194812583407578900765

theorem tailTrace_929381 : CollatzResearch.WordTrace tailWord_929381 prefixEnd_929381 424194812583407578900765 := by
  unfold tailWord_929381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33897309846018837483115997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22598206564012558322077331 33897309846018837483115997)
  ·
    refine ⟨12711491192257064056168499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33897309846018837483115997 12711491192257064056168499)
    ·
      refine ⟨19067236788385596084252749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12711491192257064056168499 19067236788385596084252749)
      ·
        refine ⟨7150213795644598531594781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19067236788385596084252749 7150213795644598531594781)
        ·
          refine ⟨2681330173366724449348043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7150213795644598531594781 2681330173366724449348043)
          ·
            refine ⟨4021995260050086674022065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681330173366724449348043 4021995260050086674022065)
            ·
              refine ⟨3016496445037565005516549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4021995260050086674022065 3016496445037565005516549)
              ·
                refine ⟨565593083444543438534353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3016496445037565005516549 565593083444543438534353)
                ·
                  refine ⟨424194812583407578900765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565593083444543438534353 424194812583407578900765)
                  ·
                    rfl

theorem cell20_929381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_929381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929381 prefixEnd_929381 := by exact prefixLift 929381
  have htrace : WordTrace (prefixWord ++ tailWord_929381) baseStart_929381 baseEnd_929381 := by
    simpa [prefixWord, tailWord_929381, baseEnd_929381] using wordTrace_append hprefix tailTrace_929381
  have hstable : (prefixWord ++ tailWord_929381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929381).length < 2 ^ (prefixWord ++ tailWord_929381).sum := by decide
  have hdescent : baseEnd_929381 < baseStart_929381 := by decide
  rcases family_descends (prefixWord ++ tailWord_929381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929385 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 4]
def baseStart_929385 : Nat := 118140960795 + 929385 * 2 ^ 59
def prefixEnd_929385 : Nat := 4983230072969 + 3 ^ 40 * 929385 * 2
def baseEnd_929385 : Nat := 424196638292401342767415

theorem tailTrace_929385 : CollatzResearch.WordTrace tailWord_929385 prefixEnd_929385 424196638292401342767415 := by
  unfold tailWord_929385
  simp only [CollatzResearch.WordTrace]
  refine ⟨33897455738004346166261609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22598303825336230777507739 33897455738004346166261609)
  ·
    refine ⟨25423091803503259624696207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33897455738004346166261609 25423091803503259624696207)
    ·
      refine ⟨38134637705254889437044311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25423091803503259624696207 38134637705254889437044311)
      ·
        refine ⟨57201956557882334155566467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38134637705254889437044311 57201956557882334155566467)
        ·
          refine ⟨85802934836823501233349701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57201956557882334155566467 85802934836823501233349701)
          ·
            refine ⟨16088050281904406481253069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85802934836823501233349701 16088050281904406481253069)
            ·
              refine ⟨6033018855714152430469901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16088050281904406481253069 6033018855714152430469901)
              ·
                refine ⟨2262382070892807161426213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6033018855714152430469901 2262382070892807161426213)
                ·
                  refine ⟨424196638292401342767415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262382070892807161426213 424196638292401342767415)
                  ·
                    rfl

theorem cell20_929385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_929385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929385 prefixEnd_929385 := by exact prefixLift 929385
  have htrace : WordTrace (prefixWord ++ tailWord_929385) baseStart_929385 baseEnd_929385 := by
    simpa [prefixWord, tailWord_929385, baseEnd_929385] using wordTrace_append hprefix tailTrace_929385
  have hstable : (prefixWord ++ tailWord_929385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929385).length < 2 ^ (prefixWord ++ tailWord_929385).sum := by decide
  have hdescent : baseEnd_929385 < baseStart_929385 := by decide
  rcases family_descends (prefixWord ++ tailWord_929385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929409 : List Nat := [1, 2, 4, 2, 1, 3, 1, 6]
def baseStart_929409 : Nat := 118140960795 + 929409 * 2 ^ 59
def prefixEnd_929409 : Nat := 4983230072969 + 3 ^ 40 * 929409 * 2
def baseEnd_929409 : Nat := 141402530848787975322439

theorem tailTrace_929409 : CollatzResearch.WordTrace tailWord_929409 prefixEnd_929409 141402530848787975322439 := by
  unfold tailWord_929409
  simp only [CollatzResearch.WordTrace]
  refine ⟨33898331089917398265135281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22598887393278265510090187 33898331089917398265135281)
  ·
    refine ⟨25423748317438048698851461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33898331089917398265135281 25423748317438048698851461)
    ·
      refine ⟨4766952809519634131034649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25423748317438048698851461 4766952809519634131034649)
      ·
        refine ⟨3575214607139725598275987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4766952809519634131034649 3575214607139725598275987)
        ·
          refine ⟨5362821910709588397413981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3575214607139725598275987 5362821910709588397413981)
          ·
            refine ⟨2011058216516095649030243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5362821910709588397413981 2011058216516095649030243)
            ·
              refine ⟨3016587324774143473545365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011058216516095649030243 3016587324774143473545365)
              ·
                refine ⟨141402530848787975322439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3016587324774143473545365 141402530848787975322439)
                ·
                  rfl

theorem cell20_929409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 6].length) (baseStart_929409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929409 prefixEnd_929409 := by exact prefixLift 929409
  have htrace : WordTrace (prefixWord ++ tailWord_929409) baseStart_929409 baseEnd_929409 := by
    simpa [prefixWord, tailWord_929409, baseEnd_929409] using wordTrace_append hprefix tailTrace_929409
  have hstable : (prefixWord ++ tailWord_929409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929409).length < 2 ^ (prefixWord ++ tailWord_929409).sum := by decide
  have hdescent : baseEnd_929409 < baseStart_929409 := by decide
  rcases family_descends (prefixWord ++ tailWord_929409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929426 : List Nat := [3, 2, 3, 1, 3, 2, 6]
def baseStart_929426 : Nat := 118140960795 + 929426 * 2 ^ 59
def prefixEnd_929426 : Nat := 4983230072969 + 3 ^ 40 * 929426 * 2
def baseEnd_929426 : Nat := 47135039089954158044509

theorem tailTrace_929426 : CollatzResearch.WordTrace tailWord_929426 prefixEnd_929426 47135039089954158044509 := by
  unfold tailWord_929426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8474737782713952542126033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22599300753903873445669421 8474737782713952542126033)
  ·
    refine ⟨6356053337035464406594525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8474737782713952542126033 6356053337035464406594525)
    ·
      refine ⟨2383520001388299152472947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6356053337035464406594525 2383520001388299152472947)
      ·
        refine ⟨3575280002082448728709421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383520001388299152472947 3575280002082448728709421)
        ·
          refine ⟨1340730000780918273266033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3575280002082448728709421 1340730000780918273266033)
          ·
            refine ⟨1005547500585688704949525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340730000780918273266033 1005547500585688704949525)
            ·
              refine ⟨47135039089954158044509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1005547500585688704949525 47135039089954158044509)
              ·
                rfl

theorem cell20_929426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 6].length) (baseStart_929426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929426 prefixEnd_929426 := by exact prefixLift 929426
  have htrace : WordTrace (prefixWord ++ tailWord_929426) baseStart_929426 baseEnd_929426 := by
    simpa [prefixWord, tailWord_929426, baseEnd_929426] using wordTrace_append hprefix tailTrace_929426
  have hstable : (prefixWord ++ tailWord_929426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929426).length < 2 ^ (prefixWord ++ tailWord_929426).sum := by decide
  have hdescent : baseEnd_929426 < baseStart_929426 := by decide
  rcases family_descends (prefixWord ++ tailWord_929426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929436 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 4]
def baseStart_929436 : Nat := 118140960795 + 929436 * 2 ^ 59
def prefixEnd_929436 : Nat := 4983230072969 + 3 ^ 40 * 929436 * 2
def baseEnd_929436 : Nat := 424219916082071832067207

theorem tailTrace_929436 : CollatzResearch.WordTrace tailWord_929436 prefixEnd_929436 424219916082071832067207 := by
  unfold tailWord_929436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949657930409790938184081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22599543907213054584245441 16949657930409790938184081)
  ·
    refine ⟨12712243447807343203638061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16949657930409790938184081 12712243447807343203638061)
    ·
      refine ⟨4767091292927753701364273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12712243447807343203638061 4767091292927753701364273)
      ·
        refine ⟨3575318469695815276023205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4767091292927753701364273 3575318469695815276023205)
        ·
          refine ⟨670372213067965364254351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3575318469695815276023205 670372213067965364254351)
          ·
            refine ⟨1005558319601948046381527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670372213067965364254351 1005558319601948046381527)
            ·
              refine ⟨1508337479402922069572291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005558319601948046381527 1508337479402922069572291)
              ·
                refine ⟨2262506219104383104358437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508337479402922069572291 2262506219104383104358437)
                ·
                  refine ⟨424219916082071832067207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262506219104383104358437 424219916082071832067207)
                  ·
                    rfl

theorem cell20_929436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 4].length) (baseStart_929436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929436 prefixEnd_929436 := by exact prefixLift 929436
  have htrace : WordTrace (prefixWord ++ tailWord_929436) baseStart_929436 baseEnd_929436 := by
    simpa [prefixWord, tailWord_929436, baseEnd_929436] using wordTrace_append hprefix tailTrace_929436
  have hstable : (prefixWord ++ tailWord_929436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929436).length < 2 ^ (prefixWord ++ tailWord_929436).sum := by decide
  have hdescent : baseEnd_929436 < baseStart_929436 := by decide
  rcases family_descends (prefixWord ++ tailWord_929436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929440 : List Nat := [2, 1, 1, 4, 3, 1, 3, 1, 4]
def baseStart_929440 : Nat := 118140960795 + 929440 * 2 ^ 59
def prefixEnd_929440 : Nat := 4983230072969 + 3 ^ 40 * 929440 * 2
def baseEnd_929440 : Nat := 424221741791065595933857

theorem tailTrace_929440 : CollatzResearch.WordTrace tailWord_929440 prefixEnd_929440 424221741791065595933857 := by
  unfold tailWord_929440
  simp only [CollatzResearch.WordTrace]
  refine ⟨16949730876402545279756887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22599641168536727039675849 16949730876402545279756887)
  ·
    refine ⟨25424596314603817919635331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16949730876402545279756887 25424596314603817919635331)
    ·
      refine ⟨38136894471905726879452997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25424596314603817919635331 38136894471905726879452997)
      ·
        refine ⟨7150667713482323789897437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38136894471905726879452997 7150667713482323789897437)
        ·
          refine ⟨2681500392555871421211539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7150667713482323789897437 2681500392555871421211539)
          ·
            refine ⟨4022250588833807131817309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681500392555871421211539 4022250588833807131817309)
            ·
              refine ⟨1508343970812677674431491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4022250588833807131817309 1508343970812677674431491)
              ·
                refine ⟨2262515956219016511647237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508343970812677674431491 2262515956219016511647237)
                ·
                  refine ⟨424221741791065595933857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2262515956219016511647237 424221741791065595933857)
                  ·
                    rfl

theorem cell20_929440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 1, 4].length) (baseStart_929440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929440 prefixEnd_929440 := by exact prefixLift 929440
  have htrace : WordTrace (prefixWord ++ tailWord_929440) baseStart_929440 baseEnd_929440 := by
    simpa [prefixWord, tailWord_929440, baseEnd_929440] using wordTrace_append hprefix tailTrace_929440
  have hstable : (prefixWord ++ tailWord_929440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929440).length < 2 ^ (prefixWord ++ tailWord_929440).sum := by decide
  have hdescent : baseEnd_929440 < baseStart_929440 := by decide
  rcases family_descends (prefixWord ++ tailWord_929440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929513 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_929513 : Nat := 118140960795 + 929513 * 2 ^ 59
def prefixEnd_929513 : Nat := 4983230072969 + 3 ^ 40 * 929513 * 2
def baseEnd_929513 : Nat := 424255060980201786500225

theorem tailTrace_929513 : CollatzResearch.WordTrace tailWord_929513 prefixEnd_929513 424255060980201786500225 := by
  unfold tailWord_929513
  simp only [CollatzResearch.WordTrace]
  refine ⟨33902124281540624026921193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22601416187693749351280795 33902124281540624026921193)
  ·
    refine ⟨25426593211155468020190895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33902124281540624026921193 25426593211155468020190895)
    ·
      refine ⟨38139889816733202030286343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25426593211155468020190895 38139889816733202030286343)
      ·
        refine ⟨57209834725099803045429515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38139889816733202030286343 57209834725099803045429515)
        ·
          refine ⟨85814752087649704568144273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57209834725099803045429515 85814752087649704568144273)
          ·
            refine ⟨64361064065737278426108205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85814752087649704568144273 64361064065737278426108205)
            ·
              refine ⟨24135399024651479409790577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64361064065737278426108205 24135399024651479409790577)
              ·
                refine ⟨18101549268488609557342933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24135399024651479409790577 18101549268488609557342933)
                ·
                  refine ⟨424255060980201786500225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18101549268488609557342933 424255060980201786500225)
                  ·
                    rfl

theorem cell20_929513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_929513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929513 prefixEnd_929513 := by exact prefixLift 929513
  have htrace : WordTrace (prefixWord ++ tailWord_929513) baseStart_929513 baseEnd_929513 := by
    simpa [prefixWord, tailWord_929513, baseEnd_929513] using wordTrace_append hprefix tailTrace_929513
  have hstable : (prefixWord ++ tailWord_929513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929513).length < 2 ^ (prefixWord ++ tailWord_929513).sum := by decide
  have hdescent : baseEnd_929513 < baseStart_929513 := by decide
  rcases family_descends (prefixWord ++ tailWord_929513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929543 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 3]
def baseStart_929543 : Nat := 118140960795 + 929543 * 2 ^ 59
def prefixEnd_929543 : Nat := 4983230072969 + 3 ^ 40 * 929543 * 2
def baseEnd_929543 : Nat := 424268753797655015500103

theorem tailTrace_929543 : CollatzResearch.WordTrace tailWord_929543 prefixEnd_929543 424268753797655015500103 := by
  unfold tailWord_929543
  simp only [CollatzResearch.WordTrace]
  refine ⟨33903218471431939150513283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22602145647621292767008855 33903218471431939150513283)
  ·
    refine ⟨50854827707147908725769925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33903218471431939150513283 50854827707147908725769925)
    ·
      refine ⟨9535280195090232886081861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50854827707147908725769925 9535280195090232886081861)
      ·
        refine ⟨1787865036579418666140349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9535280195090232886081861 1787865036579418666140349)
        ·
          refine ⟨670449388717281999802631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1787865036579418666140349 670449388717281999802631)
          ·
            refine ⟨1005674083075922999703947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670449388717281999802631 1005674083075922999703947)
            ·
              refine ⟨1508511124613884499555921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005674083075922999703947 1508511124613884499555921)
              ·
                refine ⟨1131383343460413374666941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1508511124613884499555921 1131383343460413374666941)
                ·
                  refine ⟨424268753797655015500103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131383343460413374666941 424268753797655015500103)
                  ·
                    rfl

theorem cell20_929543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 3].length) (baseStart_929543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929543 prefixEnd_929543 := by exact prefixLift 929543
  have htrace : WordTrace (prefixWord ++ tailWord_929543) baseStart_929543 baseEnd_929543 := by
    simpa [prefixWord, tailWord_929543, baseEnd_929543] using wordTrace_append hprefix tailTrace_929543
  have hstable : (prefixWord ++ tailWord_929543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929543).length < 2 ^ (prefixWord ++ tailWord_929543).sum := by decide
  have hdescent : baseEnd_929543 < baseStart_929543 := by decide
  rcases family_descends (prefixWord ++ tailWord_929543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929544 : List Nat := [2, 1, 3, 2, 2, 1, 9]
def baseStart_929544 : Nat := 118140960795 + 929544 * 2 ^ 59
def prefixEnd_929544 : Nat := 4983230072969 + 3 ^ 40 * 929544 * 2
def baseEnd_929544 : Nat := 47141023358322606274085

theorem tailTrace_929544 : CollatzResearch.WordTrace tailWord_929544 prefixEnd_929544 47141023358322606274085 := by
  unfold tailWord_929544
  simp only [CollatzResearch.WordTrace]
  refine ⟨16951627472214158160649843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22602169962952210880866457 16951627472214158160649843)
  ·
    refine ⟨25427441208321237240974765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16951627472214158160649843 25427441208321237240974765)
    ·
      refine ⟨9535290453120463965365537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25427441208321237240974765 9535290453120463965365537)
      ·
        refine ⟨7151467839840347974024153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9535290453120463965365537 7151467839840347974024153)
        ·
          refine ⟨5363600879880260980518115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7151467839840347974024153 5363600879880260980518115)
          ·
            refine ⟨8045401319820391470777173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5363600879880260980518115 8045401319820391470777173)
            ·
              refine ⟨47141023358322606274085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8045401319820391470777173 47141023358322606274085)
              ·
                rfl

theorem cell20_929544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 9].length) (baseStart_929544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929544 prefixEnd_929544 := by exact prefixLift 929544
  have htrace : WordTrace (prefixWord ++ tailWord_929544) baseStart_929544 baseEnd_929544 := by
    simpa [prefixWord, tailWord_929544, baseEnd_929544] using wordTrace_append hprefix tailTrace_929544
  have hstable : (prefixWord ++ tailWord_929544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929544).length < 2 ^ (prefixWord ++ tailWord_929544).sum := by decide
  have hdescent : baseEnd_929544 < baseStart_929544 := by decide
  rcases family_descends (prefixWord ++ tailWord_929544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929588 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 2]
def baseStart_929588 : Nat := 118140960795 + 929588 * 2 ^ 59
def prefixEnd_929588 : Nat := 4983230072969 + 3 ^ 40 * 929588 * 2
def baseEnd_929588 : Nat := 424289293023834858999919

theorem tailTrace_929588 : CollatzResearch.WordTrace tailWord_929588 prefixEnd_929588 424289293023834858999919 := by
  unfold tailWord_929588
  simp only [CollatzResearch.WordTrace]
  refine ⟨16952429878134455917950709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22603239837512607890600945 16952429878134455917950709)
  ·
    refine ⟨1589290301075105242307879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16952429878134455917950709 1589290301075105242307879)
    ·
      refine ⟨2383935451612657863461819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1589290301075105242307879 2383935451612657863461819)
      ·
        refine ⟨3575903177418986795192729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2383935451612657863461819 3575903177418986795192729)
        ·
          refine ⟨2681927383064240096394547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3575903177418986795192729 2681927383064240096394547)
          ·
            refine ⟨4022891074596360144591821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2681927383064240096394547 4022891074596360144591821)
            ·
              refine ⟨1508584152973635054221933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4022891074596360144591821 1508584152973635054221933)
              ·
                refine ⟨565719057365113145333225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1508584152973635054221933 565719057365113145333225)
                ·
                  refine ⟨424289293023834858999919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565719057365113145333225 424289293023834858999919)
                  ·
                    rfl

theorem cell20_929588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_929588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929588 prefixEnd_929588 := by exact prefixLift 929588
  have htrace : WordTrace (prefixWord ++ tailWord_929588) baseStart_929588 baseEnd_929588 := by
    simpa [prefixWord, tailWord_929588, baseEnd_929588] using wordTrace_append hprefix tailTrace_929588
  have hstable : (prefixWord ++ tailWord_929588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929588).length < 2 ^ (prefixWord ++ tailWord_929588).sum := by decide
  have hdescent : baseEnd_929588 < baseStart_929588 := by decide
  rcases family_descends (prefixWord ++ tailWord_929588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929599 : List Nat := [1, 1, 2, 2, 6, 2, 6]
def baseStart_929599 : Nat := 118140960795 + 929599 * 2 ^ 59
def prefixEnd_929599 : Nat := 4983230072969 + 3 ^ 40 * 929599 * 2
def baseEnd_929599 : Nat := 47143812635951967737023

theorem tailTrace_929599 : CollatzResearch.WordTrace tailWord_929599 prefixEnd_929599 47143812635951967737023 := by
  unfold tailWord_929599
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905260959229060714551851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22603507306152707143034567 33905260959229060714551851)
  ·
    refine ⟨50857891438843591071827777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33905260959229060714551851 50857891438843591071827777)
    ·
      refine ⟨38143418579132693303870833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50857891438843591071827777 38143418579132693303870833)
      ·
        refine ⟨28607563934349519977903125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38143418579132693303870833 28607563934349519977903125)
        ·
          refine ⟨1340979559422633748964209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28607563934349519977903125 1340979559422633748964209)
          ·
            refine ⟨1005734669566975311723157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340979559422633748964209 1005734669566975311723157)
            ·
              refine ⟨47143812635951967737023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1005734669566975311723157 47143812635951967737023)
              ·
                rfl

theorem cell20_929599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_929599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929599 prefixEnd_929599 := by exact prefixLift 929599
  have htrace : WordTrace (prefixWord ++ tailWord_929599) baseStart_929599 baseEnd_929599 := by
    simpa [prefixWord, tailWord_929599, baseEnd_929599] using wordTrace_append hprefix tailTrace_929599
  have hstable : (prefixWord ++ tailWord_929599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929599).length < 2 ^ (prefixWord ++ tailWord_929599).sum := by decide
  have hdescent : baseEnd_929599 < baseStart_929599 := by decide
  rcases family_descends (prefixWord ++ tailWord_929599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929609 : List Nat := [1, 2, 1, 1, 2, 4, 5, 2, 2]
def baseStart_929609 : Nat := 118140960795 + 929609 * 2 ^ 59
def prefixEnd_929609 : Nat := 4983230072969 + 3 ^ 40 * 929609 * 2
def baseEnd_929609 : Nat := 424298877996052119299833

theorem tailTrace_929609 : CollatzResearch.WordTrace tailWord_929609 prefixEnd_929609 424298877996052119299833 := by
  unfold tailWord_929609
  simp only [CollatzResearch.WordTrace]
  refine ⟨33905625689192832422415881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22603750459461888281610587 33905625689192832422415881)
  ·
    refine ⟨25429219266894624316811911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33905625689192832422415881 25429219266894624316811911)
    ·
      refine ⟨38143828900341936475217867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25429219266894624316811911 38143828900341936475217867)
      ·
        refine ⟨57215743350512904712826801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38143828900341936475217867 57215743350512904712826801)
        ·
          refine ⟨42911807512884678534620101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57215743350512904712826801 42911807512884678534620101)
          ·
            refine ⟨8045963908665877225241269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42911807512884678534620101 8045963908665877225241269)
            ·
              refine ⟨754309116437425989866369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8045963908665877225241269 754309116437425989866369)
              ·
                refine ⟨565731837328069492399777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754309116437425989866369 565731837328069492399777)
                ·
                  refine ⟨424298877996052119299833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565731837328069492399777 424298877996052119299833)
                  ·
                    rfl

theorem cell20_929609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_929609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929609 prefixEnd_929609 := by exact prefixLift 929609
  have htrace : WordTrace (prefixWord ++ tailWord_929609) baseStart_929609 baseEnd_929609 := by
    simpa [prefixWord, tailWord_929609, baseEnd_929609] using wordTrace_append hprefix tailTrace_929609
  have hstable : (prefixWord ++ tailWord_929609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929609).length < 2 ^ (prefixWord ++ tailWord_929609).sum := by decide
  have hdescent : baseEnd_929609 < baseStart_929609 := by decide
  rcases family_descends (prefixWord ++ tailWord_929609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929623 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_929623 : Nat := 118140960795 + 929623 * 2 ^ 59
def prefixEnd_929623 : Nat := 4983230072969 + 3 ^ 40 * 929623 * 2
def baseEnd_929623 : Nat := 424305267977530292833109

theorem tailTrace_929623 : CollatzResearch.WordTrace tailWord_929623 prefixEnd_929623 424305267977530292833109 := by
  unfold tailWord_929623
  simp only [CollatzResearch.WordTrace]
  refine ⟨33906136311142112813425523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22604090874094741875617015 33906136311142112813425523)
  ·
    refine ⟨50859204466713169220138285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33906136311142112813425523 50859204466713169220138285)
    ·
      refine ⟨19072201675017438457551857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50859204466713169220138285 19072201675017438457551857)
      ·
        refine ⟨14304151256263078843163893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19072201675017438457551857 14304151256263078843163893)
        ·
          refine ⟨1341014180274663641546615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14304151256263078843163893 1341014180274663641546615)
          ·
            refine ⟨2011521270411995462319923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341014180274663641546615 2011521270411995462319923)
            ·
              refine ⟨3017281905617993193479885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011521270411995462319923 3017281905617993193479885)
              ·
                refine ⟨1131480714606747447554957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3017281905617993193479885 1131480714606747447554957)
                ·
                  refine ⟨424305267977530292833109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131480714606747447554957 424305267977530292833109)
                  ·
                    rfl

theorem cell20_929623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_929623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929623 prefixEnd_929623 := by exact prefixLift 929623
  have htrace : WordTrace (prefixWord ++ tailWord_929623) baseStart_929623 baseEnd_929623 := by
    simpa [prefixWord, tailWord_929623, baseEnd_929623] using wordTrace_append hprefix tailTrace_929623
  have hstable : (prefixWord ++ tailWord_929623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929623).length < 2 ^ (prefixWord ++ tailWord_929623).sum := by decide
  have hdescent : baseEnd_929623 < baseStart_929623 := by decide
  rcases family_descends (prefixWord ++ tailWord_929623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929654 : List Nat := [5, 1, 1, 3, 3, 7]
def baseStart_929654 : Nat := 118140960795 + 929654 * 2 ^ 59
def prefixEnd_929654 : Nat := 4983230072969 + 3 ^ 40 * 929654 * 2
def baseEnd_929654 : Nat := 15715533971193776399987

theorem tailTrace_929654 : CollatzResearch.WordTrace tailWord_929654 prefixEnd_929654 15715533971193776399987 := by
  unfold tailWord_929654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119204185876862819237751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22604844649353203405202677 2119204185876862819237751)
  ·
    refine ⟨3178806278815294228856627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119204185876862819237751 3178806278815294228856627)
    ·
      refine ⟨4768209418222941343284941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3178806278815294228856627 4768209418222941343284941)
      ·
        refine ⟨1788078531833603003731853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4768209418222941343284941 1788078531833603003731853)
        ·
          refine ⟨670529449437601126399445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1788078531833603003731853 670529449437601126399445)
          ·
            refine ⟨15715533971193776399987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 670529449437601126399445 15715533971193776399987)
            ·
              rfl

theorem cell20_929654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 7].length) (baseStart_929654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929654 prefixEnd_929654 := by exact prefixLift 929654
  have htrace : WordTrace (prefixWord ++ tailWord_929654) baseStart_929654 baseEnd_929654 := by
    simpa [prefixWord, tailWord_929654, baseEnd_929654] using wordTrace_append hprefix tailTrace_929654
  have hstable : (prefixWord ++ tailWord_929654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929654).length < 2 ^ (prefixWord ++ tailWord_929654).sum := by decide
  have hdescent : baseEnd_929654 < baseStart_929654 := by decide
  rcases family_descends (prefixWord ++ tailWord_929654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929692 : List Nat := [2, 2, 3, 3, 1, 2, 3, 4]
def baseStart_929692 : Nat := 118140960795 + 929692 * 2 ^ 59
def prefixEnd_929692 : Nat := 4983230072969 + 3 ^ 40 * 929692 * 2
def baseEnd_929692 : Nat := 141445587152557573177609

theorem tailTrace_929692 : CollatzResearch.WordTrace tailWord_929692 prefixEnd_929692 141445587152557573177609 := by
  unfold tailWord_929692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954326473946068798843665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22605768631928091731791553 16954326473946068798843665)
  ·
    refine ⟨12715744855459551599132749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16954326473946068798843665 12715744855459551599132749)
    ·
      refine ⟨4768404320797331849674781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12715744855459551599132749 4768404320797331849674781)
      ·
        refine ⟨1788151620298999443628043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4768404320797331849674781 1788151620298999443628043)
        ·
          refine ⟨2682227430448499165442065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788151620298999443628043 2682227430448499165442065)
          ·
            refine ⟨2011670572836374374081549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2682227430448499165442065 2011670572836374374081549)
            ·
              refine ⟨754376464813640390280581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2011670572836374374081549 754376464813640390280581)
              ·
                refine ⟨141445587152557573177609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754376464813640390280581 141445587152557573177609)
                ·
                  rfl

theorem cell20_929692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 4].length) (baseStart_929692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929692 prefixEnd_929692 := by exact prefixLift 929692
  have htrace : WordTrace (prefixWord ++ tailWord_929692) baseStart_929692 baseEnd_929692 := by
    simpa [prefixWord, tailWord_929692, baseEnd_929692] using wordTrace_append hprefix tailTrace_929692
  have hstable : (prefixWord ++ tailWord_929692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929692).length < 2 ^ (prefixWord ++ tailWord_929692).sum := by decide
  have hdescent : baseEnd_929692 < baseStart_929692 := by decide
  rcases family_descends (prefixWord ++ tailWord_929692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929716 : List Nat := [2, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_929716 : Nat := 118140960795 + 929716 * 2 ^ 59
def prefixEnd_929716 : Nat := 4983230072969 + 3 ^ 40 * 929716 * 2
def baseEnd_929716 : Nat := 424347715711635302732729

theorem tailTrace_929716 : CollatzResearch.WordTrace tailWord_929716 prefixEnd_929716 424347715711635302732729 := by
  unfold tailWord_929716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16954764149902594848280501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22606352199870126464374001 16954764149902594848280501)
  ·
    refine ⟨1589509139053368267026297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16954764149902594848280501 1589509139053368267026297)
    ·
      refine ⟨1192131854290026200269723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1589509139053368267026297 1192131854290026200269723)
      ·
        refine ⟨1788197781435039300404585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192131854290026200269723 1788197781435039300404585)
        ·
          refine ⟨1341148336076279475303439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1788197781435039300404585 1341148336076279475303439)
          ·
            refine ⟨2011722504114419212955159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341148336076279475303439 2011722504114419212955159)
            ·
              refine ⟨3017583756171628819432739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2011722504114419212955159 3017583756171628819432739)
              ·
                refine ⟨4526375634257443229149109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3017583756171628819432739 4526375634257443229149109)
                ·
                  refine ⟨424347715711635302732729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4526375634257443229149109 424347715711635302732729)
                  ·
                    rfl

theorem cell20_929716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_929716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929716 prefixEnd_929716 := by exact prefixLift 929716
  have htrace : WordTrace (prefixWord ++ tailWord_929716) baseStart_929716 baseEnd_929716 := by
    simpa [prefixWord, tailWord_929716, baseEnd_929716] using wordTrace_append hprefix tailTrace_929716
  have hstable : (prefixWord ++ tailWord_929716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929716).length < 2 ^ (prefixWord ++ tailWord_929716).sum := by decide
  have hdescent : baseEnd_929716 < baseStart_929716 := by decide
  rcases family_descends (prefixWord ++ tailWord_929716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929727 : List Nat := [1, 1, 2, 2, 2, 1, 6, 1, 4]
def baseStart_929727 : Nat := 118140960795 + 929727 * 2 ^ 59
def prefixEnd_929727 : Nat := 4983230072969 + 3 ^ 40 * 929727 * 2
def baseEnd_929727 : Nat := 424352736411368153366017

theorem tailTrace_929727 : CollatzResearch.WordTrace tailWord_929727 prefixEnd_929727 424352736411368153366017 := by
  unfold tailWord_929727
  simp only [CollatzResearch.WordTrace]
  refine ⟨33909929502765338575211435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22606619668510225716807623 33909929502765338575211435)
  ·
    refine ⟨50864894254148007862817153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33909929502765338575211435 50864894254148007862817153)
    ·
      refine ⟨38148670690611005897112865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50864894254148007862817153 38148670690611005897112865)
      ·
        refine ⟨28611503017958254422834649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38148670690611005897112865 28611503017958254422834649)
        ·
          refine ⟨21458627263468690817125987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28611503017958254422834649 21458627263468690817125987)
          ·
            refine ⟨32187940895203036225688981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21458627263468690817125987 32187940895203036225688981)
            ·
              refine ⟨1508809729462642323079171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32187940895203036225688981 1508809729462642323079171)
              ·
                refine ⟨2263214594193963484618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508809729462642323079171 2263214594193963484618757)
                ·
                  refine ⟨424352736411368153366017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263214594193963484618757 424352736411368153366017)
                  ·
                    rfl

theorem cell20_929727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 1, 4].length) (baseStart_929727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929727 prefixEnd_929727 := by exact prefixLift 929727
  have htrace : WordTrace (prefixWord ++ tailWord_929727) baseStart_929727 baseEnd_929727 := by
    simpa [prefixWord, tailWord_929727, baseEnd_929727] using wordTrace_append hprefix tailTrace_929727
  have hstable : (prefixWord ++ tailWord_929727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929727).length < 2 ^ (prefixWord ++ tailWord_929727).sum := by decide
  have hdescent : baseEnd_929727 < baseStart_929727 := by decide
  rcases family_descends (prefixWord ++ tailWord_929727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929757 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 2]
def baseStart_929757 : Nat := 118140960795 + 929757 * 2 ^ 59
def prefixEnd_929757 : Nat := 4983230072969 + 3 ^ 40 * 929757 * 2
def baseEnd_929757 : Nat := 424366429228821382365895

theorem tailTrace_929757 : CollatzResearch.WordTrace tailWord_929757 prefixEnd_929757 424366429228821382365895 := by
  unfold tailWord_929757
  simp only [CollatzResearch.WordTrace]
  refine ⟨33911023692656653698803525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22607349128437769132535683 33911023692656653698803525)
  ·
    refine ⟨6358316942373122568525661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33911023692656653698803525 6358316942373122568525661)
    ·
      refine ⟨2384368853389920963197123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6358316942373122568525661 2384368853389920963197123)
      ·
        refine ⟨3576553280084881444795685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384368853389920963197123 3576553280084881444795685)
        ·
          refine ⟨670603740015915270899191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3576553280084881444795685 670603740015915270899191)
          ·
            refine ⟨1005905610023872906348787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670603740015915270899191 1005905610023872906348787)
            ·
              refine ⟨1508858415035809359523181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005905610023872906348787 1508858415035809359523181)
              ·
                refine ⟨565821905638428509821193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1508858415035809359523181 565821905638428509821193)
                ·
                  refine ⟨424366429228821382365895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565821905638428509821193 424366429228821382365895)
                  ·
                    rfl

theorem cell20_929757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_929757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929757 prefixEnd_929757 := by exact prefixLift 929757
  have htrace : WordTrace (prefixWord ++ tailWord_929757) baseStart_929757 baseEnd_929757 := by
    simpa [prefixWord, tailWord_929757, baseEnd_929757] using wordTrace_append hprefix tailTrace_929757
  have hstable : (prefixWord ++ tailWord_929757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929757).length < 2 ^ (prefixWord ++ tailWord_929757).sum := by decide
  have hdescent : baseEnd_929757 < baseStart_929757 := by decide
  rcases family_descends (prefixWord ++ tailWord_929757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929917 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 4]
def baseStart_929917 : Nat := 118140960795 + 929917 * 2 ^ 59
def prefixEnd_929917 : Nat := 4983230072969 + 3 ^ 40 * 929917 * 2
def baseEnd_929917 : Nat := 424439457588571937031907

theorem tailTrace_929917 : CollatzResearch.WordTrace tailWord_929917 prefixEnd_929917 424439457588571937031907 := by
  unfold tailWord_929917
  simp only [CollatzResearch.WordTrace]
  refine ⟨33916859372077001024628005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22611239581384667349752003 33916859372077001024628005)
  ·
    refine ⟨6359411132264437692117751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33916859372077001024628005 6359411132264437692117751)
    ·
      refine ⟨9539116698396656538176627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6359411132264437692117751 9539116698396656538176627)
      ·
        refine ⟨14308675047594984807264941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9539116698396656538176627 14308675047594984807264941)
        ·
          refine ⟨5365753142848119302724353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14308675047594984807264941 5365753142848119302724353)
          ·
            refine ⟨4024314857136089477043265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5365753142848119302724353 4024314857136089477043265)
            ·
              refine ⟨3018236142852067107782449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024314857136089477043265 3018236142852067107782449)
              ·
                refine ⟨2263677107139050330836837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018236142852067107782449 2263677107139050330836837)
                ·
                  refine ⟨424439457588571937031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263677107139050330836837 424439457588571937031907)
                  ·
                    rfl

theorem cell20_929917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_929917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929917 prefixEnd_929917 := by exact prefixLift 929917
  have htrace : WordTrace (prefixWord ++ tailWord_929917) baseStart_929917 baseEnd_929917 := by
    simpa [prefixWord, tailWord_929917, baseEnd_929917] using wordTrace_append hprefix tailTrace_929917
  have hstable : (prefixWord ++ tailWord_929917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929917).length < 2 ^ (prefixWord ++ tailWord_929917).sum := by decide
  have hdescent : baseEnd_929917 < baseStart_929917 := by decide
  rcases family_descends (prefixWord ++ tailWord_929917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929924 : List Nat := [2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_929924 : Nat := 118140960795 + 929924 * 2 ^ 59
def prefixEnd_929924 : Nat := 4983230072969 + 3 ^ 40 * 929924 * 2
def baseEnd_929924 : Nat := 141480884193103674599515

theorem tailTrace_929924 : CollatzResearch.WordTrace tailWord_929924 prefixEnd_929924 141480884193103674599515 := by
  unfold tailWord_929924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958557341525820610066413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22611409788701094146755217 16958557341525820610066413)
  ·
    refine ⟨6359459003072182728774905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16958557341525820610066413 6359459003072182728774905)
    ·
      refine ⟨4769594252304137046581179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6359459003072182728774905 4769594252304137046581179)
      ·
        refine ⟨7154391378456205569871769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769594252304137046581179 7154391378456205569871769)
        ·
          refine ⟨5365793533842154177403827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7154391378456205569871769 5365793533842154177403827)
          ·
            refine ⟨8048690300763231266105741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365793533842154177403827 8048690300763231266105741)
            ·
              refine ⟨3018258862786211724789653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8048690300763231266105741 3018258862786211724789653)
              ·
                refine ⟨141480884193103674599515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3018258862786211724789653 141480884193103674599515)
                ·
                  rfl

theorem cell20_929924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_929924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929924 prefixEnd_929924 := by exact prefixLift 929924
  have htrace : WordTrace (prefixWord ++ tailWord_929924) baseStart_929924 baseEnd_929924 := by
    simpa [prefixWord, tailWord_929924, baseEnd_929924] using wordTrace_append hprefix tailTrace_929924
  have hstable : (prefixWord ++ tailWord_929924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929924).length < 2 ^ (prefixWord ++ tailWord_929924).sum := by decide
  have hdescent : baseEnd_929924 < baseStart_929924 := by decide
  rcases family_descends (prefixWord ++ tailWord_929924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929948 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 3]
def baseStart_929948 : Nat := 118140960795 + 929948 * 2 ^ 59
def prefixEnd_929948 : Nat := 4983230072969 + 3 ^ 40 * 929948 * 2
def baseEnd_929948 : Nat := 424453606833273606998447

theorem tailTrace_929948 : CollatzResearch.WordTrace tailWord_929948 prefixEnd_929948 424453606833273606998447 := by
  unfold tailWord_929948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16958995017482346659503249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22611993356643128879337665 16958995017482346659503249)
  ·
    refine ⟨12719246263111759994627437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16958995017482346659503249 12719246263111759994627437)
    ·
      refine ⟨4769717348666909997985289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12719246263111759994627437 4769717348666909997985289)
      ·
        refine ⟨3577288011500182498488967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4769717348666909997985289 3577288011500182498488967)
        ·
          refine ⟨5365932017250273747733451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577288011500182498488967 5365932017250273747733451)
          ·
            refine ⟨8048898025875410621600177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5365932017250273747733451 8048898025875410621600177)
            ·
              refine ⟨6036673519406557966200133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8048898025875410621600177 6036673519406557966200133)
              ·
                refine ⟨1131876284888729618662525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6036673519406557966200133 1131876284888729618662525)
                ·
                  refine ⟨424453606833273606998447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131876284888729618662525 424453606833273606998447)
                  ·
                    rfl

theorem cell20_929948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 3].length) (baseStart_929948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929948 prefixEnd_929948 := by exact prefixLift 929948
  have htrace : WordTrace (prefixWord ++ tailWord_929948) baseStart_929948 baseEnd_929948 := by
    simpa [prefixWord, tailWord_929948, baseEnd_929948] using wordTrace_append hprefix tailTrace_929948
  have hstable : (prefixWord ++ tailWord_929948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929948).length < 2 ^ (prefixWord ++ tailWord_929948).sum := by decide
  have hdescent : baseEnd_929948 < baseStart_929948 := by decide
  rcases family_descends (prefixWord ++ tailWord_929948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929965 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_929965 : Nat := 118140960795 + 929965 * 2 ^ 59
def prefixEnd_929965 : Nat := 4983230072969 + 3 ^ 40 * 929965 * 2
def baseEnd_929965 : Nat := 424461366096497103431711

theorem tailTrace_929965 : CollatzResearch.WordTrace tailWord_929965 prefixEnd_929965 424461366096497103431711 := by
  unfold tailWord_929965
  simp only [CollatzResearch.WordTrace]
  refine ⟨33918610075903105222375349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22612406717268736814916899 33918610075903105222375349)
  ·
    refine ⟨3179869694615916114597689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33918610075903105222375349 3179869694615916114597689)
    ·
      refine ⟨2384902270961937085948267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179869694615916114597689 2384902270961937085948267)
      ·
        refine ⟨3577353406442905628922401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2384902270961937085948267 3577353406442905628922401)
        ·
          refine ⟨2683015054832179221691801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3577353406442905628922401 2683015054832179221691801)
          ·
            refine ⟨2012261291124134416268851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683015054832179221691801 2012261291124134416268851)
            ·
              refine ⟨3018391936686201624403277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012261291124134416268851 3018391936686201624403277)
              ·
                refine ⟨1131896976257325609151229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3018391936686201624403277 1131896976257325609151229)
                ·
                  refine ⟨424461366096497103431711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131896976257325609151229 424461366096497103431711)
                  ·
                    rfl

theorem cell20_929965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_929965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929965 prefixEnd_929965 := by exact prefixLift 929965
  have htrace : WordTrace (prefixWord ++ tailWord_929965) baseStart_929965 baseEnd_929965 := by
    simpa [prefixWord, tailWord_929965, baseEnd_929965] using wordTrace_append hprefix tailTrace_929965
  have hstable : (prefixWord ++ tailWord_929965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929965).length < 2 ^ (prefixWord ++ tailWord_929965).sum := by decide
  have hdescent : baseEnd_929965 < baseStart_929965 := by decide
  rcases family_descends (prefixWord ++ tailWord_929965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_929976 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 6]
def baseStart_929976 : Nat := 118140960795 + 929976 * 2 ^ 59
def prefixEnd_929976 : Nat := 4983230072969 + 3 ^ 40 * 929976 * 2
def baseEnd_929976 : Nat := 424466386796229954064999

theorem tailTrace_929976 : CollatzResearch.WordTrace tailWord_929976 prefixEnd_929976 424466386796229954064999 := by
  unfold tailWord_929976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16959505639431627050512891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22612674185908836067350521 16959505639431627050512891)
  ·
    refine ⟨25439258459147440575769337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16959505639431627050512891 25439258459147440575769337)
    ·
      refine ⟨19079443844360580431827003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25439258459147440575769337 19079443844360580431827003)
      ·
        refine ⟨28619165766540870647740505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19079443844360580431827003 28619165766540870647740505)
        ·
          refine ⟨21464374324905652985805379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28619165766540870647740505 21464374324905652985805379)
          ·
            refine ⟨32196561487358479478708069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21464374324905652985805379 32196561487358479478708069)
            ·
              refine ⟨6036855278879714902257763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32196561487358479478708069 6036855278879714902257763)
              ·
                refine ⟨9055282918319572353386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6036855278879714902257763 9055282918319572353386645)
                ·
                  refine ⟨424466386796229954064999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9055282918319572353386645 424466386796229954064999)
                  ·
                    rfl

theorem cell20_929976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_929976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_929976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_929976 prefixEnd_929976 := by exact prefixLift 929976
  have htrace : WordTrace (prefixWord ++ tailWord_929976) baseStart_929976 baseEnd_929976 := by
    simpa [prefixWord, tailWord_929976, baseEnd_929976] using wordTrace_append hprefix tailTrace_929976
  have hstable : (prefixWord ++ tailWord_929976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_929976).length < 2 ^ (prefixWord ++ tailWord_929976).sum := by decide
  have hdescent : baseEnd_929976 < baseStart_929976 := by decide
  rcases family_descends (prefixWord ++ tailWord_929976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930006 : List Nat := [5, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_930006 : Nat := 118140960795 + 930006 * 2 ^ 59
def prefixEnd_930006 : Nat := 4983230072969 + 3 ^ 40 * 930006 * 2
def baseEnd_930006 : Nat := 424480079613683183064877

theorem tailTrace_930006 : CollatzResearch.WordTrace tailWord_930006 prefixEnd_930006 424480079613683183064877 := by
  unfold tailWord_930006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120006591797160576538617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22613403645836379483078581 2120006591797160576538617)
  ·
    refine ⟨1590004943847870432403963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2120006591797160576538617 1590004943847870432403963)
    ·
      refine ⟨2385007415771805648605945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590004943847870432403963 2385007415771805648605945)
      ·
        refine ⟨1788755561828854236454459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2385007415771805648605945 1788755561828854236454459)
        ·
          refine ⟨2683133342743281354681689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1788755561828854236454459 2683133342743281354681689)
          ·
            refine ⟨2012350007057461016011267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683133342743281354681689 2012350007057461016011267)
            ·
              refine ⟨3018525010586191524016901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012350007057461016011267 3018525010586191524016901)
              ·
                refine ⟨565973439484910910753169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3018525010586191524016901 565973439484910910753169)
                ·
                  refine ⟨424480079613683183064877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565973439484910910753169 424480079613683183064877)
                  ·
                    rfl

theorem cell20_930006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_930006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930006 prefixEnd_930006 := by exact prefixLift 930006
  have htrace : WordTrace (prefixWord ++ tailWord_930006) baseStart_930006 baseEnd_930006 := by
    simpa [prefixWord, tailWord_930006, baseEnd_930006] using wordTrace_append hprefix tailTrace_930006
  have hstable : (prefixWord ++ tailWord_930006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930006).length < 2 ^ (prefixWord ++ tailWord_930006).sum := by decide
  have hdescent : baseEnd_930006 < baseStart_930006 := by decide
  rcases family_descends (prefixWord ++ tailWord_930006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930024 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 3]
def baseStart_930024 : Nat := 118140960795 + 930024 * 2 ^ 59
def prefixEnd_930024 : Nat := 4983230072969 + 3 ^ 40 * 930024 * 2
def baseEnd_930024 : Nat := 424488295304155120464803

theorem tailTrace_930024 : CollatzResearch.WordTrace tailWord_930024 prefixEnd_930024 424488295304155120464803 := by
  unfold tailWord_930024
  simp only [CollatzResearch.WordTrace]
  refine ⟨16960380991344679149386563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22613841321792905532515417 16960380991344679149386563)
  ·
    refine ⟨25440571487017018724079845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16960380991344679149386563 25440571487017018724079845)
    ·
      refine ⟨4770107153815691010764971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25440571487017018724079845 4770107153815691010764971)
      ·
        refine ⟨7155160730723536516147457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770107153815691010764971 7155160730723536516147457)
        ·
          refine ⟨5366370548042652387110593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7155160730723536516147457 5366370548042652387110593)
          ·
            refine ⟨4024777911031989290332945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5366370548042652387110593 4024777911031989290332945)
            ·
              refine ⟨3018583433273991967749709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4024777911031989290332945 3018583433273991967749709)
              ·
                refine ⟨1131968787477746987906141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3018583433273991967749709 1131968787477746987906141)
                ·
                  refine ⟨424488295304155120464803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1131968787477746987906141 424488295304155120464803)
                  ·
                    rfl

theorem cell20_930024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_930024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930024 prefixEnd_930024 := by exact prefixLift 930024
  have htrace : WordTrace (prefixWord ++ tailWord_930024) baseStart_930024 baseEnd_930024 := by
    simpa [prefixWord, tailWord_930024, baseEnd_930024] using wordTrace_append hprefix tailTrace_930024
  have hstable : (prefixWord ++ tailWord_930024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930024).length < 2 ^ (prefixWord ++ tailWord_930024).sum := by decide
  have hdescent : baseEnd_930024 < baseStart_930024 := by decide
  rcases family_descends (prefixWord ++ tailWord_930024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930031 : List Nat := [1, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_930031 : Nat := 118140960795 + 930031 * 2 ^ 59
def prefixEnd_930031 : Nat := 4983230072969 + 3 ^ 40 * 930031 * 2
def baseEnd_930031 : Nat := 424491490294894207231441

theorem tailTrace_930031 : CollatzResearch.WordTrace tailWord_930031 prefixEnd_930031 424491490294894207231441 := by
  unfold tailWord_930031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921017293663998494277947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614011529109332329518631 33921017293663998494277947)
  ·
    refine ⟨50881525940495997741416921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33921017293663998494277947 50881525940495997741416921)
    ·
      refine ⟨38161144455371998306062691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50881525940495997741416921 38161144455371998306062691)
      ·
        refine ⟨57241716683057997459094037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38161144455371998306062691 57241716683057997459094037)
        ·
          refine ⟨2683205469518343630895033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57241716683057997459094037 2683205469518343630895033)
          ·
            refine ⟨2012404102138757723171275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683205469518343630895033 2012404102138757723171275)
            ·
              refine ⟨3018606153208136584756913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2012404102138757723171275 3018606153208136584756913)
              ·
                refine ⟨2263954614906102438567685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3018606153208136584756913 2263954614906102438567685)
                ·
                  refine ⟨424491490294894207231441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2263954614906102438567685 424491490294894207231441)
                  ·
                    rfl

theorem cell20_930031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_930031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930031 prefixEnd_930031 := by exact prefixLift 930031
  have htrace : WordTrace (prefixWord ++ tailWord_930031) baseStart_930031 baseEnd_930031 := by
    simpa [prefixWord, tailWord_930031, baseEnd_930031] using wordTrace_append hprefix tailTrace_930031
  have hstable : (prefixWord ++ tailWord_930031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930031).length < 2 ^ (prefixWord ++ tailWord_930031).sum := by decide
  have hdescent : baseEnd_930031 < baseStart_930031 := by decide
  rcases family_descends (prefixWord ++ tailWord_930031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930038 : List Nat := [5, 1, 1, 1, 1, 1, 2, 8]
def baseStart_930038 : Nat := 118140960795 + 930038 * 2 ^ 59
def prefixEnd_930038 : Nat := 4983230072969 + 3 ^ 40 * 930038 * 2
def baseEnd_930038 : Nat := 141498228428544431332693

theorem tailTrace_930038 : CollatzResearch.WordTrace tailWord_930038 prefixEnd_930038 141498228428544431332693 := by
  unfold tailWord_930038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2120079537789914918111423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22614181736425759126521845 2120079537789914918111423)
  ·
    refine ⟨3180119306684872377167135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2120079537789914918111423 3180119306684872377167135)
    ·
      refine ⟨4770178960027308565750703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180119306684872377167135 4770178960027308565750703)
      ·
        refine ⟨7155268440040962848626055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4770178960027308565750703 7155268440040962848626055)
        ·
          refine ⟨10732902660061444272939083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7155268440040962848626055 10732902660061444272939083)
          ·
            refine ⟨16099353990092166409408625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10732902660061444272939083 16099353990092166409408625)
            ·
              refine ⟨12074515492569124807056469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16099353990092166409408625 12074515492569124807056469)
              ·
                refine ⟨141498228428544431332693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12074515492569124807056469 141498228428544431332693)
                ·
                  rfl

theorem cell20_930038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_930038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930038 prefixEnd_930038 := by exact prefixLift 930038
  have htrace : WordTrace (prefixWord ++ tailWord_930038) baseStart_930038 baseEnd_930038 := by
    simpa [prefixWord, tailWord_930038, baseEnd_930038] using wordTrace_append hprefix tailTrace_930038
  have hstable : (prefixWord ++ tailWord_930038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930038).length < 2 ^ (prefixWord ++ tailWord_930038).sum := by decide
  have hdescent : baseEnd_930038 < baseStart_930038 := by decide
  rcases family_descends (prefixWord ++ tailWord_930038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930055 : List Nat := [1, 1, 4, 5, 1, 1, 7]
def baseStart_930055 : Nat := 118140960795 + 930055 * 2 ^ 59
def prefixEnd_930055 : Nat := 4983230072969 + 3 ^ 40 * 930055 * 2
def baseEnd_930055 : Nat := 47166938283206310047927

theorem tailTrace_930055 : CollatzResearch.WordTrace tailWord_930055 prefixEnd_930055 47166938283206310047927 := by
  unfold tailWord_930055
  simp only [CollatzResearch.WordTrace]
  refine ⟨33921892645577050593151619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614595097051367062101079 33921892645577050593151619)
  ·
    refine ⟨50882838968365575889727429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33921892645577050593151619 50882838968365575889727429)
    ·
      refine ⟨9540532306568545479323893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50882838968365575889727429 9540532306568545479323893)
      ·
        refine ⟨894424903740801138686615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9540532306568545479323893 894424903740801138686615)
        ·
          refine ⟨1341637355611201708029923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894424903740801138686615 1341637355611201708029923)
          ·
            refine ⟨2012456033416802562044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1341637355611201708029923 2012456033416802562044885)
            ·
              refine ⟨47166938283206310047927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2012456033416802562044885 47166938283206310047927)
              ·
                rfl

theorem cell20_930055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 7].length) (baseStart_930055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930055 prefixEnd_930055 := by exact prefixLift 930055
  have htrace : WordTrace (prefixWord ++ tailWord_930055) baseStart_930055 baseEnd_930055 := by
    simpa [prefixWord, tailWord_930055, baseEnd_930055] using wordTrace_append hprefix tailTrace_930055
  have hstable : (prefixWord ++ tailWord_930055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930055).length < 2 ^ (prefixWord ++ tailWord_930055).sum := by decide
  have hdescent : baseEnd_930055 < baseStart_930055 := by decide
  rcases family_descends (prefixWord ++ tailWord_930055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930059 : List Nat := [1, 1, 1, 1, 5, 2, 9]
def baseStart_930059 : Nat := 118140960795 + 930059 * 2 ^ 59
def prefixEnd_930059 : Nat := 4983230072969 + 3 ^ 40 * 930059 * 2
def baseEnd_930059 : Nat := 47167141139761172699777

theorem tailTrace_930059 : CollatzResearch.WordTrace tailWord_930059 prefixEnd_930059 47167141139761172699777 := by
  unfold tailWord_930059
  simp only [CollatzResearch.WordTrace]
  refine ⟨33922038537562559276297231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22614692358375039517531487 33922038537562559276297231)
  ·
    refine ⟨50883057806343838914445847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33922038537562559276297231 50883057806343838914445847)
    ·
      refine ⟨76324586709515758371668771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50883057806343838914445847 76324586709515758371668771)
      ·
        refine ⟨114486880064273637557503157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76324586709515758371668771 114486880064273637557503157)
        ·
          refine ⟨10733145006025653521015921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114486880064273637557503157 10733145006025653521015921)
          ·
            refine ⟨8049858754519240140761941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10733145006025653521015921 8049858754519240140761941)
            ·
              refine ⟨47167141139761172699777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8049858754519240140761941 47167141139761172699777)
              ·
                rfl

theorem cell20_930059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_930059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930059 prefixEnd_930059 := by exact prefixLift 930059
  have htrace : WordTrace (prefixWord ++ tailWord_930059) baseStart_930059 baseEnd_930059 := by
    simpa [prefixWord, tailWord_930059, baseEnd_930059] using wordTrace_append hprefix tailTrace_930059
  have hstable : (prefixWord ++ tailWord_930059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930059).length < 2 ^ (prefixWord ++ tailWord_930059).sum := by decide
  have hdescent : baseEnd_930059 < baseStart_930059 := by decide
  rcases family_descends (prefixWord ++ tailWord_930059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930079 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 3]
def baseStart_930079 : Nat := 118140960795 + 930079 * 2 ^ 59
def prefixEnd_930079 : Nat := 4983230072969 + 3 ^ 40 * 930079 * 2
def baseEnd_930079 : Nat := 424513398802819373631245

theorem tailTrace_930079 : CollatzResearch.WordTrace tailWord_930079 prefixEnd_930079 424513398802819373631245 := by
  unfold tailWord_930079
  simp only [CollatzResearch.WordTrace]
  refine ⟨33922767997490102692025291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22615178664993401794683527 33922767997490102692025291)
  ·
    refine ⟨50884151996235154038037937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33922767997490102692025291 50884151996235154038037937)
    ·
      refine ⟨38163113997176365528528453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50884151996235154038037937 38163113997176365528528453)
      ·
        refine ⟨7155583874470568536599085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38163113997176365528528453 7155583874470568536599085)
        ·
          refine ⟨2683343952926463201224657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7155583874470568536599085 2683343952926463201224657)
          ·
            refine ⟨2012507964694847400918493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2683343952926463201224657 2012507964694847400918493)
            ·
              refine ⟨754690486760567775344435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2012507964694847400918493 754690486760567775344435)
              ·
                refine ⟨1132035730140851663016653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754690486760567775344435 1132035730140851663016653)
                ·
                  refine ⟨424513398802819373631245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132035730140851663016653 424513398802819373631245)
                  ·
                    rfl

theorem cell20_930079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_930079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930079 prefixEnd_930079 := by exact prefixLift 930079
  have htrace : WordTrace (prefixWord ++ tailWord_930079) baseStart_930079 baseEnd_930079 := by
    simpa [prefixWord, tailWord_930079, baseEnd_930079] using wordTrace_append hprefix tailTrace_930079
  have hstable : (prefixWord ++ tailWord_930079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930079).length < 2 ^ (prefixWord ++ tailWord_930079).sum := by decide
  have hdescent : baseEnd_930079 < baseStart_930079 := by decide
  rcases family_descends (prefixWord ++ tailWord_930079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930100 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_930100 : Nat := 118140960795 + 930100 * 2 ^ 59
def prefixEnd_930100 : Nat := 4983230072969 + 3 ^ 40 * 930100 * 2
def baseEnd_930100 : Nat := 424522983775036633931159

theorem tailTrace_930100 : CollatzResearch.WordTrace tailWord_930100 prefixEnd_930100 424522983775036633931159 := by
  unfold tailWord_930100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16961766965207011639269877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22615689286942682185693169 16961766965207011639269877)
  ·
    refine ⟨1590165652988157341181551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16961766965207011639269877 1590165652988157341181551)
    ·
      refine ⟨2385248479482236011772327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1590165652988157341181551 2385248479482236011772327)
      ·
        refine ⟨3577872719223354017658491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2385248479482236011772327 3577872719223354017658491)
        ·
          refine ⟨5366809078835031026487737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3577872719223354017658491 5366809078835031026487737)
          ·
            refine ⟨4025106809126273269865803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5366809078835031026487737 4025106809126273269865803)
            ·
              refine ⟨6037660213689409904798705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4025106809126273269865803 6037660213689409904798705)
              ·
                refine ⟨4528245160267057428599029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6037660213689409904798705 4528245160267057428599029)
                ·
                  refine ⟨424522983775036633931159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4528245160267057428599029 424522983775036633931159)
                  ·
                    rfl

theorem cell20_930100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_930100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930100 prefixEnd_930100 := by exact prefixLift 930100
  have htrace : WordTrace (prefixWord ++ tailWord_930100) baseStart_930100 baseEnd_930100 := by
    simpa [prefixWord, tailWord_930100, baseEnd_930100] using wordTrace_append hprefix tailTrace_930100
  have hstable : (prefixWord ++ tailWord_930100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930100).length < 2 ^ (prefixWord ++ tailWord_930100).sum := by decide
  have hdescent : baseEnd_930100 < baseStart_930100 := by decide
  rcases family_descends (prefixWord ++ tailWord_930100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930121 : List Nat := [1, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_930121 : Nat := 118140960795 + 930121 * 2 ^ 59
def prefixEnd_930121 : Nat := 4983230072969 + 3 ^ 40 * 930121 * 2
def baseEnd_930121 : Nat := 424532568747253894231073

theorem tailTrace_930121 : CollatzResearch.WordTrace tailWord_930121 prefixEnd_930121 424532568747253894231073 := by
  unfold tailWord_930121
  simp only [CollatzResearch.WordTrace]
  refine ⟨33924299863337943865054217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22616199908891962576702811 33924299863337943865054217)
  ·
    refine ⟨25443224897503457898790663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33924299863337943865054217 25443224897503457898790663)
    ·
      refine ⟨38164837346255186848185995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25443224897503457898790663 38164837346255186848185995)
      ·
        refine ⟨57247256019382780272278993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38164837346255186848185995 57247256019382780272278993)
        ·
          refine ⟨42935442014537085204209245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57247256019382780272278993 42935442014537085204209245)
          ·
            refine ⟨16100790755451406951578467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42935442014537085204209245 16100790755451406951578467)
            ·
              refine ⟨24151186133177110427367701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16100790755451406951578467 24151186133177110427367701)
              ·
                refine ⟨1132086849992677051282861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24151186133177110427367701 1132086849992677051282861)
                ·
                  refine ⟨424532568747253894231073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132086849992677051282861 424532568747253894231073)
                  ·
                    rfl

theorem cell20_930121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_930121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930121 prefixEnd_930121 := by exact prefixLift 930121
  have htrace : WordTrace (prefixWord ++ tailWord_930121) baseStart_930121 baseEnd_930121 := by
    simpa [prefixWord, tailWord_930121, baseEnd_930121] using wordTrace_append hprefix tailTrace_930121
  have hstable : (prefixWord ++ tailWord_930121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930121).length < 2 ^ (prefixWord ++ tailWord_930121).sum := by decide
  have hdescent : baseEnd_930121 < baseStart_930121 := by decide
  rcases family_descends (prefixWord ++ tailWord_930121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930152 : List Nat := [2, 1, 4, 2, 2, 1, 2, 6]
def baseStart_930152 : Nat := 118140960795 + 930152 * 2 ^ 59
def prefixEnd_930152 : Nat := 4983230072969 + 3 ^ 40 * 930152 * 2
def baseEnd_930152 : Nat := 141515572663985188065871

theorem tailTrace_930152 : CollatzResearch.WordTrace tailWord_930152 prefixEnd_930152 141515572663985188065871 := by
  unfold tailWord_930152
  simp only [CollatzResearch.WordTrace]
  refine ⟨16962715263112818079716355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22616953684150424106288473 16962715263112818079716355)
  ·
    refine ⟨25444072894669227119574533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16962715263112818079716355 25444072894669227119574533)
    ·
      refine ⟨4770763667750480084920225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25444072894669227119574533 4770763667750480084920225)
      ·
        refine ⟨3578072750812860063690169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4770763667750480084920225 3578072750812860063690169)
        ·
          refine ⟨2683554563109645047767627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3578072750812860063690169 2683554563109645047767627)
          ·
            refine ⟨4025331844664467571651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2683554563109645047767627 4025331844664467571651441)
            ·
              refine ⟨3018998883498350678738581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4025331844664467571651441 3018998883498350678738581)
              ·
                refine ⟨141515572663985188065871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3018998883498350678738581 141515572663985188065871)
                ·
                  rfl

theorem cell20_930152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_930152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930152 prefixEnd_930152 := by exact prefixLift 930152
  have htrace : WordTrace (prefixWord ++ tailWord_930152) baseStart_930152 baseEnd_930152 := by
    simpa [prefixWord, tailWord_930152, baseEnd_930152] using wordTrace_append hprefix tailTrace_930152
  have hstable : (prefixWord ++ tailWord_930152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930152).length < 2 ^ (prefixWord ++ tailWord_930152).sum := by decide
  have hdescent : baseEnd_930152 < baseStart_930152 := by decide
  rcases family_descends (prefixWord ++ tailWord_930152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930173 : List Nat := [1, 4, 1, 1, 2, 11]
def baseStart_930173 : Nat := 118140960795 + 930173 * 2 ^ 59
def prefixEnd_930173 : Nat := 4983230072969 + 3 ^ 40 * 930173 * 2
def baseEnd_930173 : Nat := 15724307517191586092501

theorem tailTrace_930173 : CollatzResearch.WordTrace tailWord_930173 prefixEnd_930173 15724307517191586092501 := by
  unfold tailWord_930173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33926196459149556745947173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22617464306099704497298115 33926196459149556745947173)
  ·
    refine ⟨6361161836090541889865095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33926196459149556745947173 6361161836090541889865095)
    ·
      refine ⟨9541742754135812834797643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6361161836090541889865095 9541742754135812834797643)
      ·
        refine ⟨14312614131203719252196465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9541742754135812834797643 14312614131203719252196465)
        ·
          refine ⟨10734460598402789439147349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14312614131203719252196465 10734460598402789439147349)
          ·
            refine ⟨15724307517191586092501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10734460598402789439147349 15724307517191586092501)
            ·
              rfl

theorem cell20_930173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 11].length) (baseStart_930173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930173 prefixEnd_930173 := by exact prefixLift 930173
  have htrace : WordTrace (prefixWord ++ tailWord_930173) baseStart_930173 baseEnd_930173 := by
    simpa [prefixWord, tailWord_930173, baseEnd_930173] using wordTrace_append hprefix tailTrace_930173
  have hstable : (prefixWord ++ tailWord_930173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930173).length < 2 ^ (prefixWord ++ tailWord_930173).sum := by decide
  have hdescent : baseEnd_930173 < baseStart_930173 := by decide
  rcases family_descends (prefixWord ++ tailWord_930173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930186 : List Nat := [3, 1, 2, 5, 1, 2, 1, 5]
def baseStart_930186 : Nat := 118140960795 + 930186 * 2 ^ 59
def prefixEnd_930186 : Nat := 4983230072969 + 3 ^ 40 * 930186 * 2
def baseEnd_930186 : Nat := 141520745506134185688047

theorem tailTrace_930186 : CollatzResearch.WordTrace tailWord_930186 prefixEnd_930186 141520745506134185688047 := by
  unfold tailWord_930186
  simp only [CollatzResearch.WordTrace]
  refine ⟨8481667652025614991542603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22617780405401639977446941 8481667652025614991542603)
  ·
    refine ⟨12722501478038422487313905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8481667652025614991542603 12722501478038422487313905)
    ·
      refine ⟨9541876108528816865485429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12722501478038422487313905 9541876108528816865485429)
      ·
        refine ⟨894550885174576581139259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9541876108528816865485429 894550885174576581139259)
        ·
          refine ⟨1341826327761864871708889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894550885174576581139259 1341826327761864871708889)
          ·
            refine ⟨1006369745821398653781667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341826327761864871708889 1006369745821398653781667)
            ·
              refine ⟨1509554618732097980672501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006369745821398653781667 1509554618732097980672501)
              ·
                refine ⟨141520745506134185688047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1509554618732097980672501 141520745506134185688047)
                ·
                  rfl

theorem cell20_930186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_930186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930186 prefixEnd_930186 := by exact prefixLift 930186
  have htrace : WordTrace (prefixWord ++ tailWord_930186) baseStart_930186 baseEnd_930186 := by
    simpa [prefixWord, tailWord_930186, baseEnd_930186] using wordTrace_append hprefix tailTrace_930186
  have hstable : (prefixWord ++ tailWord_930186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930186).length < 2 ^ (prefixWord ++ tailWord_930186).sum := by decide
  have hdescent : baseEnd_930186 < baseStart_930186 := by decide
  rcases family_descends (prefixWord ++ tailWord_930186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930238 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_930238 : Nat := 118140960795 + 930238 * 2 ^ 59
def prefixEnd_930238 : Nat := 4983230072969 + 3 ^ 40 * 930238 * 2
def baseEnd_930238 : Nat := 424585970735321487330595

theorem tailTrace_930238 : CollatzResearch.WordTrace tailWord_930238 prefixEnd_930238 424585970735321487330595 := by
  unfold tailWord_930238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4241070900489259105882921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22619044802609381898042245 4241070900489259105882921)
  ·
    refine ⟨3180803175366944329412191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4241070900489259105882921 3180803175366944329412191)
    ·
      refine ⟨4771204763050416494118287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3180803175366944329412191 4771204763050416494118287)
      ·
        refine ⟨7156807144575624741177431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4771204763050416494118287 7156807144575624741177431)
        ·
          refine ⟨10735210716863437111766147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7156807144575624741177431 10735210716863437111766147)
          ·
            refine ⟨16102816075295155667649221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10735210716863437111766147 16102816075295155667649221)
            ·
              refine ⟨3019278014117841687684229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16102816075295155667649221 3019278014117841687684229)
              ·
                refine ⟨566114627647095316440793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3019278014117841687684229 566114627647095316440793)
                ·
                  refine ⟨424585970735321487330595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566114627647095316440793 424585970735321487330595)
                  ·
                    rfl

theorem cell20_930238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_930238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930238 prefixEnd_930238 := by exact prefixLift 930238
  have htrace : WordTrace (prefixWord ++ tailWord_930238) baseStart_930238 baseEnd_930238 := by
    simpa [prefixWord, tailWord_930238, baseEnd_930238] using wordTrace_append hprefix tailTrace_930238
  have hstable : (prefixWord ++ tailWord_930238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930238).length < 2 ^ (prefixWord ++ tailWord_930238).sum := by decide
  have hdescent : baseEnd_930238 < baseStart_930238 := by decide
  rcases family_descends (prefixWord ++ tailWord_930238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930256 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_930256 : Nat := 118140960795 + 930256 * 2 ^ 59
def prefixEnd_930256 : Nat := 4983230072969 + 3 ^ 40 * 930256 * 2
def baseEnd_930256 : Nat := 424594186425793424730521

theorem tailTrace_930256 : CollatzResearch.WordTrace tailWord_930256 prefixEnd_930256 424594186425793424730521 := by
  unfold tailWord_930256
  simp only [CollatzResearch.WordTrace]
  refine ⟨16964611858924430960609311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22619482478565907947479081 16964611858924430960609311)
  ·
    refine ⟨25446917788386646440913967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16964611858924430960609311 25446917788386646440913967)
    ·
      refine ⟨38170376682579969661370951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25446917788386646440913967 38170376682579969661370951)
      ·
        refine ⟨57255565023869954492056427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38170376682579969661370951 57255565023869954492056427)
        ·
          refine ⟨85883347535804931738084641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57255565023869954492056427 85883347535804931738084641)
          ·
            refine ⟨64412510651853698803563481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85883347535804931738084641 64412510651853698803563481)
            ·
              refine ⟨48309382988890274102672611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64412510651853698803563481 48309382988890274102672611)
              ·
                refine ⟨72464074483335411154008917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48309382988890274102672611 72464074483335411154008917)
                ·
                  refine ⟨424594186425793424730521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72464074483335411154008917 424594186425793424730521)
                  ·
                    rfl

theorem cell20_930256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_930256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930256 prefixEnd_930256 := by exact prefixLift 930256
  have htrace : WordTrace (prefixWord ++ tailWord_930256) baseStart_930256 baseEnd_930256 := by
    simpa [prefixWord, tailWord_930256, baseEnd_930256] using wordTrace_append hprefix tailTrace_930256
  have hstable : (prefixWord ++ tailWord_930256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930256).length < 2 ^ (prefixWord ++ tailWord_930256).sum := by decide
  have hdescent : baseEnd_930256 < baseStart_930256 := by decide
  rcases family_descends (prefixWord ++ tailWord_930256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930293 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_930293 : Nat := 118140960795 + 930293 * 2 ^ 59
def prefixEnd_930293 : Nat := 4983230072969 + 3 ^ 40 * 930293 * 2
def baseEnd_930293 : Nat := 424611074233985740497037

theorem tailTrace_930293 : CollatzResearch.WordTrace tailWord_930293 prefixEnd_930293 424611074233985740497037 := by
  unfold tailWord_930293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33930573218714817240315533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22620382145809878160210355 33930573218714817240315533)
  ·
    refine ⟨12723964957018056465118325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33930573218714817240315533 12723964957018056465118325)
    ·
      refine ⟨1192871714720442793604843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12723964957018056465118325 1192871714720442793604843)
      ·
        refine ⟨1789307572080664190407265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1192871714720442793604843 1789307572080664190407265)
        ·
          refine ⟨1341980679060498142805449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789307572080664190407265 1341980679060498142805449)
          ·
            refine ⟨1006485509295373607104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341980679060498142805449 1006485509295373607104087)
            ·
              refine ⟨1509728263943060410656131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006485509295373607104087 1509728263943060410656131)
              ·
                refine ⟨2264592395914590615984197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1509728263943060410656131 2264592395914590615984197)
                ·
                  refine ⟨424611074233985740497037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264592395914590615984197 424611074233985740497037)
                  ·
                    rfl

theorem cell20_930293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_930293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930293 prefixEnd_930293 := by exact prefixLift 930293
  have htrace : WordTrace (prefixWord ++ tailWord_930293) baseStart_930293 baseEnd_930293 := by
    simpa [prefixWord, tailWord_930293, baseEnd_930293] using wordTrace_append hprefix tailTrace_930293
  have hstable : (prefixWord ++ tailWord_930293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930293).length < 2 ^ (prefixWord ++ tailWord_930293).sum := by decide
  have hdescent : baseEnd_930293 < baseStart_930293 := by decide
  rcases family_descends (prefixWord ++ tailWord_930293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930297 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 2]
def baseStart_930297 : Nat := 118140960795 + 930297 * 2 ^ 59
def prefixEnd_930297 : Nat := 4983230072969 + 3 ^ 40 * 930297 * 2
def baseEnd_930297 : Nat := 424612899942979504363687

theorem tailTrace_930297 : CollatzResearch.WordTrace tailWord_930297 prefixEnd_930297 424612899942979504363687 := by
  unfold tailWord_930297
  simp only [CollatzResearch.WordTrace]
  refine ⟨33930719110700325923461145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22620479407133550615640763 33930719110700325923461145)
  ·
    refine ⟨25448039333025244442595859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33930719110700325923461145 25448039333025244442595859)
    ·
      refine ⟨38172058999537866663893789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25448039333025244442595859 38172058999537866663893789)
      ·
        refine ⟨14314522124826699998960171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38172058999537866663893789 14314522124826699998960171)
        ·
          refine ⟨21471783187240049998440257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14314522124826699998960171 21471783187240049998440257)
          ·
            refine ⟨16103837390430037498830193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21471783187240049998440257 16103837390430037498830193)
            ·
              refine ⟨12077878042822528124122645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16103837390430037498830193 12077878042822528124122645)
              ·
                refine ⟨566150533257306005818249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12077878042822528124122645 566150533257306005818249)
                ·
                  refine ⟨424612899942979504363687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566150533257306005818249 424612899942979504363687)
                  ·
                    rfl

theorem cell20_930297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_930297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930297 prefixEnd_930297 := by exact prefixLift 930297
  have htrace : WordTrace (prefixWord ++ tailWord_930297) baseStart_930297 baseEnd_930297 := by
    simpa [prefixWord, tailWord_930297, baseEnd_930297] using wordTrace_append hprefix tailTrace_930297
  have hstable : (prefixWord ++ tailWord_930297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930297).length < 2 ^ (prefixWord ++ tailWord_930297).sum := by decide
  have hdescent : baseEnd_930297 < baseStart_930297 := by decide
  rcases family_descends (prefixWord ++ tailWord_930297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930325 : List Nat := [1, 3, 2, 1, 3, 1, 1, 8]
def baseStart_930325 : Nat := 118140960795 + 930325 * 2 ^ 59
def prefixEnd_930325 : Nat := 4983230072969 + 3 ^ 40 * 930325 * 2
def baseEnd_930325 : Nat := 141541893301978617143413

theorem tailTrace_930325 : CollatzResearch.WordTrace tailWord_930325 prefixEnd_930325 141541893301978617143413 := by
  unfold tailWord_930325
  simp only [CollatzResearch.WordTrace]
  refine ⟨33931740354598886705480429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22621160236399257803653619 33931740354598886705480429)
  ·
    refine ⟨12724402632974582514555161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33931740354598886705480429 12724402632974582514555161)
    ·
      refine ⟨9543301974730936885916371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12724402632974582514555161 9543301974730936885916371)
      ·
        refine ⟨14314952962096405328874557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9543301974730936885916371 14314952962096405328874557)
        ·
          refine ⟨5368107360786151998327959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14314952962096405328874557 5368107360786151998327959)
          ·
            refine ⟨8052161041179227997491939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5368107360786151998327959 8052161041179227997491939)
            ·
              refine ⟨12078241561768841996237909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8052161041179227997491939 12078241561768841996237909)
              ·
                refine ⟨141541893301978617143413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12078241561768841996237909 141541893301978617143413)
                ·
                  rfl

theorem cell20_930325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_930325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930325 prefixEnd_930325 := by exact prefixLift 930325
  have htrace : WordTrace (prefixWord ++ tailWord_930325) baseStart_930325 baseEnd_930325 := by
    simpa [prefixWord, tailWord_930325, baseEnd_930325] using wordTrace_append hprefix tailTrace_930325
  have hstable : (prefixWord ++ tailWord_930325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930325).length < 2 ^ (prefixWord ++ tailWord_930325).sum := by decide
  have hdescent : baseEnd_930325 < baseStart_930325 := by decide
  rcases family_descends (prefixWord ++ tailWord_930325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930335 : List Nat := [1, 1, 2, 4, 1, 1, 1, 7, 2]
def baseStart_930335 : Nat := 118140960795 + 930335 * 2 ^ 59
def prefixEnd_930335 : Nat := 4983230072969 + 3 ^ 40 * 930335 * 2
def baseEnd_930335 : Nat := 424630244178420261096865

theorem tailTrace_930335 : CollatzResearch.WordTrace tailWord_930335 prefixEnd_930335 424630244178420261096865 := by
  unfold tailWord_930335
  simp only [CollatzResearch.WordTrace]
  refine ⟨33932105084562658413344459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22621403389708438942229639 33932105084562658413344459)
  ·
    refine ⟨50898157626843987620016689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33932105084562658413344459 50898157626843987620016689)
    ·
      refine ⟨38173618220132990715012517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50898157626843987620016689 38173618220132990715012517)
      ·
        refine ⟨7157553416274935759064847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38173618220132990715012517 7157553416274935759064847)
        ·
          refine ⟨10736330124412403638597271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157553416274935759064847 10736330124412403638597271)
          ·
            refine ⟨16104495186618605457895907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10736330124412403638597271 16104495186618605457895907)
            ·
              refine ⟨24156742779927908186843861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16104495186618605457895907 24156742779927908186843861)
              ·
                refine ⟨566173658904560348129153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24156742779927908186843861 566173658904560348129153)
                ·
                  refine ⟨424630244178420261096865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566173658904560348129153 424630244178420261096865)
                  ·
                    rfl

theorem cell20_930335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 2].length) (baseStart_930335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930335 prefixEnd_930335 := by exact prefixLift 930335
  have htrace : WordTrace (prefixWord ++ tailWord_930335) baseStart_930335 baseEnd_930335 := by
    simpa [prefixWord, tailWord_930335, baseEnd_930335] using wordTrace_append hprefix tailTrace_930335
  have hstable : (prefixWord ++ tailWord_930335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930335).length < 2 ^ (prefixWord ++ tailWord_930335).sum := by decide
  have hdescent : baseEnd_930335 < baseStart_930335 := by decide
  rcases family_descends (prefixWord ++ tailWord_930335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930352 : List Nat := [2, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_930352 : Nat := 118140960795 + 930352 * 2 ^ 59
def prefixEnd_930352 : Nat := 4983230072969 + 3 ^ 40 * 930352 * 2
def baseEnd_930352 : Nat := 424638003441643757530129

theorem tailTrace_930352 : CollatzResearch.WordTrace tailWord_930352 prefixEnd_930352 424638003441643757530129 := by
  unfold tailWord_930352
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966362562750535158356655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22621816750334046877808873 16966362562750535158356655)
  ·
    refine ⟨25449543844125802737534983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16966362562750535158356655 25449543844125802737534983)
    ·
      refine ⟨38174315766188704106302475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25449543844125802737534983 38174315766188704106302475)
      ·
        refine ⟨57261473649283056159453713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38174315766188704106302475 57261473649283056159453713)
        ·
          refine ⟨42946105236962292119590285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57261473649283056159453713 42946105236962292119590285)
          ·
            refine ⟨16104789463860859544846357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42946105236962292119590285 16104789463860859544846357)
            ·
              refine ⟨754912006118477791164673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16104789463860859544846357 754912006118477791164673)
              ·
                refine ⟨566184004588858343373505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754912006118477791164673 566184004588858343373505)
                ·
                  refine ⟨424638003441643757530129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566184004588858343373505 424638003441643757530129)
                  ·
                    rfl

theorem cell20_930352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_930352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930352 prefixEnd_930352 := by exact prefixLift 930352
  have htrace : WordTrace (prefixWord ++ tailWord_930352) baseStart_930352 baseEnd_930352 := by
    simpa [prefixWord, tailWord_930352, baseEnd_930352] using wordTrace_append hprefix tailTrace_930352
  have hstable : (prefixWord ++ tailWord_930352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930352).length < 2 ^ (prefixWord ++ tailWord_930352).sum := by decide
  have hdescent : baseEnd_930352 < baseStart_930352 := by decide
  rcases family_descends (prefixWord ++ tailWord_930352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930380 : List Nat := [2, 2, 1, 3, 1, 2, 5, 4]
def baseStart_930380 : Nat := 118140960795 + 930380 * 2 ^ 59
def prefixEnd_930380 : Nat := 4983230072969 + 3 ^ 40 * 930380 * 2
def baseEnd_930380 : Nat := 141550261134866701532227

theorem tailTrace_930380 : CollatzResearch.WordTrace tailWord_930380 prefixEnd_930380 141550261134866701532227 := by
  unfold tailWord_930380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16966873184699815549366297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22622497579599754065821729 16966873184699815549366297)
  ·
    refine ⟨12725154888524861662024723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16966873184699815549366297 12725154888524861662024723)
    ·
      refine ⟨19087732332787292493037085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12725154888524861662024723 19087732332787292493037085)
      ·
        refine ⟨7157899624795234684888907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19087732332787292493037085 7157899624795234684888907)
        ·
          refine ⟨10736849437192852027333361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7157899624795234684888907 10736849437192852027333361)
          ·
            refine ⟨8052637077894639020500021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10736849437192852027333361 8052637077894639020500021)
            ·
              refine ⟨754934726052622408171877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8052637077894639020500021 754934726052622408171877)
              ·
                refine ⟨141550261134866701532227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754934726052622408171877 141550261134866701532227)
                ·
                  rfl

theorem cell20_930380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_930380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930380 prefixEnd_930380 := by exact prefixLift 930380
  have htrace : WordTrace (prefixWord ++ tailWord_930380) baseStart_930380 baseEnd_930380 := by
    simpa [prefixWord, tailWord_930380, baseEnd_930380] using wordTrace_append hprefix tailTrace_930380
  have hstable : (prefixWord ++ tailWord_930380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930380).length < 2 ^ (prefixWord ++ tailWord_930380).sum := by decide
  have hdescent : baseEnd_930380 < baseStart_930380 := by decide
  rcases family_descends (prefixWord ++ tailWord_930380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930401 : List Nat := [1, 2, 3, 1, 1, 5, 7]
def baseStart_930401 : Nat := 118140960795 + 930401 * 2 ^ 59
def prefixEnd_930401 : Nat := 4983230072969 + 3 ^ 40 * 930401 * 2
def baseEnd_930401 : Nat := 47184485375201929432955

theorem tailTrace_930401 : CollatzResearch.WordTrace tailWord_930401 prefixEnd_930401 47184485375201929432955 := by
  unfold tailWord_930401
  simp only [CollatzResearch.WordTrace]
  refine ⟨33934512302323551685247057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22623008201549034456831371 33934512302323551685247057)
  ·
    refine ⟨25450884226742663763935293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33934512302323551685247057 25450884226742663763935293)
    ·
      refine ⟨9544081585028498911475735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25450884226742663763935293 9544081585028498911475735)
      ·
        refine ⟨14316122377542748367213603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9544081585028498911475735 14316122377542748367213603)
        ·
          refine ⟨21474183566314122550820405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14316122377542748367213603 21474183566314122550820405)
          ·
            refine ⟨2013204709341948989139413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21474183566314122550820405 2013204709341948989139413)
            ·
              refine ⟨47184485375201929432955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2013204709341948989139413 47184485375201929432955)
              ·
                rfl

theorem cell20_930401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_930401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930401 prefixEnd_930401 := by exact prefixLift 930401
  have htrace : WordTrace (prefixWord ++ tailWord_930401) baseStart_930401 baseEnd_930401 := by
    simpa [prefixWord, tailWord_930401, baseEnd_930401] using wordTrace_append hprefix tailTrace_930401
  have hstable : (prefixWord ++ tailWord_930401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930401).length < 2 ^ (prefixWord ++ tailWord_930401).sum := by decide
  have hdescent : baseEnd_930401 < baseStart_930401 := by decide
  rcases family_descends (prefixWord ++ tailWord_930401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930432 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_930432 : Nat := 118140960795 + 930432 * 2 ^ 59
def prefixEnd_930432 : Nat := 4983230072969 + 3 ^ 40 * 930432 * 2
def baseEnd_930432 : Nat := 424674517621519034863135

theorem tailTrace_930432 : CollatzResearch.WordTrace tailWord_930432 prefixEnd_930432 424674517621519034863135 := by
  unfold tailWord_930432
  simp only [CollatzResearch.WordTrace]
  refine ⟨16967821482605621989812775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22623761976807495986417033 16967821482605621989812775)
  ·
    refine ⟨25451732223908432984719163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16967821482605621989812775 25451732223908432984719163)
    ·
      refine ⟨38177598335862649477078745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25451732223908432984719163 38177598335862649477078745)
      ·
        refine ⟨28633198751896987107809059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38177598335862649477078745 28633198751896987107809059)
        ·
          refine ⟨42949798127845480661713589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28633198751896987107809059 42949798127845480661713589)
          ·
            refine ⟨4026543574485513812035649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42949798127845480661713589 4026543574485513812035649)
            ·
              refine ⟨3019907680864135359026737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4026543574485513812035649 3019907680864135359026737)
              ·
                refine ⟨2264930760648101519270053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3019907680864135359026737 2264930760648101519270053)
                ·
                  refine ⟨424674517621519034863135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2264930760648101519270053 424674517621519034863135)
                  ·
                    rfl

theorem cell20_930432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_930432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930432 prefixEnd_930432 := by exact prefixLift 930432
  have htrace : WordTrace (prefixWord ++ tailWord_930432) baseStart_930432 baseEnd_930432 := by
    simpa [prefixWord, tailWord_930432, baseEnd_930432] using wordTrace_append hprefix tailTrace_930432
  have hstable : (prefixWord ++ tailWord_930432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930432).length < 2 ^ (prefixWord ++ tailWord_930432).sum := by decide
  have hdescent : baseEnd_930432 < baseStart_930432 := by decide
  rcases family_descends (prefixWord ++ tailWord_930432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930439 : List Nat := [1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_930439 : Nat := 118140960795 + 930439 * 2 ^ 59
def prefixEnd_930439 : Nat := 4983230072969 + 3 ^ 40 * 930439 * 2
def baseEnd_930439 : Nat := 141559237537419373876591

theorem tailTrace_930439 : CollatzResearch.WordTrace tailWord_930439 prefixEnd_930439 141559237537419373876591 := by
  unfold tailWord_930439
  simp only [CollatzResearch.WordTrace]
  refine ⟨33935898276185884175130371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22623932184123922783420247 33935898276185884175130371)
  ·
    refine ⟨50903847414278826262695557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33935898276185884175130371 50903847414278826262695557)
    ·
      refine ⟨9544471390177279924255417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50903847414278826262695557 9544471390177279924255417)
      ·
        refine ⟨7158353542632959943191563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9544471390177279924255417 7158353542632959943191563)
        ·
          refine ⟨10737530313949439914787345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7158353542632959943191563 10737530313949439914787345)
          ·
            refine ⟨8053147735462079936090509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10737530313949439914787345 8053147735462079936090509)
            ·
              refine ⟨3019930400798279976033941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8053147735462079936090509 3019930400798279976033941)
              ·
                refine ⟨141559237537419373876591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3019930400798279976033941 141559237537419373876591)
                ·
                  rfl

theorem cell20_930439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_930439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930439 prefixEnd_930439 := by exact prefixLift 930439
  have htrace : WordTrace (prefixWord ++ tailWord_930439) baseStart_930439 baseEnd_930439 := by
    simpa [prefixWord, tailWord_930439, baseEnd_930439] using wordTrace_append hprefix tailTrace_930439
  have hstable : (prefixWord ++ tailWord_930439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930439).length < 2 ^ (prefixWord ++ tailWord_930439).sum := by decide
  have hdescent : baseEnd_930439 < baseStart_930439 := by decide
  rcases family_descends (prefixWord ++ tailWord_930439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930517 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 2]
def baseStart_930517 : Nat := 118140960795 + 930517 * 2 ^ 59
def prefixEnd_930517 : Nat := 4983230072969 + 3 ^ 40 * 930517 * 2
def baseEnd_930517 : Nat := 424713313937636517029455

theorem tailTrace_930517 : CollatzResearch.WordTrace tailWord_930517 prefixEnd_930517 424713313937636517029455 := by
  unfold tailWord_930517
  simp only [CollatzResearch.WordTrace]
  refine ⟨33938743169903303496469805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22625828779935535664313203 33938743169903303496469805)
  ·
    refine ⟨12727028688713738811176177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33938743169903303496469805 12727028688713738811176177)
    ·
      refine ⟨9545271516535304108382133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12727028688713738811176177 9545271516535304108382133)
      ·
        refine ⟨894869204675184760160825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9545271516535304108382133 894869204675184760160825)
        ·
          refine ⟨671151903506388570120619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894869204675184760160825 671151903506388570120619)
          ·
            refine ⟨1006727855259582855180929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671151903506388570120619 1006727855259582855180929)
            ·
              refine ⟨755045891444687141385697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006727855259582855180929 755045891444687141385697)
              ·
                refine ⟨566284418583515356039273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 755045891444687141385697 566284418583515356039273)
                ·
                  refine ⟨424713313937636517029455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566284418583515356039273 424713313937636517029455)
                  ·
                    rfl

theorem cell20_930517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_930517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930517 prefixEnd_930517 := by exact prefixLift 930517
  have htrace : WordTrace (prefixWord ++ tailWord_930517) baseStart_930517 baseEnd_930517 := by
    simpa [prefixWord, tailWord_930517, baseEnd_930517] using wordTrace_append hprefix tailTrace_930517
  have hstable : (prefixWord ++ tailWord_930517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930517).length < 2 ^ (prefixWord ++ tailWord_930517).sum := by decide
  have hdescent : baseEnd_930517 < baseStart_930517 := by decide
  rcases family_descends (prefixWord ++ tailWord_930517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930532 : List Nat := [2, 3, 1, 1, 1, 6, 1, 5]
def baseStart_930532 : Nat := 118140960795 + 930532 * 2 ^ 59
def prefixEnd_930532 : Nat := 4983230072969 + 3 ^ 40 * 930532 * 2
def baseEnd_930532 : Nat := 141573386782121043843131

theorem tailTrace_930532 : CollatzResearch.WordTrace tailWord_930532 prefixEnd_930532 141573386782121043843131 := by
  unfold tailWord_930532
  simp only [CollatzResearch.WordTrace]
  refine ⟨16969645132424480529132925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22626193509899307372177233 16969645132424480529132925)
  ·
    refine ⟨6363616924659180198424847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16969645132424480529132925 6363616924659180198424847)
    ·
      refine ⟨9545425386988770297637271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363616924659180198424847 9545425386988770297637271)
      ·
        refine ⟨14318138080483155446455907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9545425386988770297637271 14318138080483155446455907)
        ·
          refine ⟨21477207120724733169683861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14318138080483155446455907 21477207120724733169683861)
          ·
            refine ⟨1006744083783971867328931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21477207120724733169683861 1006744083783971867328931)
            ·
              refine ⟨1510116125675957800993397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006744083783971867328931 1510116125675957800993397)
              ·
                refine ⟨141573386782121043843131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1510116125675957800993397 141573386782121043843131)
                ·
                  rfl

theorem cell20_930532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_930532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930532 prefixEnd_930532 := by exact prefixLift 930532
  have htrace : WordTrace (prefixWord ++ tailWord_930532) baseStart_930532 baseEnd_930532 := by
    simpa [prefixWord, tailWord_930532, baseEnd_930532] using wordTrace_append hprefix tailTrace_930532
  have hstable : (prefixWord ++ tailWord_930532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930532).length < 2 ^ (prefixWord ++ tailWord_930532).sum := by decide
  have hdescent : baseEnd_930532 < baseStart_930532 := by decide
  rcases family_descends (prefixWord ++ tailWord_930532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930546 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 6]
def baseStart_930546 : Nat := 118140960795 + 930546 * 2 ^ 59
def prefixEnd_930546 : Nat := 4983230072969 + 3 ^ 40 * 930546 * 2
def baseEnd_930546 : Nat := 424726550327841305062669

theorem tailTrace_930546 : CollatzResearch.WordTrace tailWord_930546 prefixEnd_930546 424726550327841305062669 := by
  unfold tailWord_930546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8484950221699560362318873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22626533924532160966183661 8484950221699560362318873)
  ·
    refine ⟨6363712666274670271739155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8484950221699560362318873 6363712666274670271739155)
    ·
      refine ⟨9545568999412005407608733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6363712666274670271739155 9545568999412005407608733)
      ·
        refine ⟨3579588374779502027853275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9545568999412005407608733 3579588374779502027853275)
        ·
          refine ⟨5369382562169253041779913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3579588374779502027853275 5369382562169253041779913)
          ·
            refine ⟨4027036921626939781334935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5369382562169253041779913 4027036921626939781334935)
            ·
              refine ⟨6040555382440409672002403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4027036921626939781334935 6040555382440409672002403)
              ·
                refine ⟨9060833073660614508003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6040555382440409672002403 9060833073660614508003605)
                ·
                  refine ⟨424726550327841305062669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9060833073660614508003605 424726550327841305062669)
                  ·
                    rfl

theorem cell20_930546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_930546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930546 prefixEnd_930546 := by exact prefixLift 930546
  have htrace : WordTrace (prefixWord ++ tailWord_930546) baseStart_930546 baseEnd_930546 := by
    simpa [prefixWord, tailWord_930546, baseEnd_930546] using wordTrace_append hprefix tailTrace_930546
  have hstable : (prefixWord ++ tailWord_930546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930546).length < 2 ^ (prefixWord ++ tailWord_930546).sum := by decide
  have hdescent : baseEnd_930546 < baseStart_930546 := by decide
  rcases family_descends (prefixWord ++ tailWord_930546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930577 : List Nat := [1, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_930577 : Nat := 118140960795 + 930577 * 2 ^ 59
def prefixEnd_930577 : Nat := 4983230072969 + 3 ^ 40 * 930577 * 2
def baseEnd_930577 : Nat := 424740699572542975029209

theorem tailTrace_930577 : CollatzResearch.WordTrace tailWord_930577 prefixEnd_930577 424740699572542975029209 := by
  unfold tailWord_930577
  simp only [CollatzResearch.WordTrace]
  refine ⟨33940931549685933743653985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22627287699790622495769323 33940931549685933743653985)
  ·
    refine ⟨25455698662264450307740489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33940931549685933743653985 25455698662264450307740489)
    ·
      refine ⟨19091773996698337730805367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25455698662264450307740489 19091773996698337730805367)
      ·
        refine ⟨28637660995047506596208051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19091773996698337730805367 28637660995047506596208051)
        ·
          refine ⟨42956491492571259894312077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28637660995047506596208051 42956491492571259894312077)
          ·
            refine ⟨16108684309714222460367029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42956491492571259894312077 16108684309714222460367029)
            ·
              refine ⟨1510189154035708355659409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16108684309714222460367029 1510189154035708355659409)
              ·
                refine ⟨1132641865526781266744557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510189154035708355659409 1132641865526781266744557)
                ·
                  refine ⟨424740699572542975029209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132641865526781266744557 424740699572542975029209)
                  ·
                    rfl

theorem cell20_930577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_930577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930577 prefixEnd_930577 := by exact prefixLift 930577
  have htrace : WordTrace (prefixWord ++ tailWord_930577) baseStart_930577 baseEnd_930577 := by
    simpa [prefixWord, tailWord_930577, baseEnd_930577] using wordTrace_append hprefix tailTrace_930577
  have hstable : (prefixWord ++ tailWord_930577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930577).length < 2 ^ (prefixWord ++ tailWord_930577).sum := by decide
  have hdescent : baseEnd_930577 < baseStart_930577 := by decide
  rcases family_descends (prefixWord ++ tailWord_930577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930614 : List Nat := [5, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_930614 : Nat := 118140960795 + 930614 * 2 ^ 59
def prefixEnd_930614 : Nat := 4983230072969 + 3 ^ 40 * 930614 * 2
def baseEnd_930614 : Nat := 424757587380735290795725

theorem tailTrace_930614 : CollatzResearch.WordTrace tailWord_930614 prefixEnd_930614 424757587380735290795725 := by
  unfold tailWord_930614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121392565659493066421931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22628187367034592708500597 2121392565659493066421931)
  ·
    refine ⟨3182088848489239599632897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121392565659493066421931 3182088848489239599632897)
    ·
      refine ⟨2386566636366929699724673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3182088848489239599632897 2386566636366929699724673)
      ·
        refine ⟨1789924977275197274793505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2386566636366929699724673 1789924977275197274793505)
        ·
          refine ⟨1342443732956397956095129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1789924977275197274793505 1342443732956397956095129)
          ·
            refine ⟨1006832799717298467071347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342443732956397956095129 1006832799717298467071347)
            ·
              refine ⟨1510249199575947700607021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1006832799717298467071347 1510249199575947700607021)
              ·
                refine ⟨566343449840980387727633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1510249199575947700607021 566343449840980387727633)
                ·
                  refine ⟨424757587380735290795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566343449840980387727633 424757587380735290795725)
                  ·
                    rfl

theorem cell20_930614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_930614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930614 prefixEnd_930614 := by exact prefixLift 930614
  have htrace : WordTrace (prefixWord ++ tailWord_930614) baseStart_930614 baseEnd_930614 := by
    simpa [prefixWord, tailWord_930614, baseEnd_930614] using wordTrace_append hprefix tailTrace_930614
  have hstable : (prefixWord ++ tailWord_930614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930614).length < 2 ^ (prefixWord ++ tailWord_930614).sum := by decide
  have hdescent : baseEnd_930614 < baseStart_930614 := by decide
  rcases family_descends (prefixWord ++ tailWord_930614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930625 : List Nat := [1, 2, 5, 3, 1, 2, 6]
def baseStart_930625 : Nat := 118140960795 + 930625 * 2 ^ 59
def prefixEnd_930625 : Nat := 4983230072969 + 3 ^ 40 * 930625 * 2
def baseEnd_930625 : Nat := 47195845342274237936557

theorem tailTrace_930625 : CollatzResearch.WordTrace tailWord_930625 prefixEnd_930625 47195845342274237936557 := by
  unfold tailWord_930625
  simp only [CollatzResearch.WordTrace]
  refine ⟨33942682253512037941401329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22628454835674691960934219 33942682253512037941401329)
  ·
    refine ⟨25457011690134028456050997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33942682253512037941401329 25457011690134028456050997)
    ·
      refine ⟨2386594845950065167754781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25457011690134028456050997 2386594845950065167754781)
      ·
        refine ⟨894973067231274437908043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2386594845950065167754781 894973067231274437908043)
        ·
          refine ⟨1342459600846911656862065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894973067231274437908043 1342459600846911656862065)
          ·
            refine ⟨1006844700635183742646549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342459600846911656862065 1006844700635183742646549)
            ·
              refine ⟨47195845342274237936557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1006844700635183742646549 47195845342274237936557)
              ·
                rfl

theorem cell20_930625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_930625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930625 prefixEnd_930625 := by exact prefixLift 930625
  have htrace : WordTrace (prefixWord ++ tailWord_930625) baseStart_930625 baseEnd_930625 := by
    simpa [prefixWord, tailWord_930625, baseEnd_930625] using wordTrace_append hprefix tailTrace_930625
  have hstable : (prefixWord ++ tailWord_930625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930625).length < 2 ^ (prefixWord ++ tailWord_930625).sum := by decide
  have hdescent : baseEnd_930625 < baseStart_930625 := by decide
  rcases family_descends (prefixWord ++ tailWord_930625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930674 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_930674 : Nat := 118140960795 + 930674 * 2 ^ 59
def prefixEnd_930674 : Nat := 4983230072969 + 3 ^ 40 * 930674 * 2
def baseEnd_930674 : Nat := 424784973015641748795479

theorem tailTrace_930674 : CollatzResearch.WordTrace tailWord_930674 prefixEnd_930674 424784973015641748795479 := by
  unfold tailWord_930674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486117357583629827483769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22629646286889679539956717 8486117357583629827483769)
  ·
    refine ⟨6364588018187722370612827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8486117357583629827483769 6364588018187722370612827)
    ·
      refine ⟨9546882027281583555919241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6364588018187722370612827 9546882027281583555919241)
      ·
        refine ⟨7160161520461187666939431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9546882027281583555919241 7160161520461187666939431)
        ·
          refine ⟨10740242280691781500409147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7160161520461187666939431 10740242280691781500409147)
          ·
            refine ⟨16110363421037672250613721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10740242280691781500409147 16110363421037672250613721)
            ·
              refine ⟨12082772565778254187960291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16110363421037672250613721 12082772565778254187960291)
              ·
                refine ⟨18124158848667381281940437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12082772565778254187960291 18124158848667381281940437)
                ·
                  refine ⟨424784973015641748795479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18124158848667381281940437 424784973015641748795479)
                  ·
                    rfl

theorem cell20_930674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_930674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930674 prefixEnd_930674 := by exact prefixLift 930674
  have htrace : WordTrace (prefixWord ++ tailWord_930674) baseStart_930674 baseEnd_930674 := by
    simpa [prefixWord, tailWord_930674, baseEnd_930674] using wordTrace_append hprefix tailTrace_930674
  have hstable : (prefixWord ++ tailWord_930674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930674).length < 2 ^ (prefixWord ++ tailWord_930674).sum := by decide
  have hdescent : baseEnd_930674 < baseStart_930674 := by decide
  rcases family_descends (prefixWord ++ tailWord_930674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930690 : List Nat := [3, 4, 2, 2, 1, 1, 1, 4, 2]
def baseStart_930690 : Nat := 118140960795 + 930690 * 2 ^ 59
def prefixEnd_930690 : Nat := 4983230072969 + 3 ^ 40 * 930690 * 2
def baseEnd_930690 : Nat := 424792275851616804262081

theorem tailTrace_930690 : CollatzResearch.WordTrace tailWord_930690 prefixEnd_930690 424792275851616804262081 := by
  unfold tailWord_930690
  simp only [CollatzResearch.WordTrace]
  refine ⟨8486263249569138510629381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22630035332184369361678349 8486263249569138510629381)
  ·
    refine ⟨1591174359294213470743009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8486263249569138510629381 1591174359294213470743009)
    ·
      refine ⟨1193380769470660103057257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1591174359294213470743009 1193380769470660103057257)
      ·
        refine ⟨895035577102995077292943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1193380769470660103057257 895035577102995077292943)
        ·
          refine ⟨1342553365654492615939415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895035577102995077292943 1342553365654492615939415)
          ·
            refine ⟨2013830048481738923909123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342553365654492615939415 2013830048481738923909123)
            ·
              refine ⟨3020745072722608385863685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013830048481738923909123 3020745072722608385863685)
              ·
                refine ⟨566389701135489072349441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3020745072722608385863685 566389701135489072349441)
                ·
                  refine ⟨424792275851616804262081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 566389701135489072349441 424792275851616804262081)
                  ·
                    rfl

theorem cell20_930690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_930690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930690 prefixEnd_930690 := by exact prefixLift 930690
  have htrace : WordTrace (prefixWord ++ tailWord_930690) baseStart_930690 baseEnd_930690 := by
    simpa [prefixWord, tailWord_930690, baseEnd_930690] using wordTrace_append hprefix tailTrace_930690
  have hstable : (prefixWord ++ tailWord_930690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930690).length < 2 ^ (prefixWord ++ tailWord_930690).sum := by decide
  have hdescent : baseEnd_930690 < baseStart_930690 := by decide
  rcases family_descends (prefixWord ++ tailWord_930690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930691 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_930691 : Nat := 118140960795 + 930691 * 2 ^ 59
def prefixEnd_930691 : Nat := 4983230072969 + 3 ^ 40 * 930691 * 2
def baseEnd_930691 : Nat := 424792732278865245228743

theorem tailTrace_930691 : CollatzResearch.WordTrace tailWord_930691 prefixEnd_930691 424792732278865245228743 := by
  unfold tailWord_930691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33945089471272931213303927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22630059647515287475535951 33945089471272931213303927)
  ·
    refine ⟨50917634206909396819955891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33945089471272931213303927 50917634206909396819955891)
    ·
      refine ⟨76376451310364095229933837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50917634206909396819955891 76376451310364095229933837)
      ·
        refine ⟨28641169241386535711225189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76376451310364095229933837 28641169241386535711225189)
        ·
          refine ⟨5370219232759975445854723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28641169241386535711225189 5370219232759975445854723)
          ·
            refine ⟨8055328849139963168782085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5370219232759975445854723 8055328849139963168782085)
            ·
              refine ⟨1510374159213743094146641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8055328849139963168782085 1510374159213743094146641)
              ·
                refine ⟨1132780619410307320609981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1510374159213743094146641 1132780619410307320609981)
                ·
                  refine ⟨424792732278865245228743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1132780619410307320609981 424792732278865245228743)
                  ·
                    rfl

theorem cell20_930691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_930691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930691 prefixEnd_930691 := by exact prefixLift 930691
  have htrace : WordTrace (prefixWord ++ tailWord_930691) baseStart_930691 baseEnd_930691 := by
    simpa [prefixWord, tailWord_930691, baseEnd_930691] using wordTrace_append hprefix tailTrace_930691
  have hstable : (prefixWord ++ tailWord_930691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930691).length < 2 ^ (prefixWord ++ tailWord_930691).sum := by decide
  have hdescent : baseEnd_930691 < baseStart_930691 := by decide
  rcases family_descends (prefixWord ++ tailWord_930691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930742 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_930742 : Nat := 118140960795 + 930742 * 2 ^ 59
def prefixEnd_930742 : Nat := 4983230072969 + 3 ^ 40 * 930742 * 2
def baseEnd_930742 : Nat := 424816010068535734528535

theorem tailTrace_930742 : CollatzResearch.WordTrace tailWord_930742 prefixEnd_930742 424816010068535734528535 := by
  unfold tailWord_930742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2121684349630510432713155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22631299729392111282273653 2121684349630510432713155)
  ·
    refine ⟨3182526524445765649069733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2121684349630510432713155 3182526524445765649069733)
    ·
      refine ⟨596723723333581059200575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3182526524445765649069733 596723723333581059200575)
      ·
        refine ⟨895085585000371588800863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596723723333581059200575 895085585000371588800863)
        ·
          refine ⟨1342628377500557383201295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 895085585000371588800863 1342628377500557383201295)
          ·
            refine ⟨2013942566250836074801943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1342628377500557383201295 2013942566250836074801943)
            ·
              refine ⟨3020913849376254112202915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2013942566250836074801943 3020913849376254112202915)
              ·
                refine ⟨4531370774064381168304373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3020913849376254112202915 4531370774064381168304373)
                ·
                  refine ⟨424816010068535734528535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4531370774064381168304373 424816010068535734528535)
                  ·
                    rfl

theorem cell20_930742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_930742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930742 prefixEnd_930742 := by exact prefixLift 930742
  have htrace : WordTrace (prefixWord ++ tailWord_930742) baseStart_930742 baseEnd_930742 := by
    simpa [prefixWord, tailWord_930742, baseEnd_930742] using wordTrace_append hprefix tailTrace_930742
  have hstable : (prefixWord ++ tailWord_930742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930742).length < 2 ^ (prefixWord ++ tailWord_930742).sum := by decide
  have hdescent : baseEnd_930742 < baseStart_930742 := by decide
  rcases family_descends (prefixWord ++ tailWord_930742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930798 : List Nat := [4, 1, 2, 1, 4, 2, 6]
def baseStart_930798 : Nat := 118140960795 + 930798 * 2 ^ 59
def prefixEnd_930798 : Nat := 4983230072969 + 3 ^ 40 * 930798 * 2
def baseEnd_930798 : Nat := 47204618888272047629071

theorem tailTrace_930798 : CollatzResearch.WordTrace tailWord_930798 prefixEnd_930798 47204618888272047629071 := by
  unfold tailWord_930798
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243624010235661060931131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22632661387923525658299365 4243624010235661060931131)
  ·
    refine ⟨6365436015353491591396697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4243624010235661060931131 6365436015353491591396697)
    ·
      refine ⟨4774077011515118693547523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6365436015353491591396697 4774077011515118693547523)
      ·
        refine ⟨7161115517272678040321285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4774077011515118693547523 7161115517272678040321285)
        ·
          refine ⟨1342709159488627132560241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7161115517272678040321285 1342709159488627132560241)
          ·
            refine ⟨1007031869616470349420181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1342709159488627132560241 1007031869616470349420181)
            ·
              refine ⟨47204618888272047629071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1007031869616470349420181 47204618888272047629071)
              ·
                rfl

theorem cell20_930798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 6].length) (baseStart_930798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930798 prefixEnd_930798 := by exact prefixLift 930798
  have htrace : WordTrace (prefixWord ++ tailWord_930798) baseStart_930798 baseEnd_930798 := by
    simpa [prefixWord, tailWord_930798, baseEnd_930798] using wordTrace_append hprefix tailTrace_930798
  have hstable : (prefixWord ++ tailWord_930798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930798).length < 2 ^ (prefixWord ++ tailWord_930798).sum := by decide
  have hdescent : baseEnd_930798 < baseStart_930798 := by decide
  rcases family_descends (prefixWord ++ tailWord_930798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930812 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_930812 : Nat := 118140960795 + 930812 * 2 ^ 59
def prefixEnd_930812 : Nat := 4983230072969 + 3 ^ 40 * 930812 * 2
def baseEnd_930812 : Nat := 424847959975926602194915

theorem tailTrace_930812 : CollatzResearch.WordTrace tailWord_930812 prefixEnd_930812 424847959975926602194915 := by
  unfold tailWord_930812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16974751351917284439229345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22633001802556379252305793 16974751351917284439229345)
  ·
    refine ⟨12731063513937963329422009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16974751351917284439229345 12731063513937963329422009)
    ·
      refine ⟨9548297635453472497066507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12731063513937963329422009 9548297635453472497066507)
      ·
        refine ⟨14322446453180208745599761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9548297635453472497066507 14322446453180208745599761)
        ·
          refine ⟨10741834839885156559199821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14322446453180208745599761 10741834839885156559199821)
          ·
            refine ⟨4028188064956933709699933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10741834839885156559199821 4028188064956933709699933)
            ·
              refine ⟨1510570524358850141137475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4028188064956933709699933 1510570524358850141137475)
              ·
                refine ⟨2265855786538275211706213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1510570524358850141137475 2265855786538275211706213)
                ·
                  refine ⟨424847959975926602194915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265855786538275211706213 424847959975926602194915)
                  ·
                    rfl

theorem cell20_930812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_930812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930812 prefixEnd_930812 := by exact prefixLift 930812
  have htrace : WordTrace (prefixWord ++ tailWord_930812) baseStart_930812 baseEnd_930812 := by
    simpa [prefixWord, tailWord_930812, baseEnd_930812] using wordTrace_append hprefix tailTrace_930812
  have hstable : (prefixWord ++ tailWord_930812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930812).length < 2 ^ (prefixWord ++ tailWord_930812).sum := by decide
  have hdescent : baseEnd_930812 < baseStart_930812 := by decide
  rcases family_descends (prefixWord ++ tailWord_930812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930833 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_930833 : Nat := 118140960795 + 930833 * 2 ^ 59
def prefixEnd_930833 : Nat := 4983230072969 + 3 ^ 40 * 930833 * 2
def baseEnd_930833 : Nat := 424857544948143862494829

theorem tailTrace_930833 : CollatzResearch.WordTrace tailWord_930833 prefixEnd_930833 424857544948143862494829 := by
  unfold tailWord_930833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33950268636758489464973153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22633512424505659643315435 33950268636758489464973153)
  ·
    refine ⟨25462701477568867098729865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33950268636758489464973153 25462701477568867098729865)
    ·
      refine ⟨19097026108176650324047399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25462701477568867098729865 19097026108176650324047399)
      ·
        refine ⟨28645539162264975486071099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097026108176650324047399 28645539162264975486071099)
        ·
          refine ⟨42968308743397463229106649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28645539162264975486071099 42968308743397463229106649)
          ·
            refine ⟨32226231557548097421829987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42968308743397463229106649 32226231557548097421829987)
            ·
              refine ⟨48339347336322146132744981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32226231557548097421829987 48339347336322146132744981)
              ·
                refine ⟨2265906906390100599972421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48339347336322146132744981 2265906906390100599972421)
                ·
                  refine ⟨424857544948143862494829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265906906390100599972421 424857544948143862494829)
                  ·
                    rfl

theorem cell20_930833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_930833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930833 prefixEnd_930833 := by exact prefixLift 930833
  have htrace : WordTrace (prefixWord ++ tailWord_930833) baseStart_930833 baseEnd_930833 := by
    simpa [prefixWord, tailWord_930833, baseEnd_930833] using wordTrace_append hprefix tailTrace_930833
  have hstable : (prefixWord ++ tailWord_930833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930833).length < 2 ^ (prefixWord ++ tailWord_930833).sum := by decide
  have hdescent : baseEnd_930833 < baseStart_930833 := by decide
  rcases family_descends (prefixWord ++ tailWord_930833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_930871 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_930871 : Nat := 118140960795 + 930871 * 2 ^ 59
def prefixEnd_930871 : Nat := 4983230072969 + 3 ^ 40 * 930871 * 2
def baseEnd_930871 : Nat := 424874889183584619228007

theorem tailTrace_930871 : CollatzResearch.WordTrace tailWord_930871 prefixEnd_930871 424874889183584619228007 := by
  unfold tailWord_930871
  simp only [CollatzResearch.WordTrace]
  refine ⟨33951654610620821954856467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22634436407080547969904311 33951654610620821954856467)
  ·
    refine ⟨50927481915931232932284701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33951654610620821954856467 50927481915931232932284701)
    ·
      refine ⟨19097805718474212349606763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50927481915931232932284701 19097805718474212349606763)
      ·
        refine ⟨28646708577711318524410145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19097805718474212349606763 28646708577711318524410145)
        ·
          refine ⟨21485031433283488893307609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28646708577711318524410145 21485031433283488893307609)
          ·
            refine ⟨16113773574962616669980707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21485031433283488893307609 16113773574962616669980707)
            ·
              refine ⟨24170660362443925004971061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16113773574962616669980707 24170660362443925004971061)
              ·
                refine ⟨2265999408979117969216037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24170660362443925004971061 2265999408979117969216037)
                ·
                  refine ⟨424874889183584619228007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2265999408979117969216037 424874889183584619228007)
                  ·
                    rfl

theorem cell20_930871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_930871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_930871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_930871 prefixEnd_930871 := by exact prefixLift 930871
  have htrace : WordTrace (prefixWord ++ tailWord_930871) baseStart_930871 baseEnd_930871 := by
    simpa [prefixWord, tailWord_930871, baseEnd_930871] using wordTrace_append hprefix tailTrace_930871
  have hstable : (prefixWord ++ tailWord_930871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_930871).length < 2 ^ (prefixWord ++ tailWord_930871).sum := by decide
  have hdescent : baseEnd_930871 < baseStart_930871 := by decide
  rcases family_descends (prefixWord ++ tailWord_930871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
