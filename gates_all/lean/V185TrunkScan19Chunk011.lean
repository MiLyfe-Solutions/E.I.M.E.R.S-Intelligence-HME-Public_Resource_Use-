import V185TrunkScan19Chunk010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_111450 : List Nat := [3, 1, 1, 2, 1, 6, 5]
def baseStart_111450 : Nat := 118140960795 + 111450 * 2 ^ 59
def prefixEnd_111450 : Nat := 4983230072969 + 3 ^ 40 * 111450 * 2
def baseEnd_111450 : Nat := 11304181519742061246905

theorem tailTrace_111450 : CollatzResearch.WordTrace tailWord_111450 prefixEnd_111450 11304181519742061246905 := by
  unfold tailWord_111450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1016228861560789747430951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2709943630828772659815869 1016228861560789747430951)
  ·
    refine ⟨1524343292341184621146427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1016228861560789747430951 1524343292341184621146427)
    ·
      refine ⟨2286514938511776931719641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1524343292341184621146427 2286514938511776931719641)
      ·
        refine ⟨1714886203883832698789731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2286514938511776931719641 1714886203883832698789731)
        ·
          refine ⟨2572329305825749048184597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1714886203883832698789731 2572329305825749048184597)
          ·
            refine ⟨120577936210581986633653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2572329305825749048184597 120577936210581986633653)
            ·
              refine ⟨11304181519742061246905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120577936210581986633653 11304181519742061246905)
              ·
                rfl

theorem cell19_111450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 5].length) (baseStart_111450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111450 prefixEnd_111450 := by exact prefixLift 111450
  have htrace : WordTrace (prefixWord ++ tailWord_111450) baseStart_111450 baseEnd_111450 := by
    simpa [prefixWord, tailWord_111450, baseEnd_111450] using wordTrace_append hprefix tailTrace_111450
  have hstable : (prefixWord ++ tailWord_111450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111450).length < 2 ^ (prefixWord ++ tailWord_111450).sum := by decide
  have hdescent : baseEnd_111450 < baseStart_111450 := by decide
  rcases family_descends (prefixWord ++ tailWord_111450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111509 : List Nat := [1, 3, 2, 1, 1, 11]
def baseStart_111509 : Nat := 118140960795 + 111509 * 2 ^ 59
def prefixEnd_111509 : Nat := 4983230072969 + 3 ^ 40 * 111509 * 2
def baseEnd_111509 : Nat := 3770055262703503158827

theorem tailTrace_111509 : CollatzResearch.WordTrace tailWord_111509 prefixEnd_111509 3770055262703503158827 := by
  unfold tailWord_111509
  simp only [CollatzResearch.WordTrace]
  refine ⟨4067067353029412066121581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2711378235352941377414387 4067067353029412066121581)
  ·
    refine ⟨1525150257386029524795593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4067067353029412066121581 1525150257386029524795593)
    ·
      refine ⟨1143862693039522143596695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1525150257386029524795593 1143862693039522143596695)
      ·
        refine ⟨1715794039559283215395043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1143862693039522143596695 1715794039559283215395043)
        ·
          refine ⟨2573691059338924823092565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1715794039559283215395043 2573691059338924823092565)
          ·
            refine ⟨3770055262703503158827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2573691059338924823092565 3770055262703503158827)
            ·
              rfl

theorem cell19_111509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 11].length) (baseStart_111509 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111509 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111509 prefixEnd_111509 := by exact prefixLift 111509
  have htrace : WordTrace (prefixWord ++ tailWord_111509) baseStart_111509 baseEnd_111509 := by
    simpa [prefixWord, tailWord_111509, baseEnd_111509] using wordTrace_append hprefix tailTrace_111509
  have hstable : (prefixWord ++ tailWord_111509).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111509).length < 2 ^ (prefixWord ++ tailWord_111509).sum := by decide
  have hdescent : baseEnd_111509 < baseStart_111509 := by decide
  rcases family_descends (prefixWord ++ tailWord_111509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111585 : List Nat := [1, 2, 3, 1, 2, 1, 1, 8]
def baseStart_111585 : Nat := 118140960795 + 111585 * 2 ^ 59
def prefixEnd_111585 : Nat := 4983230072969 + 3 ^ 40 * 111585 * 2
def baseEnd_111585 : Nat := 33953623011585870740347

theorem tailTrace_111585 : CollatzResearch.WordTrace tailWord_111585 prefixEnd_111585 33953623011585870740347 := by
  unfold tailWord_111585
  simp only [CollatzResearch.WordTrace]
  refine ⟨4069839300754077045888209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2713226200502718030592139 4069839300754077045888209)
  ·
    refine ⟨3052379475565557784416157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4069839300754077045888209 3052379475565557784416157)
    ·
      refine ⟨1144642303337084169156059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3052379475565557784416157 1144642303337084169156059)
      ·
        refine ⟨1716963455005626253734089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1144642303337084169156059 1716963455005626253734089)
        ·
          refine ⟨1287722591254219690300567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1716963455005626253734089 1287722591254219690300567)
          ·
            refine ⟨1931583886881329535450851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1287722591254219690300567 1931583886881329535450851)
            ·
              refine ⟨2897375830321994303176277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1931583886881329535450851 2897375830321994303176277)
              ·
                refine ⟨33953623011585870740347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2897375830321994303176277 33953623011585870740347)
                ·
                  rfl

theorem cell19_111585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 8].length) (baseStart_111585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111585 prefixEnd_111585 := by exact prefixLift 111585
  have htrace : WordTrace (prefixWord ++ tailWord_111585) baseStart_111585 baseEnd_111585 := by
    simpa [prefixWord, tailWord_111585, baseEnd_111585] using wordTrace_append hprefix tailTrace_111585
  have hstable : (prefixWord ++ tailWord_111585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111585).length < 2 ^ (prefixWord ++ tailWord_111585).sum := by decide
  have hdescent : baseEnd_111585 < baseStart_111585 := by decide
  rcases family_descends (prefixWord ++ tailWord_111585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111598 : List Nat := [4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_111598 : Nat := 118140960795 + 111598 * 2 ^ 59
def prefixEnd_111598 : Nat := 4983230072969 + 3 ^ 40 * 111598 * 2
def baseEnd_111598 : Nat := 33957578714405692451423

theorem tailTrace_111598 : CollatzResearch.WordTrace tailWord_111598 prefixEnd_111598 33957578714405692451423 := by
  unfold tailWord_111598
  simp only [CollatzResearch.WordTrace]
  refine ⟨508789181213372533263931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2713542299804653510740965 508789181213372533263931)
  ·
    refine ⟨763183771820058799895897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 508789181213372533263931 763183771820058799895897)
    ·
      refine ⟨572387828865044099921923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 763183771820058799895897 572387828865044099921923)
      ·
        refine ⟨858581743297566149882885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 572387828865044099921923 858581743297566149882885)
        ·
          refine ⟨160984076868293653103041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 858581743297566149882885 160984076868293653103041)
          ·
            refine ⟨120738057651220239827281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160984076868293653103041 120738057651220239827281)
            ·
              refine ⟨90553543238415179870461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120738057651220239827281 90553543238415179870461)
              ·
                refine ⟨33957578714405692451423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90553543238415179870461 33957578714405692451423)
                ·
                  rfl

theorem cell19_111598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_111598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111598 prefixEnd_111598 := by exact prefixLift 111598
  have htrace : WordTrace (prefixWord ++ tailWord_111598) baseStart_111598 baseEnd_111598 := by
    simpa [prefixWord, tailWord_111598, baseEnd_111598] using wordTrace_append hprefix tailTrace_111598
  have hstable : (prefixWord ++ tailWord_111598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111598).length < 2 ^ (prefixWord ++ tailWord_111598).sum := by decide
  have hdescent : baseEnd_111598 < baseStart_111598 := by decide
  rcases family_descends (prefixWord ++ tailWord_111598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111634 : List Nat := [3, 2, 5, 1, 1, 1, 2, 4]
def baseStart_111634 : Nat := 118140960795 + 111634 * 2 ^ 59
def prefixEnd_111634 : Nat := 4983230072969 + 3 ^ 40 * 111634 * 2
def baseEnd_111634 : Nat := 33968532968368275651325

theorem tailTrace_111634 : CollatzResearch.WordTrace tailWord_111634 prefixEnd_111634 33968532968368275651325 := by
  unfold tailWord_111634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1017906619394139603605489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2714417651717705609614637 1017906619394139603605489)
  ·
    refine ⟨763429964545604702704117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1017906619394139603605489 763429964545604702704117)
    ·
      refine ⟨71571559176150440878511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 763429964545604702704117 71571559176150440878511)
      ·
        refine ⟨107357338764225661317767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71571559176150440878511 107357338764225661317767)
        ·
          refine ⟨161036008146338491976651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107357338764225661317767 161036008146338491976651)
          ·
            refine ⟨241554012219507737964977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161036008146338491976651 241554012219507737964977)
            ·
              refine ⟨181165509164630803473733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241554012219507737964977 181165509164630803473733)
              ·
                refine ⟨33968532968368275651325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181165509164630803473733 33968532968368275651325)
                ·
                  rfl

theorem cell19_111634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_111634 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111634 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111634 prefixEnd_111634 := by exact prefixLift 111634
  have htrace : WordTrace (prefixWord ++ tailWord_111634) baseStart_111634 baseEnd_111634 := by
    simpa [prefixWord, tailWord_111634, baseEnd_111634] using wordTrace_append hprefix tailTrace_111634
  have hstable : (prefixWord ++ tailWord_111634).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111634).length < 2 ^ (prefixWord ++ tailWord_111634).sum := by decide
  have hdescent : baseEnd_111634 < baseStart_111634 := by decide
  rcases family_descends (prefixWord ++ tailWord_111634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111640 : List Nat := [2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_111640 : Nat := 118140960795 + 111640 * 2 ^ 59
def prefixEnd_111640 : Nat := 4983230072969 + 3 ^ 40 * 111640 * 2
def baseEnd_111640 : Nat := 33970358677362039517975

theorem tailTrace_111640 : CollatzResearch.WordTrace tailWord_111640 prefixEnd_111640 33970358677362039517975 := by
  unfold tailWord_111640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2035922657777410719570187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2714563543703214292760249 2035922657777410719570187)
  ·
    refine ⟨3053883986666116079355281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2035922657777410719570187 3053883986666116079355281)
    ·
      refine ⟨2290412989999587059516461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3053883986666116079355281 2290412989999587059516461)
      ·
        refine ⟨858904871249845147318673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2290412989999587059516461 858904871249845147318673)
        ·
          refine ⟨644178653437383860489005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 858904871249845147318673 644178653437383860489005)
          ·
            refine ⟨241566995039018947683377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 644178653437383860489005 241566995039018947683377)
            ·
              refine ⟨181175246279264210762533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241566995039018947683377 181175246279264210762533)
              ·
                refine ⟨33970358677362039517975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181175246279264210762533 33970358677362039517975)
                ·
                  rfl

theorem cell19_111640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_111640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111640 prefixEnd_111640 := by exact prefixLift 111640
  have htrace : WordTrace (prefixWord ++ tailWord_111640) baseStart_111640 baseEnd_111640 := by
    simpa [prefixWord, tailWord_111640, baseEnd_111640] using wordTrace_append hprefix tailTrace_111640
  have hstable : (prefixWord ++ tailWord_111640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111640).length < 2 ^ (prefixWord ++ tailWord_111640).sum := by decide
  have hdescent : baseEnd_111640 < baseStart_111640 := by decide
  rcases family_descends (prefixWord ++ tailWord_111640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111678 : List Nat := [4, 2, 1, 3, 1, 8]
def baseStart_111678 : Nat := 118140960795 + 111678 * 2 ^ 59
def prefixEnd_111678 : Nat := 4983230072969 + 3 ^ 40 * 111678 * 2
def baseEnd_111678 : Nat := 3775769055665467852603

theorem tailTrace_111678 : CollatzResearch.WordTrace tailWord_111678 prefixEnd_111678 3775769055665467852603 := by
  unfold tailWord_111678
  simp only [CollatzResearch.WordTrace]
  refine ⟨509153911177144241127961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2715487526278102619349125 509153911177144241127961)
  ·
    refine ⟨381865433382858180845971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 509153911177144241127961 381865433382858180845971)
    ·
      refine ⟨572798150074287271268957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 381865433382858180845971 572798150074287271268957)
      ·
        refine ⟨214799306277857726725859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 572798150074287271268957 214799306277857726725859)
        ·
          refine ⟨322198959416786590088789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214799306277857726725859 322198959416786590088789)
          ·
            refine ⟨3775769055665467852603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 322198959416786590088789 3775769055665467852603)
            ·
              rfl

theorem cell19_111678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_111678 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111678 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111678 prefixEnd_111678 := by exact prefixLift 111678
  have htrace : WordTrace (prefixWord ++ tailWord_111678) baseStart_111678 baseEnd_111678 := by
    simpa [prefixWord, tailWord_111678, baseEnd_111678] using wordTrace_append hprefix tailTrace_111678
  have hstable : (prefixWord ++ tailWord_111678).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111678).length < 2 ^ (prefixWord ++ tailWord_111678).sum := by decide
  have hdescent : baseEnd_111678 < baseStart_111678 := by decide
  rcases family_descends (prefixWord ++ tailWord_111678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111710 : List Nat := [4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_111710 : Nat := 118140960795 + 111710 * 2 ^ 59
def prefixEnd_111710 : Nat := 4983230072969 + 3 ^ 40 * 111710 * 2
def baseEnd_111710 : Nat := 33991658615622617962229

theorem tailTrace_111710 : CollatzResearch.WordTrace tailWord_111710 prefixEnd_111710 33991658615622617962229 := by
  unfold tailWord_111710
  simp only [CollatzResearch.WordTrace]
  refine ⟨509299803162652924273573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2716265616867482262792389 509299803162652924273573)
  ·
    refine ⟨95493713092997423301295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 509299803162652924273573 95493713092997423301295)
    ·
      refine ⟨143240569639496134951943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95493713092997423301295 143240569639496134951943)
      ·
        refine ⟨214860854459244202427915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143240569639496134951943 214860854459244202427915)
        ·
          refine ⟨322291281688866303641873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 214860854459244202427915 322291281688866303641873)
          ·
            refine ⟨241718461266649727731405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322291281688866303641873 241718461266649727731405)
            ·
              refine ⟨90644422974993647899277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 241718461266649727731405 90644422974993647899277)
              ·
                refine ⟨33991658615622617962229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90644422974993647899277 33991658615622617962229)
                ·
                  rfl

theorem cell19_111710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_111710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111710 prefixEnd_111710 := by exact prefixLift 111710
  have htrace : WordTrace (prefixWord ++ tailWord_111710) baseStart_111710 baseEnd_111710 := by
    simpa [prefixWord, tailWord_111710, baseEnd_111710] using wordTrace_append hprefix tailTrace_111710
  have hstable : (prefixWord ++ tailWord_111710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111710).length < 2 ^ (prefixWord ++ tailWord_111710).sum := by decide
  have hdescent : baseEnd_111710 < baseStart_111710 := by decide
  rcases family_descends (prefixWord ++ tailWord_111710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111733 : List Nat := [1, 3, 4, 3, 1, 1, 6]
def baseStart_111733 : Nat := 118140960795 + 111733 * 2 ^ 59
def prefixEnd_111733 : Nat := 4983230072969 + 3 ^ 40 * 111733 * 2
def baseEnd_111733 : Nat := 11332885722255126483685

theorem tailTrace_111733 : CollatzResearch.WordTrace tailWord_111733 prefixEnd_111733 11332885722255126483685 := by
  unfold tailWord_111733
  simp only [CollatzResearch.WordTrace]
  refine ⟨4075237304217898322275853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2716824869478598881517235 4075237304217898322275853)
  ·
    refine ⟨1528213989081711870853445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4075237304217898322275853 1528213989081711870853445)
    ·
      refine ⟨286540122952820975785021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1528213989081711870853445 286540122952820975785021)
      ·
        refine ⟨107452546107307865919383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 286540122952820975785021 107452546107307865919383)
        ·
          refine ⟨161178819160961798879075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 107452546107307865919383 161178819160961798879075)
          ·
            refine ⟨241768228741442698318613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161178819160961798879075 241768228741442698318613)
            ·
              refine ⟨11332885722255126483685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 241768228741442698318613 11332885722255126483685)
              ·
                rfl

theorem cell19_111733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_111733 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111733 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111733 prefixEnd_111733 := by exact prefixLift 111733
  have htrace : WordTrace (prefixWord ++ tailWord_111733) baseStart_111733 baseEnd_111733 := by
    simpa [prefixWord, tailWord_111733, baseEnd_111733] using wordTrace_append hprefix tailTrace_111733
  have hstable : (prefixWord ++ tailWord_111733).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111733).length < 2 ^ (prefixWord ++ tailWord_111733).sum := by decide
  have hdescent : baseEnd_111733 < baseStart_111733 := by decide
  rcases family_descends (prefixWord ++ tailWord_111733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111794 : List Nat := [3, 2, 1, 1, 1, 4, 7]
def baseStart_111794 : Nat := 118140960795 + 111794 * 2 ^ 59
def prefixEnd_111794 : Nat := 4983230072969 + 3 ^ 40 * 111794 * 2
def baseEnd_111794 : Nat := 11339072847178437365111

theorem tailTrace_111794 : CollatzResearch.WordTrace tailWord_111794 prefixEnd_111794 11339072847178437365111 := by
  unfold tailWord_111794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1019365539249226435061609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2718308104664603826830957 1019365539249226435061609)
  ·
    refine ⟨764524154436919826296207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1019365539249226435061609 764524154436919826296207)
    ·
      refine ⟨1146786231655379739444311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 764524154436919826296207 1146786231655379739444311)
      ·
        refine ⟨1720179347483069609166467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1146786231655379739444311 1720179347483069609166467)
        ·
          refine ⟨2580269021224604413749701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1720179347483069609166467 2580269021224604413749701)
          ·
            refine ⟨483800441479613327578069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2580269021224604413749701 483800441479613327578069)
            ·
              refine ⟨11339072847178437365111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 483800441479613327578069 11339072847178437365111)
              ·
                rfl

theorem cell19_111794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_111794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111794 prefixEnd_111794 := by exact prefixLift 111794
  have htrace : WordTrace (prefixWord ++ tailWord_111794) baseStart_111794 baseEnd_111794 := by
    simpa [prefixWord, tailWord_111794, baseEnd_111794] using wordTrace_append hprefix tailTrace_111794
  have hstable : (prefixWord ++ tailWord_111794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111794).length < 2 ^ (prefixWord ++ tailWord_111794).sum := by decide
  have hdescent : baseEnd_111794 < baseStart_111794 := by decide
  rcases family_descends (prefixWord ++ tailWord_111794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111809 : List Nat := [1, 2, 6, 1, 1, 2, 2, 4]
def baseStart_111809 : Nat := 118140960795 + 111809 * 2 ^ 59
def prefixEnd_111809 : Nat := 4983230072969 + 3 ^ 40 * 111809 * 2
def baseEnd_111809 : Nat := 34021782814019721761959

theorem tailTrace_111809 : CollatzResearch.WordTrace tailWord_111809 prefixEnd_111809 34021782814019721761959 := by
  unfold tailWord_111809
  simp only [CollatzResearch.WordTrace]
  refine ⟨4078009251942563302042481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2718672834628375534694987 4078009251942563302042481)
  ·
    refine ⟨3058506938956922476531861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4078009251942563302042481 3058506938956922476531861)
    ·
      refine ⟨143367512763605741087431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3058506938956922476531861 143367512763605741087431)
      ·
        refine ⟨215051269145408611631147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143367512763605741087431 215051269145408611631147)
        ·
          refine ⟨322576903718112917446721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215051269145408611631147 322576903718112917446721)
          ·
            refine ⟨241932677788584688085041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 322576903718112917446721 241932677788584688085041)
            ·
              refine ⟨181449508341438516063781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 241932677788584688085041 181449508341438516063781)
              ·
                refine ⟨34021782814019721761959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181449508341438516063781 34021782814019721761959)
                ·
                  rfl

theorem cell19_111809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 4].length) (baseStart_111809 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111809 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111809 prefixEnd_111809 := by exact prefixLift 111809
  have htrace : WordTrace (prefixWord ++ tailWord_111809) baseStart_111809 baseEnd_111809 := by
    simpa [prefixWord, tailWord_111809, baseEnd_111809] using wordTrace_append hprefix tailTrace_111809
  have hstable : (prefixWord ++ tailWord_111809).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111809).length < 2 ^ (prefixWord ++ tailWord_111809).sum := by decide
  have hdescent : baseEnd_111809 < baseStart_111809 := by decide
  rcases family_descends (prefixWord ++ tailWord_111809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111860 : List Nat := [2, 6, 1, 2, 2, 1, 1, 4]
def baseStart_111860 : Nat := 118140960795 + 111860 * 2 ^ 59
def prefixEnd_111860 : Nat := 4983230072969 + 3 ^ 40 * 111860 * 2
def baseEnd_111860 : Nat := 34037301340466714628487

theorem tailTrace_111860 : CollatzResearch.WordTrace tailWord_111860 prefixEnd_111860 34037301340466714628487 := by
  unfold tailWord_111860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2039934687378899506074517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2719912916505199341432689 2039934687378899506074517)
  ·
    refine ⟨95621938470885914347243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2039934687378899506074517 95621938470885914347243)
    ·
      refine ⟨143432907706328871520865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95621938470885914347243 143432907706328871520865)
      ·
        refine ⟨107574680779746653640649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 143432907706328871520865 107574680779746653640649)
        ·
          refine ⟨80681010584809990230487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107574680779746653640649 80681010584809990230487)
          ·
            refine ⟨121021515877214985345731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80681010584809990230487 121021515877214985345731)
            ·
              refine ⟨181532273815822478018597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121021515877214985345731 181532273815822478018597)
              ·
                refine ⟨34037301340466714628487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181532273815822478018597 34037301340466714628487)
                ·
                  rfl

theorem cell19_111860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 4].length) (baseStart_111860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111860 prefixEnd_111860 := by exact prefixLift 111860
  have htrace : WordTrace (prefixWord ++ tailWord_111860) baseStart_111860 baseEnd_111860 := by
    simpa [prefixWord, tailWord_111860, baseEnd_111860] using wordTrace_append hprefix tailTrace_111860
  have hstable : (prefixWord ++ tailWord_111860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111860).length < 2 ^ (prefixWord ++ tailWord_111860).sum := by decide
  have hdescent : baseEnd_111860 < baseStart_111860 := by decide
  rcases family_descends (prefixWord ++ tailWord_111860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111906 : List Nat := [3, 3, 1, 1, 4, 1, 6]
def baseStart_111906 : Nat := 118140960795 + 111906 * 2 ^ 59
def prefixEnd_111906 : Nat := 4983230072969 + 3 ^ 40 * 111906 * 2
def baseEnd_111906 : Nat := 11350432814250745868713

theorem tailTrace_111906 : CollatzResearch.WordTrace tailWord_111906 prefixEnd_111906 11350432814250745868713 := by
  unfold tailWord_111906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1020386783147787217080893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2721031421727432578882381 1020386783147787217080893)
  ·
    refine ⟨382645043680420206405335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1020386783147787217080893 382645043680420206405335)
    ·
      refine ⟨573967565520630309608003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 382645043680420206405335 573967565520630309608003)
      ·
        refine ⟨860951348280945464412005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 573967565520630309608003 860951348280945464412005)
        ·
          refine ⟨161428377802677274577251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 860951348280945464412005 161428377802677274577251)
          ·
            refine ⟨242142566704015911865877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 161428377802677274577251 242142566704015911865877)
            ·
              refine ⟨11350432814250745868713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 242142566704015911865877 11350432814250745868713)
              ·
                rfl

theorem cell19_111906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_111906 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111906 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111906 prefixEnd_111906 := by exact prefixLift 111906
  have htrace : WordTrace (prefixWord ++ tailWord_111906) baseStart_111906 baseEnd_111906 := by
    simpa [prefixWord, tailWord_111906, baseEnd_111906] using wordTrace_append hprefix tailTrace_111906
  have hstable : (prefixWord ++ tailWord_111906).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111906).length < 2 ^ (prefixWord ++ tailWord_111906).sum := by decide
  have hdescent : baseEnd_111906 < baseStart_111906 := by decide
  rcases family_descends (prefixWord ++ tailWord_111906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111908 : List Nat := [2, 3, 1, 3, 1, 1, 8]
def baseStart_111908 : Nat := 118140960795 + 111908 * 2 ^ 59
def prefixEnd_111908 : Nat := 4983230072969 + 3 ^ 40 * 111908 * 2
def baseEnd_111908 : Nat := 11350635670805608520563

theorem tailTrace_111908 : CollatzResearch.WordTrace tailWord_111908 prefixEnd_111908 11350635670805608520563 := by
  unfold tailWord_111908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2040810039291951604948189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2721080052389268806597585 2040810039291951604948189)
  ·
    refine ⟨765303764734481851855571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2040810039291951604948189 765303764734481851855571)
    ·
      refine ⟨1147955647101722777783357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 765303764734481851855571 1147955647101722777783357)
      ·
        refine ⟨430483367663146041668759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1147955647101722777783357 430483367663146041668759)
        ·
          refine ⟨645725051494719062503139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 430483367663146041668759 645725051494719062503139)
          ·
            refine ⟨968587577242078593754709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 645725051494719062503139 968587577242078593754709)
            ·
              refine ⟨11350635670805608520563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 968587577242078593754709 11350635670805608520563)
              ·
                rfl

theorem cell19_111908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 8].length) (baseStart_111908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111908 prefixEnd_111908 := by exact prefixLift 111908
  have htrace : WordTrace (prefixWord ++ tailWord_111908) baseStart_111908 baseEnd_111908 := by
    simpa [prefixWord, tailWord_111908, baseEnd_111908] using wordTrace_append hprefix tailTrace_111908
  have hstable : (prefixWord ++ tailWord_111908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111908).length < 2 ^ (prefixWord ++ tailWord_111908).sum := by decide
  have hdescent : baseEnd_111908 < baseStart_111908 := by decide
  rcases family_descends (prefixWord ++ tailWord_111908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111940 : List Nat := [2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_111940 : Nat := 118140960795 + 111940 * 2 ^ 59
def prefixEnd_111940 : Nat := 4983230072969 + 3 ^ 40 * 111940 * 2
def baseEnd_111940 : Nat := 34061644127050232850491

theorem tailTrace_111940 : CollatzResearch.WordTrace tailWord_111940 prefixEnd_111940 34061644127050232850491 := by
  unfold tailWord_111940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2041393607233986337530637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2721858142978648450040849 2041393607233986337530637)
  ·
    refine ⟨765522602712744876573989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2041393607233986337530637 765522602712744876573989)
    ·
      refine ⟨143535488008639664357623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 765522602712744876573989 143535488008639664357623)
      ·
        refine ⟨215303232012959496536435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 143535488008639664357623 215303232012959496536435)
        ·
          refine ⟨322954848019439244804653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 215303232012959496536435 322954848019439244804653)
          ·
            refine ⟨121108068007289716801745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 322954848019439244804653 121108068007289716801745)
            ·
              refine ⟨90831051005467287601309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121108068007289716801745 90831051005467287601309)
              ·
                refine ⟨34061644127050232850491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90831051005467287601309 34061644127050232850491)
                ·
                  rfl

theorem cell19_111940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_111940 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111940 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111940 prefixEnd_111940 := by exact prefixLift 111940
  have htrace : WordTrace (prefixWord ++ tailWord_111940) baseStart_111940 baseEnd_111940 := by
    simpa [prefixWord, tailWord_111940, baseEnd_111940] using wordTrace_append hprefix tailTrace_111940
  have hstable : (prefixWord ++ tailWord_111940).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111940).length < 2 ^ (prefixWord ++ tailWord_111940).sum := by decide
  have hdescent : baseEnd_111940 < baseStart_111940 := by decide
  rcases family_descends (prefixWord ++ tailWord_111940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_111984 : List Nat := [2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_111984 : Nat := 118140960795 + 111984 * 2 ^ 59
def prefixEnd_111984 : Nat := 4983230072969 + 3 ^ 40 * 111984 * 2
def baseEnd_111984 : Nat := 34075032659671167872593

theorem tailTrace_111984 : CollatzResearch.WordTrace tailWord_111984 prefixEnd_111984 34075032659671167872593 := by
  unfold tailWord_111984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2042196013154284094831503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2722928017539045459775337 2042196013154284094831503)
  ·
    refine ⟨3063294019731426142247255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2042196013154284094831503 3063294019731426142247255)
    ·
      refine ⟨4594941029597139213370883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063294019731426142247255 4594941029597139213370883)
      ·
        refine ⟨6892411544395708820056325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594941029597139213370883 6892411544395708820056325)
        ·
          refine ⟨1292327164574195403760561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6892411544395708820056325 1292327164574195403760561)
          ·
            refine ⟨969245373430646552820421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1292327164574195403760561 969245373430646552820421)
            ·
              refine ⟨181733507518246228653829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 969245373430646552820421 181733507518246228653829)
              ·
                refine ⟨34075032659671167872593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 181733507518246228653829 34075032659671167872593)
                ·
                  rfl

theorem cell19_111984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_111984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_111984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_111984 prefixEnd_111984 := by exact prefixLift 111984
  have htrace : WordTrace (prefixWord ++ tailWord_111984) baseStart_111984 baseEnd_111984 := by
    simpa [prefixWord, tailWord_111984, baseEnd_111984] using wordTrace_append hprefix tailTrace_111984
  have hstable : (prefixWord ++ tailWord_111984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_111984).length < 2 ^ (prefixWord ++ tailWord_111984).sum := by decide
  have hdescent : baseEnd_111984 < baseStart_111984 := by decide
  rcases family_descends (prefixWord ++ tailWord_111984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112003 : List Nat := [1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_112003 : Nat := 118140960795 + 112003 * 2 ^ 59
def prefixEnd_112003 : Nat := 4983230072969 + 3 ^ 40 * 112003 * 2
def baseEnd_112003 : Nat := 34080814071484753450319

theorem tailTrace_112003 : CollatzResearch.WordTrace tailWord_112003 prefixEnd_112003 34080814071484753450319 := by
  unfold tailWord_112003
  simp only [CollatzResearch.WordTrace]
  refine ⟨4085085013239734434604663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2723390008826489623069775 4085085013239734434604663)
  ·
    refine ⟨6127627519859601651906995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4085085013239734434604663 6127627519859601651906995)
    ·
      refine ⟨9191441279789402477860493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6127627519859601651906995 9191441279789402477860493)
      ·
        refine ⟨3446790479921025929197685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9191441279789402477860493 3446790479921025929197685)
        ·
          refine ⟨323136607492596180862283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3446790479921025929197685 323136607492596180862283)
          ·
            refine ⟨484704911238894271293425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 323136607492596180862283 484704911238894271293425)
            ·
              refine ⟨363528683429170703470069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 484704911238894271293425 363528683429170703470069)
              ·
                refine ⟨34080814071484753450319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 363528683429170703470069 34080814071484753450319)
                ·
                  rfl

theorem cell19_112003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_112003 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112003 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112003 prefixEnd_112003 := by exact prefixLift 112003
  have htrace : WordTrace (prefixWord ++ tailWord_112003) baseStart_112003 baseEnd_112003 := by
    simpa [prefixWord, tailWord_112003, baseEnd_112003] using wordTrace_append hprefix tailTrace_112003
  have hstable : (prefixWord ++ tailWord_112003).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112003).length < 2 ^ (prefixWord ++ tailWord_112003).sum := by decide
  have hdescent : baseEnd_112003 < baseStart_112003 := by decide
  rcases family_descends (prefixWord ++ tailWord_112003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112018 : List Nat := [3, 2, 3, 3, 2, 6]
def baseStart_112018 : Nat := 118140960795 + 112018 * 2 ^ 59
def prefixEnd_112018 : Nat := 4983230072969 + 3 ^ 40 * 112018 * 2
def baseEnd_112018 : Nat := 3787264260441018124105

theorem tailTrace_112018 : CollatzResearch.WordTrace tailWord_112018 prefixEnd_112018 3787264260441018124105 := by
  unfold tailWord_112018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1021408027046347999100177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2723754738790261330933805 1021408027046347999100177)
  ·
    refine ⟨766056020284760999325133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1021408027046347999100177 766056020284760999325133)
    ·
      refine ⟨287271007606785374746925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 766056020284760999325133 287271007606785374746925)
      ·
        refine ⟨107726627852544515530097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 287271007606785374746925 107726627852544515530097)
        ·
          refine ⟨80794970889408386647573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 107726627852544515530097 80794970889408386647573)
          ·
            refine ⟨3787264260441018124105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80794970889408386647573 3787264260441018124105)
            ·
              rfl

theorem cell19_112018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 6].length) (baseStart_112018 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112018 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112018 prefixEnd_112018 := by exact prefixLift 112018
  have htrace : WordTrace (prefixWord ++ tailWord_112018) baseStart_112018 baseEnd_112018 := by
    simpa [prefixWord, tailWord_112018, baseEnd_112018] using wordTrace_append hprefix tailTrace_112018
  have hstable : (prefixWord ++ tailWord_112018).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112018).length < 2 ^ (prefixWord ++ tailWord_112018).sum := by decide
  have hdescent : baseEnd_112018 < baseStart_112018 := by decide
  rcases family_descends (prefixWord ++ tailWord_112018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112132 : List Nat := [2, 3, 2, 3, 3, 1, 5]
def baseStart_112132 : Nat := 118140960795 + 112132 * 2 ^ 59
def prefixEnd_112132 : Nat := 4983230072969 + 3 ^ 40 * 112132 * 2
def baseEnd_112132 : Nat := 11373355604950225527767

theorem tailTrace_112132 : CollatzResearch.WordTrace tailWord_112132 prefixEnd_112132 11373355604950225527767 := by
  unfold tailWord_112132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2044895014886194733025325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2726526686514926310700433 2044895014886194733025325)
  ·
    refine ⟨766835630582323024884497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2044895014886194733025325 766835630582323024884497)
    ·
      refine ⟨575126722936742268663373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 766835630582323024884497 575126722936742268663373)
      ·
        refine ⟨215672521101278350748765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 575126722936742268663373 215672521101278350748765)
        ·
          refine ⟨80877195412979381530787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 215672521101278350748765 80877195412979381530787)
          ·
            refine ⟨121315793119469072296181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80877195412979381530787 121315793119469072296181)
            ·
              refine ⟨11373355604950225527767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121315793119469072296181 11373355604950225527767)
              ·
                rfl

theorem cell19_112132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 5].length) (baseStart_112132 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112132 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112132 prefixEnd_112132 := by exact prefixLift 112132
  have htrace : WordTrace (prefixWord ++ tailWord_112132) baseStart_112132 baseEnd_112132 := by
    simpa [prefixWord, tailWord_112132, baseEnd_112132] using wordTrace_append hprefix tailTrace_112132
  have hstable : (prefixWord ++ tailWord_112132).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112132).length < 2 ^ (prefixWord ++ tailWord_112132).sum := by decide
  have hdescent : baseEnd_112132 < baseStart_112132 := by decide
  rcases family_descends (prefixWord ++ tailWord_112132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112210 : List Nat := [3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_112210 : Nat := 118140960795 + 112210 * 2 ^ 59
def prefixEnd_112210 : Nat := 4983230072969 + 3 ^ 40 * 112210 * 2
def baseEnd_112210 : Nat := 34143801031769606849755

theorem tailTrace_112210 : CollatzResearch.WordTrace tailWord_112210 prefixEnd_112210 34143801031769606849755 := by
  unfold tailWord_112210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1023158730872452196847521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2728423282326539191593389 1023158730872452196847521)
  ·
    refine ⟨767369048154339147635641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1023158730872452196847521 767369048154339147635641)
    ·
      refine ⟨575526786115754360726731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 767369048154339147635641 575526786115754360726731)
      ·
        refine ⟨863290179173631541090097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 575526786115754360726731 863290179173631541090097)
        ·
          refine ⟨647467634380223655817573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 863290179173631541090097 647467634380223655817573)
          ·
            refine ⟨121400181446291935465795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 647467634380223655817573 121400181446291935465795)
            ·
              refine ⟨182100272169437903198693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121400181446291935465795 182100272169437903198693)
              ·
                refine ⟨34143801031769606849755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182100272169437903198693 34143801031769606849755)
                ·
                  rfl

theorem cell19_112210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_112210 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112210 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112210 prefixEnd_112210 := by exact prefixLift 112210
  have htrace : WordTrace (prefixWord ++ tailWord_112210) baseStart_112210 baseEnd_112210 := by
    simpa [prefixWord, tailWord_112210, baseEnd_112210] using wordTrace_append hprefix tailTrace_112210
  have hstable : (prefixWord ++ tailWord_112210).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112210).length < 2 ^ (prefixWord ++ tailWord_112210).sum := by decide
  have hdescent : baseEnd_112210 < baseStart_112210 := by decide
  rcases family_descends (prefixWord ++ tailWord_112210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112229 : List Nat := [1, 3, 1, 3, 3, 2, 3, 3]
def baseStart_112229 : Nat := 118140960795 + 112229 * 2 ^ 59
def prefixEnd_112229 : Nat := 4983230072969 + 3 ^ 40 * 112229 * 2
def baseEnd_112229 : Nat := 34149582443583192427481

theorem tailTrace_112229 : CollatzResearch.WordTrace tailWord_112229 prefixEnd_112229 34149582443583192427481 := by
  unfold tailWord_112229
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093327910420975032331741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2728885273613983354887827 4093327910420975032331741)
  ·
    refine ⟨1534997966407865637124403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4093327910420975032331741 1534997966407865637124403)
    ·
      refine ⟨2302496949611798455686605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1534997966407865637124403 2302496949611798455686605)
      ·
        refine ⟨863436356104424420882477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2302496949611798455686605 863436356104424420882477)
        ·
          refine ⟨323788633539159157830929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 863436356104424420882477 323788633539159157830929)
          ·
            refine ⟨242841475154369368373197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323788633539159157830929 242841475154369368373197)
            ·
              refine ⟨91065553182888513139949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 242841475154369368373197 91065553182888513139949)
              ·
                refine ⟨34149582443583192427481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91065553182888513139949 34149582443583192427481)
                ·
                  rfl

theorem cell19_112229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 3].length) (baseStart_112229 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112229 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112229 prefixEnd_112229 := by exact prefixLift 112229
  have htrace : WordTrace (prefixWord ++ tailWord_112229) baseStart_112229 baseEnd_112229 := by
    simpa [prefixWord, tailWord_112229, baseEnd_112229] using wordTrace_append hprefix tailTrace_112229
  have hstable : (prefixWord ++ tailWord_112229).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112229).length < 2 ^ (prefixWord ++ tailWord_112229).sum := by decide
  have hdescent : baseEnd_112229 < baseStart_112229 := by decide
  rcases family_descends (prefixWord ++ tailWord_112229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112233 : List Nat := [1, 2, 1, 1, 1, 4, 2, 7]
def baseStart_112233 : Nat := 118140960795 + 112233 * 2 ^ 59
def prefixEnd_112233 : Nat := 4983230072969 + 3 ^ 40 * 112233 * 2
def baseEnd_112233 : Nat := 34150799582912368338581

theorem tailTrace_112233 : CollatzResearch.WordTrace tailWord_112233 prefixEnd_112233 34150799582912368338581 := by
  unfold tailWord_112233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4093473802406483715477353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2728982534937655810318235 4093473802406483715477353)
  ·
    refine ⟨3070105351804862786608015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4093473802406483715477353 3070105351804862786608015)
    ·
      refine ⟨4605158027707294179912023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3070105351804862786608015 4605158027707294179912023)
      ·
        refine ⟨6907737041560941269868035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605158027707294179912023 6907737041560941269868035)
        ·
          refine ⟨10361605562341411904802053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907737041560941269868035 10361605562341411904802053)
          ·
            refine ⟨1942801042939014732150385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10361605562341411904802053 1942801042939014732150385)
            ·
              refine ⟨1457100782204261049112789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1942801042939014732150385 1457100782204261049112789)
              ·
                refine ⟨34150799582912368338581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1457100782204261049112789 34150799582912368338581)
                ·
                  rfl

theorem cell19_112233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_112233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112233 prefixEnd_112233 := by exact prefixLift 112233
  have htrace : WordTrace (prefixWord ++ tailWord_112233) baseStart_112233 baseEnd_112233 := by
    simpa [prefixWord, tailWord_112233, baseEnd_112233] using wordTrace_append hprefix tailTrace_112233
  have hstable : (prefixWord ++ tailWord_112233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112233).length < 2 ^ (prefixWord ++ tailWord_112233).sum := by decide
  have hdescent : baseEnd_112233 < baseStart_112233 := by decide
  rcases family_descends (prefixWord ++ tailWord_112233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112284 : List Nat := [2, 2, 3, 2, 3, 2, 2, 3]
def baseStart_112284 : Nat := 118140960795 + 112284 * 2 ^ 59
def prefixEnd_112284 : Nat := 4983230072969 + 3 ^ 40 * 112284 * 2
def baseEnd_112284 : Nat := 34166318109359361205109

theorem tailTrace_112284 : CollatzResearch.WordTrace tailWord_112284 prefixEnd_112284 34166318109359361205109 := by
  unfold tailWord_112284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047666962610859712791953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2730222616814479617055937 2047666962610859712791953)
  ·
    refine ⟨1535750221958144784593965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2047666962610859712791953 1535750221958144784593965)
    ·
      refine ⟨575906333234304294222737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1535750221958144784593965 575906333234304294222737)
      ·
        refine ⟨431929749925728220667053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 575906333234304294222737 431929749925728220667053)
        ·
          refine ⟨161973656222148082750145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 431929749925728220667053 161973656222148082750145)
          ·
            refine ⟨121480242166611062062609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 161973656222148082750145 121480242166611062062609)
            ·
              refine ⟨91110181624958296546957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 121480242166611062062609 91110181624958296546957)
              ·
                refine ⟨34166318109359361205109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91110181624958296546957 34166318109359361205109)
                ·
                  rfl

theorem cell19_112284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 3].length) (baseStart_112284 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112284 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112284 prefixEnd_112284 := by exact prefixLift 112284
  have htrace : WordTrace (prefixWord ++ tailWord_112284) baseStart_112284 baseEnd_112284 := by
    simpa [prefixWord, tailWord_112284, baseEnd_112284] using wordTrace_append hprefix tailTrace_112284
  have hstable : (prefixWord ++ tailWord_112284).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112284).length < 2 ^ (prefixWord ++ tailWord_112284).sum := by decide
  have hdescent : baseEnd_112284 < baseStart_112284 := by decide
  rcases family_descends (prefixWord ++ tailWord_112284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112286 : List Nat := [4, 3, 1, 1, 1, 3, 1, 5]
def baseStart_112286 : Nat := 118140960795 + 112286 * 2 ^ 59
def prefixEnd_112286 : Nat := 4983230072969 + 3 ^ 40 * 112286 * 2
def baseEnd_112286 : Nat := 34166926679023949160659

theorem tailTrace_112286 : CollatzResearch.WordTrace tailWord_112286 prefixEnd_112286 34166926679023949160659 := by
  unfold tailWord_112286
  simp only [CollatzResearch.WordTrace]
  refine ⟨511925858901809220894589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2730271247476315844771141 511925858901809220894589)
  ·
    refine ⟨191972197088178457835471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 511925858901809220894589 191972197088178457835471)
    ·
      refine ⟨287958295632267686753207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 191972197088178457835471 287958295632267686753207)
      ·
        refine ⟨431937443448401530129811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 287958295632267686753207 431937443448401530129811)
        ·
          refine ⟨647906165172602295194717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 431937443448401530129811 647906165172602295194717)
          ·
            refine ⟨242964811939725860698019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 647906165172602295194717 242964811939725860698019)
            ·
              refine ⟨364447217909588791047029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242964811939725860698019 364447217909588791047029)
              ·
                refine ⟨34166926679023949160659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364447217909588791047029 34166926679023949160659)
                ·
                  rfl

theorem cell19_112286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_112286 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112286 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112286 prefixEnd_112286 := by exact prefixLift 112286
  have htrace : WordTrace (prefixWord ++ tailWord_112286) baseStart_112286 baseEnd_112286 := by
    simpa [prefixWord, tailWord_112286, baseEnd_112286] using wordTrace_append hprefix tailTrace_112286
  have hstable : (prefixWord ++ tailWord_112286).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112286).length < 2 ^ (prefixWord ++ tailWord_112286).sum := by decide
  have hdescent : baseEnd_112286 < baseStart_112286 := by decide
  rcases family_descends (prefixWord ++ tailWord_112286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112288 : List Nat := [2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_112288 : Nat := 118140960795 + 112288 * 2 ^ 59
def prefixEnd_112288 : Nat := 4983230072969 + 3 ^ 40 * 112288 * 2
def baseEnd_112288 : Nat := 34167535248688537116209

theorem tailTrace_112288 : CollatzResearch.WordTrace tailWord_112288 prefixEnd_112288 34167535248688537116209 := by
  unfold tailWord_112288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2047739908603614054364759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2730319878138152072486345 2047739908603614054364759)
  ·
    refine ⟨3071609862905421081547139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2047739908603614054364759 3071609862905421081547139)
    ·
      refine ⟨4607414794358131622320709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3071609862905421081547139 4607414794358131622320709)
      ·
        refine ⟨863890273942149679185133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4607414794358131622320709 863890273942149679185133)
        ·
          refine ⟨323958852728306129694425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 863890273942149679185133 323958852728306129694425)
          ·
            refine ⟨242969139546229597270819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 323958852728306129694425 242969139546229597270819)
            ·
              refine ⟨364453709319344395906229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 242969139546229597270819 364453709319344395906229)
              ·
                refine ⟨34167535248688537116209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 364453709319344395906229 34167535248688537116209)
                ·
                  rfl

theorem cell19_112288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_112288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112288 prefixEnd_112288 := by exact prefixLift 112288
  have htrace : WordTrace (prefixWord ++ tailWord_112288) baseStart_112288 baseEnd_112288 := by
    simpa [prefixWord, tailWord_112288, baseEnd_112288] using wordTrace_append hprefix tailTrace_112288
  have hstable : (prefixWord ++ tailWord_112288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112288).length < 2 ^ (prefixWord ++ tailWord_112288).sum := by decide
  have hdescent : baseEnd_112288 < baseStart_112288 := by decide
  rcases family_descends (prefixWord ++ tailWord_112288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112476 : List Nat := [2, 2, 4, 2, 2, 2, 5]
def baseStart_112476 : Nat := 118140960795 + 112476 * 2 ^ 59
def prefixEnd_112476 : Nat := 4983230072969 + 3 ^ 40 * 112476 * 2
def baseEnd_112476 : Nat := 11408246932386601645973

theorem tailTrace_112476 : CollatzResearch.WordTrace tailWord_112476 prefixEnd_112476 11408246932386601645973 := by
  unfold tailWord_112476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051168370263068108286641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2734891160350757477715521 2051168370263068108286641)
  ·
    refine ⟨1538376277697301081214981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2051168370263068108286641 1538376277697301081214981)
    ·
      refine ⟨288445552068243952727809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1538376277697301081214981 288445552068243952727809)
      ·
        refine ⟨216334164051182964545857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 288445552068243952727809 216334164051182964545857)
        ·
          refine ⟨162250623038387223409393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 216334164051182964545857 162250623038387223409393)
          ·
            refine ⟨121687967278790417557045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 162250623038387223409393 121687967278790417557045)
            ·
              refine ⟨11408246932386601645973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 121687967278790417557045 11408246932386601645973)
              ·
                rfl

theorem cell19_112476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 5].length) (baseStart_112476 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112476 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112476 prefixEnd_112476 := by exact prefixLift 112476
  have htrace : WordTrace (prefixWord ++ tailWord_112476) baseStart_112476 baseEnd_112476 := by
    simpa [prefixWord, tailWord_112476, baseEnd_112476] using wordTrace_append hprefix tailTrace_112476
  have hstable : (prefixWord ++ tailWord_112476).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112476).length < 2 ^ (prefixWord ++ tailWord_112476).sum := by decide
  have hdescent : baseEnd_112476 < baseStart_112476 := by decide
  rcases family_descends (prefixWord ++ tailWord_112476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112480 : List Nat := [2, 1, 1, 3, 3, 2, 7]
def baseStart_112480 : Nat := 118140960795 + 112480 * 2 ^ 59
def prefixEnd_112480 : Nat := 4983230072969 + 3 ^ 40 * 112480 * 2
def baseEnd_112480 : Nat := 11408652645496326949673

theorem tailTrace_112480 : CollatzResearch.WordTrace tailWord_112480 prefixEnd_112480 11408652645496326949673 := by
  unfold tailWord_112480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2051241316255822449859447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2734988421674429933145929 2051241316255822449859447)
  ·
    refine ⟨3076861974383733674789171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2051241316255822449859447 3076861974383733674789171)
    ·
      refine ⟨4615292961575600512183757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3076861974383733674789171 4615292961575600512183757)
      ·
        refine ⟨1730734860590850192068909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4615292961575600512183757 1730734860590850192068909)
        ·
          refine ⟨649025572721568822025841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1730734860590850192068909 649025572721568822025841)
          ·
            refine ⟨486769179541176616519381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 649025572721568822025841 486769179541176616519381)
            ·
              refine ⟨11408652645496326949673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 486769179541176616519381 11408652645496326949673)
              ·
                rfl

theorem cell19_112480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_112480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112480 prefixEnd_112480 := by exact prefixLift 112480
  have htrace : WordTrace (prefixWord ++ tailWord_112480) baseStart_112480 baseEnd_112480 := by
    simpa [prefixWord, tailWord_112480, baseEnd_112480] using wordTrace_append hprefix tailTrace_112480
  have hstable : (prefixWord ++ tailWord_112480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112480).length < 2 ^ (prefixWord ++ tailWord_112480).sum := by decide
  have hdescent : baseEnd_112480 < baseStart_112480 := by decide
  rcases family_descends (prefixWord ++ tailWord_112480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112668 : List Nat := [2, 2, 3, 1, 3, 2, 2, 4]
def baseStart_112668 : Nat := 118140960795 + 112668 * 2 ^ 59
def prefixEnd_112668 : Nat := 4983230072969 + 3 ^ 40 * 112668 * 2
def baseEnd_112668 : Nat := 34283163484960248670729

theorem tailTrace_112668 : CollatzResearch.WordTrace tailWord_112668 prefixEnd_112668 34283163484960248670729 := by
  unfold tailWord_112668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2054669777915276503781329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2739559703887035338375105 2054669777915276503781329)
  ·
    refine ⟨1541002333436457377835997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2054669777915276503781329 1541002333436457377835997)
    ·
      refine ⟨577875875038671516688499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1541002333436457377835997 577875875038671516688499)
      ·
        refine ⟨866813812558007275032749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 577875875038671516688499 866813812558007275032749)
        ·
          refine ⟨325055179709252728137281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 866813812558007275032749 325055179709252728137281)
          ·
            refine ⟨243791384781939546102961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 325055179709252728137281 243791384781939546102961)
            ·
              refine ⟨182843538586454659577221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 243791384781939546102961 182843538586454659577221)
              ·
                refine ⟨34283163484960248670729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182843538586454659577221 34283163484960248670729)
                ·
                  rfl

theorem cell19_112668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_112668 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112668 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112668 prefixEnd_112668 := by exact prefixLift 112668
  have htrace : WordTrace (prefixWord ++ tailWord_112668) baseStart_112668 baseEnd_112668 := by
    simpa [prefixWord, tailWord_112668, baseEnd_112668] using wordTrace_append hprefix tailTrace_112668
  have hstable : (prefixWord ++ tailWord_112668).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112668).length < 2 ^ (prefixWord ++ tailWord_112668).sum := by decide
  have hdescent : baseEnd_112668 < baseStart_112668 := by decide
  rcases family_descends (prefixWord ++ tailWord_112668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112689 : List Nat := [1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_112689 : Nat := 118140960795 + 112689 * 2 ^ 59
def prefixEnd_112689 : Nat := 4983230072969 + 3 ^ 40 * 112689 * 2
def baseEnd_112689 : Nat := 34289553466438422204005

theorem tailTrace_112689 : CollatzResearch.WordTrace tailWord_112689 prefixEnd_112689 34289553466438422204005 := by
  unfold tailWord_112689
  simp only [CollatzResearch.WordTrace]
  refine ⟨4110105488754473594077121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2740070325836315729384747 4110105488754473594077121)
  ·
    refine ⟨3082579116565855195557841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4110105488754473594077121 3082579116565855195557841)
    ·
      refine ⟨2311934337424391396668381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3082579116565855195557841 2311934337424391396668381)
      ·
        refine ⟨866975376534146773750643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2311934337424391396668381 866975376534146773750643)
        ·
          refine ⟨1300463064801220160625965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 866975376534146773750643 1300463064801220160625965)
          ·
            refine ⟨487673649300457560234737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1300463064801220160625965 487673649300457560234737)
            ·
              refine ⟨365755236975343170176053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 487673649300457560234737 365755236975343170176053)
              ·
                refine ⟨34289553466438422204005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 365755236975343170176053 34289553466438422204005)
                ·
                  rfl

theorem cell19_112689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_112689 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112689 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112689 prefixEnd_112689 := by exact prefixLift 112689
  have htrace : WordTrace (prefixWord ++ tailWord_112689) baseStart_112689 baseEnd_112689 := by
    simpa [prefixWord, tailWord_112689, baseEnd_112689] using wordTrace_append hprefix tailTrace_112689
  have hstable : (prefixWord ++ tailWord_112689).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112689).length < 2 ^ (prefixWord ++ tailWord_112689).sum := by decide
  have hdescent : baseEnd_112689 < baseStart_112689 := by decide
  rcases family_descends (prefixWord ++ tailWord_112689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112725 : List Nat := [1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_112725 : Nat := 118140960795 + 112725 * 2 ^ 59
def prefixEnd_112725 : Nat := 4983230072969 + 3 ^ 40 * 112725 * 2
def baseEnd_112725 : Nat := 34300507720401005403907

theorem tailTrace_112725 : CollatzResearch.WordTrace tailWord_112725 prefixEnd_112725 34300507720401005403907 := by
  unfold tailWord_112725
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111418516624051742387629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2740945677749367828258419 4111418516624051742387629)
  ·
    refine ⟨1541781943734019403395361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4111418516624051742387629 1541781943734019403395361)
    ·
      refine ⟨1156336457800514552546521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1541781943734019403395361 1156336457800514552546521)
      ·
        refine ⟨867252343350385914409891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1156336457800514552546521 867252343350385914409891)
        ·
          refine ⟨1300878515025578871614837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 867252343350385914409891 1300878515025578871614837)
          ·
            refine ⟨121957360783648019213891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1300878515025578871614837 121957360783648019213891)
            ·
              refine ⟨182936041175472028820837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 121957360783648019213891 182936041175472028820837)
              ·
                refine ⟨34300507720401005403907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182936041175472028820837 34300507720401005403907)
                ·
                  rfl

theorem cell19_112725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_112725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112725 prefixEnd_112725 := by exact prefixLift 112725
  have htrace : WordTrace (prefixWord ++ tailWord_112725) baseStart_112725 baseEnd_112725 := by
    simpa [prefixWord, tailWord_112725, baseEnd_112725] using wordTrace_append hprefix tailTrace_112725
  have hstable : (prefixWord ++ tailWord_112725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112725).length < 2 ^ (prefixWord ++ tailWord_112725).sum := by decide
  have hdescent : baseEnd_112725 < baseStart_112725 := by decide
  rcases family_descends (prefixWord ++ tailWord_112725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112727 : List Nat := [1, 1, 3, 2, 2, 1, 5, 4]
def baseStart_112727 : Nat := 118140960795 + 112727 * 2 ^ 59
def prefixEnd_112727 : Nat := 4983230072969 + 3 ^ 40 * 112727 * 2
def baseEnd_112727 : Nat := 34301116290065593359457

theorem tailTrace_112727 : CollatzResearch.WordTrace tailWord_112727 prefixEnd_112727 34301116290065593359457 := by
  unfold tailWord_112727
  simp only [CollatzResearch.WordTrace]
  refine ⟨4111491462616806083960435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2740994308411204055973623 4111491462616806083960435)
  ·
    refine ⟨6167237193925209125940653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4111491462616806083960435 6167237193925209125940653)
    ·
      refine ⟨2312713947721953422227745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6167237193925209125940653 2312713947721953422227745)
      ·
        refine ⟨1734535460791465066670809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2312713947721953422227745 1734535460791465066670809)
        ·
          refine ⟨1300901595593598800003107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1734535460791465066670809 1300901595593598800003107)
          ·
            refine ⟨1951352393390398200004661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1300901595593598800003107 1951352393390398200004661)
            ·
              refine ⟨182939286880349831250437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1951352393390398200004661 182939286880349831250437)
              ·
                refine ⟨34301116290065593359457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 182939286880349831250437 34301116290065593359457)
                ·
                  rfl

theorem cell19_112727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_112727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112727 prefixEnd_112727 := by exact prefixLift 112727
  have htrace : WordTrace (prefixWord ++ tailWord_112727) baseStart_112727 baseEnd_112727 := by
    simpa [prefixWord, tailWord_112727, baseEnd_112727] using wordTrace_append hprefix tailTrace_112727
  have hstable : (prefixWord ++ tailWord_112727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112727).length < 2 ^ (prefixWord ++ tailWord_112727).sum := by decide
  have hdescent : baseEnd_112727 < baseStart_112727 := by decide
  rcases family_descends (prefixWord ++ tailWord_112727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112765 : List Nat := [1, 4, 1, 1, 3, 3, 6]
def baseStart_112765 : Nat := 118140960795 + 112765 * 2 ^ 59
def prefixEnd_112765 : Nat := 4983230072969 + 3 ^ 40 * 112765 * 2
def baseEnd_112765 : Nat := 11437559704564254838303

theorem tailTrace_112765 : CollatzResearch.WordTrace tailWord_112765 prefixEnd_112765 11437559704564254838303 := by
  unfold tailWord_112765
  simp only [CollatzResearch.WordTrace]
  refine ⟨4112877436479138573843749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2741918290986092382562499 4112877436479138573843749)
  ·
    refine ⟨771164519339838482595703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4112877436479138573843749 771164519339838482595703)
    ·
      refine ⟨1156746779009757723893555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 771164519339838482595703 1156746779009757723893555)
      ·
        refine ⟨1735120168514636585840333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1156746779009757723893555 1735120168514636585840333)
        ·
          refine ⟨650670063192988719690125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1735120168514636585840333 650670063192988719690125)
          ·
            refine ⟨244001273697370769883797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 650670063192988719690125 244001273697370769883797)
            ·
              refine ⟨11437559704564254838303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 244001273697370769883797 11437559704564254838303)
              ·
                rfl

theorem cell19_112765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_112765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112765 prefixEnd_112765 := by exact prefixLift 112765
  have htrace : WordTrace (prefixWord ++ tailWord_112765) baseStart_112765 baseEnd_112765 := by
    simpa [prefixWord, tailWord_112765, baseEnd_112765] using wordTrace_append hprefix tailTrace_112765
  have hstable : (prefixWord ++ tailWord_112765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112765).length < 2 ^ (prefixWord ++ tailWord_112765).sum := by decide
  have hdescent : baseEnd_112765 < baseStart_112765 := by decide
  rcases family_descends (prefixWord ++ tailWord_112765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112799 : List Nat := [1, 1, 2, 6, 1, 3, 2, 3]
def baseStart_112799 : Nat := 118140960795 + 112799 * 2 ^ 59
def prefixEnd_112799 : Nat := 4983230072969 + 3 ^ 40 * 112799 * 2
def baseEnd_112799 : Nat := 34323024797990759759261

theorem tailTrace_112799 : CollatzResearch.WordTrace tailWord_112799 prefixEnd_112799 34323024797990759759261 := by
  unfold tailWord_112799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114117518355962380581451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742745012237308253720967 4114117518355962380581451)
  ·
    refine ⟨6171176277533943570872177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4114117518355962380581451 6171176277533943570872177)
    ·
      refine ⟨4628382208150457678154133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6171176277533943570872177 4628382208150457678154133)
      ·
        refine ⟨216955416007052703663475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4628382208150457678154133 216955416007052703663475)
        ·
          refine ⟨325433124010579055495213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 216955416007052703663475 325433124010579055495213)
          ·
            refine ⟨122037421503967145810705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 325433124010579055495213 122037421503967145810705)
            ·
              refine ⟨91528066127975359358029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122037421503967145810705 91528066127975359358029)
              ·
                refine ⟨34323024797990759759261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91528066127975359358029 34323024797990759759261)
                ·
                  rfl

theorem cell19_112799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 2, 3].length) (baseStart_112799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112799 prefixEnd_112799 := by exact prefixLift 112799
  have htrace : WordTrace (prefixWord ++ tailWord_112799) baseStart_112799 baseEnd_112799 := by
    simpa [prefixWord, tailWord_112799, baseEnd_112799] using wordTrace_append hprefix tailTrace_112799
  have hstable : (prefixWord ++ tailWord_112799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112799).length < 2 ^ (prefixWord ++ tailWord_112799).sum := by decide
  have hdescent : baseEnd_112799 < baseStart_112799 := by decide
  rcases family_descends (prefixWord ++ tailWord_112799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112801 : List Nat := [1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_112801 : Nat := 118140960795 + 112801 * 2 ^ 59
def prefixEnd_112801 : Nat := 4983230072969 + 3 ^ 40 * 112801 * 2
def baseEnd_112801 : Nat := 34323633367655347714811

theorem tailTrace_112801 : CollatzResearch.WordTrace tailWord_112801 prefixEnd_112801 34323633367655347714811 := by
  unfold tailWord_112801
  simp only [CollatzResearch.WordTrace]
  refine ⟨4114190464348716722154257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2742793642899144481436171 4114190464348716722154257)
  ·
    refine ⟨3085642848261537541615693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4114190464348716722154257 3085642848261537541615693)
    ·
      refine ⟨1157116068098076578105885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3085642848261537541615693 1157116068098076578105885)
      ·
        refine ⟨433918525536778716789707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1157116068098076578105885 433918525536778716789707)
        ·
          refine ⟨650877788305168075184561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 433918525536778716789707 650877788305168075184561)
          ·
            refine ⟨488158341228876056388421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 650877788305168075184561 488158341228876056388421)
            ·
              refine ⟨91529688980414260572829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 488158341228876056388421 91529688980414260572829)
              ·
                refine ⟨34323633367655347714811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91529688980414260572829 34323633367655347714811)
                ·
                  rfl

theorem cell19_112801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_112801 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112801 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112801 prefixEnd_112801 := by exact prefixLift 112801
  have htrace : WordTrace (prefixWord ++ tailWord_112801) baseStart_112801 baseEnd_112801 := by
    simpa [prefixWord, tailWord_112801, baseEnd_112801] using wordTrace_append hprefix tailTrace_112801
  have hstable : (prefixWord ++ tailWord_112801).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112801).length < 2 ^ (prefixWord ++ tailWord_112801).sum := by decide
  have hdescent : baseEnd_112801 < baseStart_112801 := by decide
  rcases family_descends (prefixWord ++ tailWord_112801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_112877 : List Nat := [1, 5, 1, 2, 4, 6]
def baseStart_112877 : Nat := 118140960795 + 112877 * 2 ^ 59
def prefixEnd_112877 : Nat := 4983230072969 + 3 ^ 40 * 112877 * 2
def baseEnd_112877 : Nat := 3816306557212187780635

theorem tailTrace_112877 : CollatzResearch.WordTrace tailWord_112877 prefixEnd_112877 3816306557212187780635 := by
  unfold tailWord_112877
  simp only [CollatzResearch.WordTrace]
  refine ⟨4116962412073381701920885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2744641608048921134613923 4116962412073381701920885)
  ·
    refine ⟨385965226131879534555083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4116962412073381701920885 385965226131879534555083)
    ·
      refine ⟨578947839197819301832625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 385965226131879534555083 578947839197819301832625)
      ·
        refine ⟨434210879398364476374469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 578947839197819301832625 434210879398364476374469)
        ·
          refine ⟨81414539887193339320213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 434210879398364476374469 81414539887193339320213)
          ·
            refine ⟨3816306557212187780635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 81414539887193339320213 3816306557212187780635)
            ·
              rfl

theorem cell19_112877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 6].length) (baseStart_112877 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_112877 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_112877 prefixEnd_112877 := by exact prefixLift 112877
  have htrace : WordTrace (prefixWord ++ tailWord_112877) baseStart_112877 baseEnd_112877 := by
    simpa [prefixWord, tailWord_112877, baseEnd_112877] using wordTrace_append hprefix tailTrace_112877
  have hstable : (prefixWord ++ tailWord_112877).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_112877).length < 2 ^ (prefixWord ++ tailWord_112877).sum := by decide
  have hdescent : baseEnd_112877 < baseStart_112877 := by decide
  rcases family_descends (prefixWord ++ tailWord_112877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113046 : List Nat := [5, 3, 1, 2, 8]
def baseStart_113046 : Nat := 118140960795 + 113046 * 2 ^ 59
def prefixEnd_113046 : Nat := 4983230072969 + 3 ^ 40 * 113046 * 2
def baseEnd_113046 : Nat := 1274006783391384158137

theorem tailTrace_113046 : CollatzResearch.WordTrace tailWord_113046 prefixEnd_113046 1274006783391384158137 := by
  unfold tailWord_113046
  simp only [CollatzResearch.WordTrace]
  refine ⟨257695396778820222801437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2748750898974082376548661 257695396778820222801437)
  ·
    refine ⟨96635773792057583550539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 257695396778820222801437 96635773792057583550539)
    ·
      refine ⟨144953660688086375325809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96635773792057583550539 144953660688086375325809)
      ·
        refine ⟨108715245516064781494357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 144953660688086375325809 108715245516064781494357)
        ·
          refine ⟨1274006783391384158137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 108715245516064781494357 1274006783391384158137)
          ·
            rfl

theorem cell19_113046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_113046 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113046 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113046 prefixEnd_113046 := by exact prefixLift 113046
  have htrace : WordTrace (prefixWord ++ tailWord_113046) baseStart_113046 baseEnd_113046 := by
    simpa [prefixWord, tailWord_113046, baseEnd_113046] using wordTrace_append hprefix tailTrace_113046
  have hstable : (prefixWord ++ tailWord_113046).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113046).length < 2 ^ (prefixWord ++ tailWord_113046).sum := by decide
  have hdescent : baseEnd_113046 < baseStart_113046 := by decide
  rcases family_descends (prefixWord ++ tailWord_113046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113052 : List Nat := [2, 2, 3, 12]
def baseStart_113052 : Nat := 118140960795 + 113052 * 2 ^ 59
def prefixEnd_113052 : Nat := 4983230072969 + 3 ^ 40 * 113052 * 2
def baseEnd_113052 : Nat := 424691467414335014029

theorem tailTrace_113052 : CollatzResearch.WordTrace tailWord_113052 prefixEnd_113052 424691467414335014029 := by
  unfold tailWord_113052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2061672593219693294770705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2748896790959591059694273 2061672593219693294770705)
  ·
    refine ⟨1546254444914769971078029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2061672593219693294770705 1546254444914769971078029)
    ·
      refine ⟨579845416843038739154261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1546254444914769971078029 579845416843038739154261)
      ·
        refine ⟨424691467414335014029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 579845416843038739154261 424691467414335014029)
        ·
          rfl

theorem cell19_113052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 12].length) (baseStart_113052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113052 prefixEnd_113052 := by exact prefixLift 113052
  have htrace : WordTrace (prefixWord ++ tailWord_113052) baseStart_113052 baseEnd_113052 := by
    simpa [prefixWord, tailWord_113052, baseEnd_113052] using wordTrace_append hprefix tailTrace_113052
  have hstable : (prefixWord ++ tailWord_113052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113052).length < 2 ^ (prefixWord ++ tailWord_113052).sum := by decide
  have hdescent : baseEnd_113052 < baseStart_113052 := by decide
  rcases family_descends (prefixWord ++ tailWord_113052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113145 : List Nat := [1, 2, 1, 3, 1, 2, 6, 3]
def baseStart_113145 : Nat := 118140960795 + 113145 * 2 ^ 59
def prefixEnd_113145 : Nat := 4983230072969 + 3 ^ 40 * 113145 * 2
def baseEnd_113145 : Nat := 34428307349964476069429

theorem tailTrace_113145 : CollatzResearch.WordTrace tailWord_113145 prefixEnd_113145 34428307349964476069429 := by
  unfold tailWord_113145
  simp only [CollatzResearch.WordTrace]
  refine ⟨4126737175102463472676889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2751158116734975648451259 4126737175102463472676889)
  ·
    refine ⟨3095052881326847604507667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4126737175102463472676889 3095052881326847604507667)
    ·
      refine ⟨4642579321990271406761501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3095052881326847604507667 4642579321990271406761501)
      ·
        refine ⟨1740967245746351777535563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4642579321990271406761501 1740967245746351777535563)
        ·
          refine ⟨2611450868619527666303345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1740967245746351777535563 2611450868619527666303345)
          ·
            refine ⟨1958588151464645749727509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2611450868619527666303345 1958588151464645749727509)
            ·
              refine ⟨91808819599905269518477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1958588151464645749727509 91808819599905269518477)
              ·
                refine ⟨34428307349964476069429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91808819599905269518477 34428307349964476069429)
                ·
                  rfl

theorem cell19_113145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 3].length) (baseStart_113145 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113145 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113145 prefixEnd_113145 := by exact prefixLift 113145
  have htrace : WordTrace (prefixWord ++ tailWord_113145) baseStart_113145 baseEnd_113145 := by
    simpa [prefixWord, tailWord_113145, baseEnd_113145] using wordTrace_append hprefix tailTrace_113145
  have hstable : (prefixWord ++ tailWord_113145).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113145).length < 2 ^ (prefixWord ++ tailWord_113145).sum := by decide
  have hdescent : baseEnd_113145 < baseStart_113145 := by decide
  rcases family_descends (prefixWord ++ tailWord_113145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113158 : List Nat := [6, 2, 1, 1, 1, 3, 5]
def baseStart_113158 : Nat := 118140960795 + 113158 * 2 ^ 59
def prefixEnd_113158 : Nat := 4983230072969 + 3 ^ 40 * 113158 * 2
def baseEnd_113158 : Nat := 11477421017594765926835

theorem tailTrace_113158 : CollatzResearch.WordTrace tailWord_113158 prefixEnd_113158 11477421017594765926835 := by
  unfold tailWord_113158
  simp only [CollatzResearch.WordTrace]
  refine ⟨128975353876730209153129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2751474216036911128600085 128975353876730209153129)
  ·
    refine ⟨96731515407547656864847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 128975353876730209153129 96731515407547656864847)
    ·
      refine ⟨145097273111321485297271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 96731515407547656864847 145097273111321485297271)
      ·
        refine ⟨217645909666982227945907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145097273111321485297271 217645909666982227945907)
        ·
          refine ⟨326468864500473341918861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 217645909666982227945907 326468864500473341918861)
          ·
            refine ⟨122425824187677503219573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326468864500473341918861 122425824187677503219573)
            ·
              refine ⟨11477421017594765926835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122425824187677503219573 11477421017594765926835)
              ·
                rfl

theorem cell19_113158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_113158 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113158 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113158 prefixEnd_113158 := by exact prefixLift 113158
  have htrace : WordTrace (prefixWord ++ tailWord_113158) baseStart_113158 baseEnd_113158 := by
    simpa [prefixWord, tailWord_113158, baseEnd_113158] using wordTrace_append hprefix tailTrace_113158
  have hstable : (prefixWord ++ tailWord_113158).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113158).length < 2 ^ (prefixWord ++ tailWord_113158).sum := by decide
  have hdescent : baseEnd_113158 < baseStart_113158 := by decide
  rcases family_descends (prefixWord ++ tailWord_113158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113164 : List Nat := [2, 2, 1, 2, 4, 3, 5]
def baseStart_113164 : Nat := 118140960795 + 113164 * 2 ^ 59
def prefixEnd_113164 : Nat := 4983230072969 + 3 ^ 40 * 113164 * 2
def baseEnd_113164 : Nat := 11478029587259353882385

theorem tailTrace_113164 : CollatzResearch.WordTrace tailWord_113164 prefixEnd_113164 11478029587259353882385 := by
  unfold tailWord_113164
  simp only [CollatzResearch.WordTrace]
  refine ⟨2063715081016814858809273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2751620108022419811745697 2063715081016814858809273)
  ·
    refine ⟨1547786310762611144106955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2063715081016814858809273 1547786310762611144106955)
    ·
      refine ⟨2321679466143916716160433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1547786310762611144106955 2321679466143916716160433)
      ·
        refine ⟨1741259599607937537120325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2321679466143916716160433 1741259599607937537120325)
        ·
          refine ⟨326486174926488288210061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1741259599607937537120325 326486174926488288210061)
          ·
            refine ⟨122432315597433108078773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 326486174926488288210061 122432315597433108078773)
            ·
              refine ⟨11478029587259353882385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122432315597433108078773 11478029587259353882385)
              ·
                rfl

theorem cell19_113164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_113164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113164 prefixEnd_113164 := by exact prefixLift 113164
  have htrace : WordTrace (prefixWord ++ tailWord_113164) baseStart_113164 baseEnd_113164 := by
    simpa [prefixWord, tailWord_113164, baseEnd_113164] using wordTrace_append hprefix tailTrace_113164
  have hstable : (prefixWord ++ tailWord_113164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113164).length < 2 ^ (prefixWord ++ tailWord_113164).sum := by decide
  have hdescent : baseEnd_113164 < baseStart_113164 := by decide
  rcases family_descends (prefixWord ++ tailWord_113164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113223 : List Nat := [1, 1, 4, 1, 4, 8]
def baseStart_113223 : Nat := 118140960795 + 113223 * 2 ^ 59
def prefixEnd_113223 : Nat := 4983230072969 + 3 ^ 40 * 113223 * 2
def baseEnd_113223 : Nat := 3828004618542600703987

theorem tailTrace_113223 : CollatzResearch.WordTrace tailWord_113223 prefixEnd_113223 3828004618542600703987 := by
  unfold tailWord_113223
  simp only [CollatzResearch.WordTrace]
  refine ⟨4129582068819882794016323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2753054712546588529344215 4129582068819882794016323)
  ·
    refine ⟨6194373103229824191024485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4129582068819882794016323 6194373103229824191024485)
    ·
      refine ⟨1161444956855592035817091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6194373103229824191024485 1161444956855592035817091)
      ·
        refine ⟨1742167435283388053725637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1161444956855592035817091 1742167435283388053725637)
        ·
          refine ⟨326656394115635260073557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1742167435283388053725637 326656394115635260073557)
          ·
            refine ⟨3828004618542600703987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 326656394115635260073557 3828004618542600703987)
            ·
              rfl

theorem cell19_113223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 8].length) (baseStart_113223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113223 prefixEnd_113223 := by exact prefixLift 113223
  have htrace : WordTrace (prefixWord ++ tailWord_113223) baseStart_113223 baseEnd_113223 := by
    simpa [prefixWord, tailWord_113223, baseEnd_113223] using wordTrace_append hprefix tailTrace_113223
  have hstable : (prefixWord ++ tailWord_113223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113223).length < 2 ^ (prefixWord ++ tailWord_113223).sum := by decide
  have hdescent : baseEnd_113223 < baseStart_113223 := by decide
  rcases family_descends (prefixWord ++ tailWord_113223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113280 : List Nat := [2, 1, 1, 2, 1, 6, 6]
def baseStart_113280 : Nat := 118140960795 + 113280 * 2 ^ 59
def prefixEnd_113280 : Nat := 4983230072969 + 3 ^ 40 * 113280 * 2
def baseEnd_113280 : Nat := 11489795267441387689687

theorem tailTrace_113280 : CollatzResearch.WordTrace tailWord_113280 prefixEnd_113280 11489795267441387689687 := by
  unfold tailWord_113280
  simp only [CollatzResearch.WordTrace]
  refine ⟨2065830514806690764420647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2754440686408921019227529 2065830514806690764420647)
  ·
    refine ⟨3098745772210036146630971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2065830514806690764420647 3098745772210036146630971)
    ·
      refine ⟨4648118658315054219946457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3098745772210036146630971 4648118658315054219946457)
      ·
        refine ⟨3486088993736290664959843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4648118658315054219946457 3486088993736290664959843)
        ·
          refine ⟨5229133490604435997439765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486088993736290664959843 5229133490604435997439765)
          ·
            refine ⟨245115632372082937379989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5229133490604435997439765 245115632372082937379989)
            ·
              refine ⟨11489795267441387689687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 245115632372082937379989 11489795267441387689687)
              ·
                rfl

theorem cell19_113280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 6].length) (baseStart_113280 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113280 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113280 prefixEnd_113280 := by exact prefixLift 113280
  have htrace : WordTrace (prefixWord ++ tailWord_113280) baseStart_113280 baseEnd_113280 := by
    simpa [prefixWord, tailWord_113280, baseEnd_113280] using wordTrace_append hprefix tailTrace_113280
  have hstable : (prefixWord ++ tailWord_113280).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113280).length < 2 ^ (prefixWord ++ tailWord_113280).sum := by decide
  have hdescent : baseEnd_113280 < baseStart_113280 := by decide
  rcases family_descends (prefixWord ++ tailWord_113280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113312 : List Nat := [2, 1, 1, 4, 5, 1, 2, 3]
def baseStart_113312 : Nat := 118140960795 + 113312 * 2 ^ 59
def prefixEnd_113312 : Nat := 4983230072969 + 3 ^ 40 * 113312 * 2
def baseEnd_113312 : Nat := 34479122916957570357863

theorem tailTrace_113312 : CollatzResearch.WordTrace tailWord_113312 prefixEnd_113312 34479122916957570357863 := by
  unfold tailWord_113312
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066414082748725497003095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2755218776998300662670793 2066414082748725497003095)
  ·
    refine ⟨3099621124123088245504643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066414082748725497003095 3099621124123088245504643)
    ·
      refine ⟨4649431686184632368256965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099621124123088245504643 4649431686184632368256965)
      ·
        refine ⟨871768441159618569048181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4649431686184632368256965 871768441159618569048181)
        ·
          refine ⟨81728291358714240848267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 871768441159618569048181 81728291358714240848267)
          ·
            refine ⟨122592437038071361272401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 81728291358714240848267 122592437038071361272401)
            ·
              refine ⟨91944327778553520954301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 122592437038071361272401 91944327778553520954301)
              ·
                refine ⟨34479122916957570357863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 91944327778553520954301 34479122916957570357863)
                ·
                  rfl

theorem cell19_113312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_113312 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113312 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113312 prefixEnd_113312 := by exact prefixLift 113312
  have htrace : WordTrace (prefixWord ++ tailWord_113312) baseStart_113312 baseEnd_113312 := by
    simpa [prefixWord, tailWord_113312, baseEnd_113312] using wordTrace_append hprefix tailTrace_113312
  have hstable : (prefixWord ++ tailWord_113312).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113312).length < 2 ^ (prefixWord ++ tailWord_113312).sum := by decide
  have hdescent : baseEnd_113312 < baseStart_113312 := by decide
  rcases family_descends (prefixWord ++ tailWord_113312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113335 : List Nat := [1, 1, 3, 1, 6, 2, 5]
def baseStart_113335 : Nat := 118140960795 + 113335 * 2 ^ 59
def prefixEnd_113335 : Nat := 4983230072969 + 3 ^ 40 * 113335 * 2
def baseEnd_113335 : Nat := 11495373822700110615563

theorem tailTrace_113335 : CollatzResearch.WordTrace tailWord_113335 prefixEnd_113335 11495373822700110615563 := by
  unfold tailWord_113335
  simp only [CollatzResearch.WordTrace]
  refine ⟨4133667044414125922093459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2755778029609417281395639 4133667044414125922093459)
  ·
    refine ⟨6200500566621188883140189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4133667044414125922093459 6200500566621188883140189)
    ·
      refine ⟨2325187712482945831177571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6200500566621188883140189 2325187712482945831177571)
      ·
        refine ⟨3487781568724418746766357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2325187712482945831177571 3487781568724418746766357)
        ·
          refine ⟨163489761033957128754673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3487781568724418746766357 163489761033957128754673)
          ·
            refine ⟨122617320775467846566005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 163489761033957128754673 122617320775467846566005)
            ·
              refine ⟨11495373822700110615563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 122617320775467846566005 11495373822700110615563)
              ·
                rfl

theorem cell19_113335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_113335 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113335 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113335 prefixEnd_113335 := by exact prefixLift 113335
  have htrace : WordTrace (prefixWord ++ tailWord_113335) baseStart_113335 baseEnd_113335 := by
    simpa [prefixWord, tailWord_113335, baseEnd_113335] using wordTrace_append hprefix tailTrace_113335
  have hstable : (prefixWord ++ tailWord_113335).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113335).length < 2 ^ (prefixWord ++ tailWord_113335).sum := by decide
  have hdescent : baseEnd_113335 < baseStart_113335 := by decide
  rcases family_descends (prefixWord ++ tailWord_113335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113354 : List Nat := [3, 1, 2, 1, 4, 2, 2, 4]
def baseStart_113354 : Nat := 118140960795 + 113354 * 2 ^ 59
def prefixEnd_113354 : Nat := 4983230072969 + 3 ^ 40 * 113354 * 2
def baseEnd_113354 : Nat := 34491902879913917424415

theorem tailTrace_113354 : CollatzResearch.WordTrace tailWord_113354 prefixEnd_113354 34491902879913917424415 := by
  unfold tailWord_113354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033590007836323041758779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2756240020896861444690077 1033590007836323041758779)
  ·
    refine ⟨1550385011754484562638169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1033590007836323041758779 1550385011754484562638169)
    ·
      refine ⟨1162788758815863421978627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1550385011754484562638169 1162788758815863421978627)
      ·
        refine ⟨1744183138223795132967941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1162788758815863421978627 1744183138223795132967941)
        ·
          refine ⟨327034338416961587431489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1744183138223795132967941 327034338416961587431489)
          ·
            refine ⟨245275753812721190573617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 327034338416961587431489 245275753812721190573617)
            ·
              refine ⟨183956815359540892930213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245275753812721190573617 183956815359540892930213)
              ·
                refine ⟨34491902879913917424415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 183956815359540892930213 34491902879913917424415)
                ·
                  rfl

theorem cell19_113354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_113354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113354 prefixEnd_113354 := by exact prefixLift 113354
  have htrace : WordTrace (prefixWord ++ tailWord_113354) baseStart_113354 baseEnd_113354 := by
    simpa [prefixWord, tailWord_113354, baseEnd_113354] using wordTrace_append hprefix tailTrace_113354
  have hstable : (prefixWord ++ tailWord_113354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113354).length < 2 ^ (prefixWord ++ tailWord_113354).sum := by decide
  have hdescent : baseEnd_113354 < baseStart_113354 := by decide
  rcases family_descends (prefixWord ++ tailWord_113354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113375 : List Nat := [1, 1, 2, 3, 2, 3, 2, 5]
def baseStart_113375 : Nat := 118140960795 + 113375 * 2 ^ 59
def prefixEnd_113375 : Nat := 4983230072969 + 3 ^ 40 * 113375 * 2
def baseEnd_113375 : Nat := 34498292861392090957691

theorem tailTrace_113375 : CollatzResearch.WordTrace tailWord_113375 prefixEnd_113375 34498292861392090957691 := by
  unfold tailWord_113375
  simp only [CollatzResearch.WordTrace]
  refine ⟨4135125964269212753549579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2756750642846141835699719 4135125964269212753549579)
  ·
    refine ⟨6202688946403819130324369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4135125964269212753549579 6202688946403819130324369)
    ·
      refine ⟨4652016709802864347743277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6202688946403819130324369 4652016709802864347743277)
      ·
        refine ⟨1744506266176074130403729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4652016709802864347743277 1744506266176074130403729)
        ·
          refine ⟨1308379699632055597802797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744506266176074130403729 1308379699632055597802797)
          ·
            refine ⟨490642387362020849176049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1308379699632055597802797 490642387362020849176049)
            ·
              refine ⟨367981790521515636882037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 490642387362020849176049 367981790521515636882037)
              ·
                refine ⟨34498292861392090957691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 367981790521515636882037 34498292861392090957691)
                ·
                  rfl

theorem cell19_113375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_113375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113375 prefixEnd_113375 := by exact prefixLift 113375
  have htrace : WordTrace (prefixWord ++ tailWord_113375) baseStart_113375 baseEnd_113375 := by
    simpa [prefixWord, tailWord_113375, baseEnd_113375] using wordTrace_append hprefix tailTrace_113375
  have hstable : (prefixWord ++ tailWord_113375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113375).length < 2 ^ (prefixWord ++ tailWord_113375).sum := by decide
  have hdescent : baseEnd_113375 < baseStart_113375 := by decide
  rcases family_descends (prefixWord ++ tailWord_113375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113394 : List Nat := [3, 2, 1, 3, 1, 9]
def baseStart_113394 : Nat := 118140960795 + 113394 * 2 ^ 59
def prefixEnd_113394 : Nat := 4983230072969 + 3 ^ 40 * 113394 * 2
def baseEnd_113394 : Nat := 3833786030356186281713

theorem tailTrace_113394 : CollatzResearch.WordTrace tailWord_113394 prefixEnd_113394 3833786030356186281713 := by
  unfold tailWord_113394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1033954737800094749622809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2757212634133585998994157 1033954737800094749622809)
  ·
    refine ⟨775466053350071062217107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1033954737800094749622809 775466053350071062217107)
    ·
      refine ⟨1163199080025106593325661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 775466053350071062217107 1163199080025106593325661)
      ·
        refine ⟨436199655009414972497123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1163199080025106593325661 436199655009414972497123)
        ·
          refine ⟨654299482514122458745685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436199655009414972497123 654299482514122458745685)
          ·
            refine ⟨3833786030356186281713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 654299482514122458745685 3833786030356186281713)
            ·
              rfl

theorem cell19_113394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 9].length) (baseStart_113394 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113394 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113394 prefixEnd_113394 := by exact prefixLift 113394
  have htrace : WordTrace (prefixWord ++ tailWord_113394) baseStart_113394 baseEnd_113394 := by
    simpa [prefixWord, tailWord_113394, baseEnd_113394] using wordTrace_append hprefix tailTrace_113394
  have hstable : (prefixWord ++ tailWord_113394).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113394).length < 2 ^ (prefixWord ++ tailWord_113394).sum := by decide
  have hdescent : baseEnd_113394 < baseStart_113394 := by decide
  rcases family_descends (prefixWord ++ tailWord_113394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113426 : List Nat := [3, 2, 4, 1, 2, 1, 3, 3]
def baseStart_113426 : Nat := 118140960795 + 113426 * 2 ^ 59
def prefixEnd_113426 : Nat := 4983230072969 + 3 ^ 40 * 113426 * 2
def baseEnd_113426 : Nat := 34513811387839083824219

theorem tailTrace_113426 : CollatzResearch.WordTrace tailWord_113426 prefixEnd_113426 34513811387839083824219 := by
  unfold tailWord_113426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1034246521771112115914033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2757990724722965642437421 1034246521771112115914033)
  ·
    refine ⟨775684891328334086935525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1034246521771112115914033 775684891328334086935525)
    ·
      refine ⟨145440917124062641300411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 775684891328334086935525 145440917124062641300411)
      ·
        refine ⟨218161375686093961950617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 145440917124062641300411 218161375686093961950617)
        ·
          refine ⟨163621031764570471462963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218161375686093961950617 163621031764570471462963)
          ·
            refine ⟨245431547646855707194445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163621031764570471462963 245431547646855707194445)
            ·
              refine ⟨92036830367570890197917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 245431547646855707194445 92036830367570890197917)
              ·
                refine ⟨34513811387839083824219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92036830367570890197917 34513811387839083824219)
                ·
                  rfl

theorem cell19_113426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_113426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113426 prefixEnd_113426 := by exact prefixLift 113426
  have htrace : WordTrace (prefixWord ++ tailWord_113426) baseStart_113426 baseEnd_113426 := by
    simpa [prefixWord, tailWord_113426, baseEnd_113426] using wordTrace_append hprefix tailTrace_113426
  have hstable : (prefixWord ++ tailWord_113426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113426).length < 2 ^ (prefixWord ++ tailWord_113426).sum := by decide
  have hdescent : baseEnd_113426 < baseStart_113426 := by decide
  rcases family_descends (prefixWord ++ tailWord_113426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113485 : List Nat := [1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_113485 : Nat := 118140960795 + 113485 * 2 ^ 59
def prefixEnd_113485 : Nat := 4983230072969 + 3 ^ 40 * 113485 * 2
def baseEnd_113485 : Nat := 34531764192944428512947

theorem tailTrace_113485 : CollatzResearch.WordTrace tailWord_113485 prefixEnd_113485 34531764192944428512947 := by
  unfold tailWord_113485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139137993870701540053909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2759425329247134360035939 4139137993870701540053909)
  ·
    refine ⟨194022093462689134690027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4139137993870701540053909 194022093462689134690027)
    ·
      refine ⟨291033140194033702035041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194022093462689134690027 291033140194033702035041)
      ·
        refine ⟨218274855145525276526281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 291033140194033702035041 218274855145525276526281)
        ·
          refine ⟨163706141359143957394711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 218274855145525276526281 163706141359143957394711)
          ·
            refine ⟨245559212038715936092067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163706141359143957394711 245559212038715936092067)
            ·
              refine ⟨368338818058073904138101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245559212038715936092067 368338818058073904138101)
              ·
                refine ⟨34531764192944428512947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368338818058073904138101 34531764192944428512947)
                ·
                  rfl

theorem cell19_113485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_113485 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113485 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113485 prefixEnd_113485 := by exact prefixLift 113485
  have htrace : WordTrace (prefixWord ++ tailWord_113485) baseStart_113485 baseEnd_113485 := by
    simpa [prefixWord, tailWord_113485, baseEnd_113485] using wordTrace_append hprefix tailTrace_113485
  have hstable : (prefixWord ++ tailWord_113485).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113485).length < 2 ^ (prefixWord ++ tailWord_113485).sum := by decide
  have hdescent : baseEnd_113485 < baseStart_113485 := by decide
  rcases family_descends (prefixWord ++ tailWord_113485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113508 : List Nat := [2, 3, 1, 1, 4, 1, 7]
def baseStart_113508 : Nat := 118140960795 + 113508 * 2 ^ 59
def prefixEnd_113508 : Nat := 4983230072969 + 3 ^ 40 * 113508 * 2
def baseEnd_113508 : Nat := 11512920914695730000591

theorem tailTrace_113508 : CollatzResearch.WordTrace tailWord_113508 prefixEnd_113508 11512920914695730000591 := by
  unfold tailWord_113508
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069988436393688234070589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2759984581858250978760785 2069988436393688234070589)
  ·
    refine ⟨776245663647633087776471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2069988436393688234070589 776245663647633087776471)
    ·
      refine ⟨1164368495471449631664707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 776245663647633087776471 1164368495471449631664707)
      ·
        refine ⟨1746552743207174447497061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164368495471449631664707 1746552743207174447497061)
        ·
          refine ⟨327478639351345208905699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1746552743207174447497061 327478639351345208905699)
          ·
            refine ⟨491217959027017813358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 327478639351345208905699 491217959027017813358549)
            ·
              refine ⟨11512920914695730000591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 491217959027017813358549 11512920914695730000591)
              ·
                rfl

theorem cell19_113508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_113508 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113508 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113508 prefixEnd_113508 := by exact prefixLift 113508
  have htrace : WordTrace (prefixWord ++ tailWord_113508) baseStart_113508 baseEnd_113508 := by
    simpa [prefixWord, tailWord_113508, baseEnd_113508] using wordTrace_append hprefix tailTrace_113508
  have hstable : (prefixWord ++ tailWord_113508).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113508).length < 2 ^ (prefixWord ++ tailWord_113508).sum := by decide
  have hdescent : baseEnd_113508 < baseStart_113508 := by decide
  rcases family_descends (prefixWord ++ tailWord_113508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113525 : List Nat := [1, 3, 4, 1, 1, 3, 2, 4]
def baseStart_113525 : Nat := 118140960795 + 113525 * 2 ^ 59
def prefixEnd_113525 : Nat := 4983230072969 + 3 ^ 40 * 113525 * 2
def baseEnd_113525 : Nat := 34543935586236187623949

theorem tailTrace_113525 : CollatzResearch.WordTrace tailWord_113525 prefixEnd_113525 34543935586236187623949 := by
  unfold tailWord_113525
  simp only [CollatzResearch.WordTrace]
  refine ⟨4140596913725788371510029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2760397942483858914340019 4140596913725788371510029)
  ·
    refine ⟨1552723842647170639316261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4140596913725788371510029 1552723842647170639316261)
    ·
      refine ⟨291135720496344494871799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1552723842647170639316261 291135720496344494871799)
      ·
        refine ⟨436703580744516742307699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291135720496344494871799 436703580744516742307699)
        ·
          refine ⟨655055371116775113461549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 436703580744516742307699 655055371116775113461549)
          ·
            refine ⟨245645764168790667548081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 655055371116775113461549 245645764168790667548081)
            ·
              refine ⟨184234323126593000661061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 245645764168790667548081 184234323126593000661061)
              ·
                refine ⟨34543935586236187623949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184234323126593000661061 34543935586236187623949)
                ·
                  rfl

theorem cell19_113525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 4].length) (baseStart_113525 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113525 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113525 prefixEnd_113525 := by exact prefixLift 113525
  have htrace : WordTrace (prefixWord ++ tailWord_113525) baseStart_113525 baseEnd_113525 := by
    simpa [prefixWord, tailWord_113525, baseEnd_113525] using wordTrace_append hprefix tailTrace_113525
  have hstable : (prefixWord ++ tailWord_113525).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113525).length < 2 ^ (prefixWord ++ tailWord_113525).sum := by decide
  have hdescent : baseEnd_113525 < baseStart_113525 := by decide
  rcases family_descends (prefixWord ++ tailWord_113525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113652 : List Nat := [2, 6, 2, 1, 1, 1, 1, 5]
def baseStart_113652 : Nat := 118140960795 + 113652 * 2 ^ 59
def prefixEnd_113652 : Nat := 4983230072969 + 3 ^ 40 * 113652 * 2
def baseEnd_113652 : Nat := 34582579759937522801381

theorem tailTrace_113652 : CollatzResearch.WordTrace tailWord_113652 prefixEnd_113652 34582579759937522801381 := by
  unfold tailWord_113652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072614492132844530691605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2763485989510459374255473 2072614492132844530691605)
  ·
    refine ⟨97153804318727087376169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2072614492132844530691605 97153804318727087376169)
    ·
      refine ⟨72865353239045315532127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97153804318727087376169 72865353239045315532127)
      ·
        refine ⟨109298029858567973298191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72865353239045315532127 109298029858567973298191)
        ·
          refine ⟨163947044787851959947287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109298029858567973298191 163947044787851959947287)
          ·
            refine ⟨245920567181777939920931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 163947044787851959947287 245920567181777939920931)
            ·
              refine ⟨368880850772666909881397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245920567181777939920931 368880850772666909881397)
              ·
                refine ⟨34582579759937522801381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368880850772666909881397 34582579759937522801381)
                ·
                  rfl

theorem cell19_113652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_113652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113652 prefixEnd_113652 := by exact prefixLift 113652
  have htrace : WordTrace (prefixWord ++ tailWord_113652) baseStart_113652 baseEnd_113652 := by
    simpa [prefixWord, tailWord_113652, baseEnd_113652] using wordTrace_append hprefix tailTrace_113652
  have hstable : (prefixWord ++ tailWord_113652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113652).length < 2 ^ (prefixWord ++ tailWord_113652).sum := by decide
  have hdescent : baseEnd_113652 < baseStart_113652 := by decide
  rcases family_descends (prefixWord ++ tailWord_113652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113660 : List Nat := [2, 2, 2, 1, 2, 4, 1, 5]
def baseStart_113660 : Nat := 118140960795 + 113660 * 2 ^ 59
def prefixEnd_113660 : Nat := 4983230072969 + 3 ^ 40 * 113660 * 2
def baseEnd_113660 : Nat := 34585014038595874623581

theorem tailTrace_113660 : CollatzResearch.WordTrace tailWord_113660 prefixEnd_113660 34585014038595874623581 := by
  unfold tailWord_113660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2072760384118353213837217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2763680512157804285116289 2072760384118353213837217)
  ·
    refine ⟨1554570288088764910377913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2072760384118353213837217 1554570288088764910377913)
    ·
      refine ⟨1165927716066573682783435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1554570288088764910377913 1165927716066573682783435)
      ·
        refine ⟨1748891574099860524175153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165927716066573682783435 1748891574099860524175153)
        ·
          refine ⟨1311668680574895393131365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748891574099860524175153 1311668680574895393131365)
          ·
            refine ⟨245937877607792886212131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1311668680574895393131365 245937877607792886212131)
            ·
              refine ⟨368906816411689329318197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 245937877607792886212131 368906816411689329318197)
              ·
                refine ⟨34585014038595874623581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 368906816411689329318197 34585014038595874623581)
                ·
                  rfl

theorem cell19_113660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_113660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113660 prefixEnd_113660 := by exact prefixLift 113660
  have htrace : WordTrace (prefixWord ++ tailWord_113660) baseStart_113660 baseEnd_113660 := by
    simpa [prefixWord, tailWord_113660, baseEnd_113660] using wordTrace_append hprefix tailTrace_113660
  have hstable : (prefixWord ++ tailWord_113660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113660).length < 2 ^ (prefixWord ++ tailWord_113660).sum := by decide
  have hdescent : baseEnd_113660 < baseStart_113660 := by decide
  rcases family_descends (prefixWord ++ tailWord_113660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113698 : List Nat := [3, 3, 1, 1, 1, 3, 1, 6]
def baseStart_113698 : Nat := 118140960795 + 113698 * 2 ^ 59
def prefixEnd_113698 : Nat := 4983230072969 + 3 ^ 40 * 113698 * 2
def baseEnd_113698 : Nat := 34596576862223045779033

theorem tailTrace_113698 : CollatzResearch.WordTrace tailWord_113698 prefixEnd_113698 34596576862223045779033 := by
  unfold tailWord_113698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036726685524759729389437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2764604494732692611705165 1036726685524759729389437)
  ·
    refine ⟨388772507071784898521039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1036726685524759729389437 388772507071784898521039)
    ·
      refine ⟨583158760607677347781559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 388772507071784898521039 583158760607677347781559)
      ·
        refine ⟨874738140911516021672339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583158760607677347781559 874738140911516021672339)
        ·
          refine ⟨1312107211367274032508509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874738140911516021672339 1312107211367274032508509)
          ·
            refine ⟨492040204262727762190691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1312107211367274032508509 492040204262727762190691)
            ·
              refine ⟨738060306394091643286037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 492040204262727762190691 738060306394091643286037)
              ·
                refine ⟨34596576862223045779033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 738060306394091643286037 34596576862223045779033)
                ·
                  rfl

theorem cell19_113698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_113698 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113698 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113698 prefixEnd_113698 := by exact prefixLift 113698
  have htrace : WordTrace (prefixWord ++ tailWord_113698) baseStart_113698 baseEnd_113698 := by
    simpa [prefixWord, tailWord_113698, baseEnd_113698] using wordTrace_append hprefix tailTrace_113698
  have hstable : (prefixWord ++ tailWord_113698).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113698).length < 2 ^ (prefixWord ++ tailWord_113698).sum := by decide
  have hdescent : baseEnd_113698 < baseStart_113698 := by decide
  rcases family_descends (prefixWord ++ tailWord_113698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113734 : List Nat := [6, 1, 1, 1, 1, 9]
def baseStart_113734 : Nat := 118140960795 + 113734 * 2 ^ 59
def prefixEnd_113734 : Nat := 4983230072969 + 3 ^ 40 * 113734 * 2
def baseEnd_113734 : Nat := 3845281235131736553215

theorem tailTrace_113734 : CollatzResearch.WordTrace tailWord_113734 prefixEnd_113734 3845281235131736553215 := by
  unfold tailWord_113734
  simp only [CollatzResearch.WordTrace]
  refine ⟨129631867811519283308383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2765479846645744710578837 129631867811519283308383)
  ·
    refine ⟨194447801717278924962575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 129631867811519283308383 194447801717278924962575)
    ·
      refine ⟨291671702575918387443863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194447801717278924962575 291671702575918387443863)
      ·
        refine ⟨437507553863877581165795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 291671702575918387443863 437507553863877581165795)
        ·
          refine ⟨656261330795816371748693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 437507553863877581165795 656261330795816371748693)
          ·
            refine ⟨3845281235131736553215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 656261330795816371748693 3845281235131736553215)
            ·
              rfl

theorem cell19_113734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 9].length) (baseStart_113734 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113734 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113734 prefixEnd_113734 := by exact prefixLift 113734
  have htrace : WordTrace (prefixWord ++ tailWord_113734) baseStart_113734 baseEnd_113734 := by
    simpa [prefixWord, tailWord_113734, baseEnd_113734] using wordTrace_append hprefix tailTrace_113734
  have hstable : (prefixWord ++ tailWord_113734).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113734).length < 2 ^ (prefixWord ++ tailWord_113734).sum := by decide
  have hdescent : baseEnd_113734 < baseStart_113734 := by decide
  rcases family_descends (prefixWord ++ tailWord_113734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113793 : List Nat := [1, 2, 4, 2, 2, 2, 6]
def baseStart_113793 : Nat := 118140960795 + 113793 * 2 ^ 59
def prefixEnd_113793 : Nat := 4983230072969 + 3 ^ 40 * 113793 * 2
def baseEnd_113793 : Nat := 11541827973763657889221

theorem tailTrace_113793 : CollatzResearch.WordTrace tailWord_113793 prefixEnd_113793 11541827973763657889221 := by
  unfold tailWord_113793
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150371676754870142266033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2766914451169913428177355 4150371676754870142266033)
  ·
    refine ⟨3112778757566152606699525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4150371676754870142266033 3112778757566152606699525)
    ·
      refine ⟨583646017043653613756161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3112778757566152606699525 583646017043653613756161)
      ·
        refine ⟨437734512782740210317121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 583646017043653613756161 437734512782740210317121)
        ·
          refine ⟨328300884587055157737841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 437734512782740210317121 328300884587055157737841)
          ·
            refine ⟨246225663440291368303381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 328300884587055157737841 246225663440291368303381)
            ·
              refine ⟨11541827973763657889221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246225663440291368303381 11541827973763657889221)
              ·
                rfl

theorem cell19_113793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 6].length) (baseStart_113793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113793 prefixEnd_113793 := by exact prefixLift 113793
  have htrace : WordTrace (prefixWord ++ tailWord_113793) baseStart_113793 baseEnd_113793 := by
    simpa [prefixWord, tailWord_113793, baseEnd_113793] using wordTrace_append hprefix tailTrace_113793
  have hstable : (prefixWord ++ tailWord_113793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113793).length < 2 ^ (prefixWord ++ tailWord_113793).sum := by decide
  have hdescent : baseEnd_113793 < baseStart_113793 := by decide
  rcases family_descends (prefixWord ++ tailWord_113793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113795 : List Nat := [1, 1, 1, 3, 3, 2, 8]
def baseStart_113795 : Nat := 118140960795 + 113795 * 2 ^ 59
def prefixEnd_113795 : Nat := 4983230072969 + 3 ^ 40 * 113795 * 2
def baseEnd_113795 : Nat := 11542030830318520541071

theorem tailTrace_113795 : CollatzResearch.WordTrace tailWord_113795 prefixEnd_113795 11542030830318520541071 := by
  unfold tailWord_113795
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150444622747624483838839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2766963081831749655892559 4150444622747624483838839)
  ·
    refine ⟨6225666934121436725758259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150444622747624483838839 6225666934121436725758259)
    ·
      refine ⟨9338500401182155088637389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225666934121436725758259 9338500401182155088637389)
      ·
        refine ⟨3501937650443308158239021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9338500401182155088637389 3501937650443308158239021)
        ·
          refine ⟨1313226618916240559339633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3501937650443308158239021 1313226618916240559339633)
          ·
            refine ⟨984919964187180419504725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313226618916240559339633 984919964187180419504725)
            ·
              refine ⟨11542030830318520541071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 984919964187180419504725 11542030830318520541071)
              ·
                rfl

theorem cell19_113795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 8].length) (baseStart_113795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113795 prefixEnd_113795 := by exact prefixLift 113795
  have htrace : WordTrace (prefixWord ++ tailWord_113795) baseStart_113795 baseEnd_113795 := by
    simpa [prefixWord, tailWord_113795, baseEnd_113795] using wordTrace_append hprefix tailTrace_113795
  have hstable : (prefixWord ++ tailWord_113795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113795).length < 2 ^ (prefixWord ++ tailWord_113795).sum := by decide
  have hdescent : baseEnd_113795 < baseStart_113795 := by decide
  rcases family_descends (prefixWord ++ tailWord_113795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113829 : List Nat := [1, 3, 1, 2, 1, 6, 2, 3]
def baseStart_113829 : Nat := 118140960795 + 113829 * 2 ^ 59
def prefixEnd_113829 : Nat := 4983230072969 + 3 ^ 40 * 113829 * 2
def baseEnd_113829 : Nat := 34636438175253556867565

theorem tailTrace_113829 : CollatzResearch.WordTrace tailWord_113829 prefixEnd_113829 34636438175253556867565 := by
  unfold tailWord_113829
  simp only [CollatzResearch.WordTrace]
  refine ⟨4151684704624448290576541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2767789803082965527051027 4151684704624448290576541)
  ·
    refine ⟨1556881764234168108966203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4151684704624448290576541 1556881764234168108966203)
    ·
      refine ⟨2335322646351252163449305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1556881764234168108966203 2335322646351252163449305)
      ·
        refine ⟨1751491984763439122586979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2335322646351252163449305 1751491984763439122586979)
        ·
          refine ⟨2627237977145158683880469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1751491984763439122586979 2627237977145158683880469)
          ·
            refine ⟨123151780178679313306897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2627237977145158683880469 123151780178679313306897)
            ·
              refine ⟨92363835134009484980173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123151780178679313306897 92363835134009484980173)
              ·
                refine ⟨34636438175253556867565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92363835134009484980173 34636438175253556867565)
                ·
                  rfl

theorem cell19_113829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 3].length) (baseStart_113829 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113829 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113829 prefixEnd_113829 := by exact prefixLift 113829
  have htrace : WordTrace (prefixWord ++ tailWord_113829) baseStart_113829 baseEnd_113829 := by
    simpa [prefixWord, tailWord_113829, baseEnd_113829] using wordTrace_append hprefix tailTrace_113829
  have hstable : (prefixWord ++ tailWord_113829).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113829).length < 2 ^ (prefixWord ++ tailWord_113829).sum := by decide
  have hdescent : baseEnd_113829 < baseStart_113829 := by decide
  rcases family_descends (prefixWord ++ tailWord_113829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113922 : List Nat := [3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_113922 : Nat := 118140960795 + 113922 * 2 ^ 59
def prefixEnd_113922 : Nat := 4983230072969 + 3 ^ 40 * 113922 * 2
def baseEnd_113922 : Nat := 34664736664656896800645

theorem tailTrace_113922 : CollatzResearch.WordTrace tailWord_113922 prefixEnd_113922 34664736664656896800645 := by
  unfold tailWord_113922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038769173321881293428005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2770051128858350115808013 1038769173321881293428005)
  ·
    refine ⟨194769219997852742517751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1038769173321881293428005 194769219997852742517751)
    ·
      refine ⟨292153829996779113776627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 194769219997852742517751 292153829996779113776627)
      ·
        refine ⟨438230744995168670664941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 292153829996779113776627 438230744995168670664941)
        ·
          refine ⟨164336529373188251499353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 438230744995168670664941 164336529373188251499353)
          ·
            refine ⟨123252397029891188624515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164336529373188251499353 123252397029891188624515)
            ·
              refine ⟨184878595544836782936773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123252397029891188624515 184878595544836782936773)
              ·
                refine ⟨34664736664656896800645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184878595544836782936773 34664736664656896800645)
                ·
                  rfl

theorem cell19_113922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_113922 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113922 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113922 prefixEnd_113922 := by exact prefixLift 113922
  have htrace : WordTrace (prefixWord ++ tailWord_113922) baseStart_113922 baseEnd_113922 := by
    simpa [prefixWord, tailWord_113922, baseEnd_113922] using wordTrace_append hprefix tailTrace_113922
  have hstable : (prefixWord ++ tailWord_113922).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113922).length < 2 ^ (prefixWord ++ tailWord_113922).sum := by decide
  have hdescent : baseEnd_113922 < baseStart_113922 := by decide
  rcases family_descends (prefixWord ++ tailWord_113922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_113924 : List Nat := [2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_113924 : Nat := 118140960795 + 113924 * 2 ^ 59
def prefixEnd_113924 : Nat := 4983230072969 + 3 ^ 40 * 113924 * 2
def baseEnd_113924 : Nat := 34665345234321484756195

theorem tailTrace_113924 : CollatzResearch.WordTrace tailWord_113924 prefixEnd_113924 34665345234321484756195 := by
  unfold tailWord_113924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2077574819640139757642413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2770099759520186343523217 2077574819640139757642413)
  ·
    refine ⟨779090557365052409115905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2077574819640139757642413 779090557365052409115905)
    ·
      refine ⟨584317918023789306836929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 779090557365052409115905 584317918023789306836929)
      ·
        refine ⟨438238438517841980127697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 584317918023789306836929 438238438517841980127697)
        ·
          refine ⟨328678828888381485095773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 438238438517841980127697 328678828888381485095773)
          ·
            refine ⟨123254560833143056910915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 328678828888381485095773 123254560833143056910915)
            ·
              refine ⟨184881841249714585366373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123254560833143056910915 184881841249714585366373)
              ·
                refine ⟨34665345234321484756195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 184881841249714585366373 34665345234321484756195)
                ·
                  rfl

theorem cell19_113924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_113924 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_113924 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_113924 prefixEnd_113924 := by exact prefixLift 113924
  have htrace : WordTrace (prefixWord ++ tailWord_113924) baseStart_113924 baseEnd_113924 := by
    simpa [prefixWord, tailWord_113924, baseEnd_113924] using wordTrace_append hprefix tailTrace_113924
  have hstable : (prefixWord ++ tailWord_113924).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_113924).length < 2 ^ (prefixWord ++ tailWord_113924).sum := by decide
  have hdescent : baseEnd_113924 < baseStart_113924 := by decide
  rcases family_descends (prefixWord ++ tailWord_113924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114076 : List Nat := [2, 2, 3, 4, 2, 6]
def baseStart_114076 : Nat := 118140960795 + 114076 * 2 ^ 59
def prefixEnd_114076 : Nat := 4983230072969 + 3 ^ 40 * 114076 * 2
def baseEnd_114076 : Nat := 3856844058758907708667

theorem tailTrace_114076 : CollatzResearch.WordTrace tailWord_114076 prefixEnd_114076 3856844058758907708667 := by
  unfold tailWord_114076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2080346767364804737409041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2773795689819739649878721 2080346767364804737409041)
  ·
    refine ⟨1560260075523603553056781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2080346767364804737409041 1560260075523603553056781)
    ·
      refine ⟨585097528321351332396293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1560260075523603553056781 585097528321351332396293)
      ·
        refine ⟨109705786560253374824305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 585097528321351332396293 109705786560253374824305)
        ·
          refine ⟨82279339920190031118229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109705786560253374824305 82279339920190031118229)
          ·
            refine ⟨3856844058758907708667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82279339920190031118229 3856844058758907708667)
            ·
              rfl

theorem cell19_114076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 6].length) (baseStart_114076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114076 prefixEnd_114076 := by exact prefixLift 114076
  have htrace : WordTrace (prefixWord ++ tailWord_114076) baseStart_114076 baseEnd_114076 := by
    simpa [prefixWord, tailWord_114076, baseEnd_114076] using wordTrace_append hprefix tailTrace_114076
  have hstable : (prefixWord ++ tailWord_114076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114076).length < 2 ^ (prefixWord ++ tailWord_114076).sum := by decide
  have hdescent : baseEnd_114076 < baseStart_114076 := by decide
  rcases family_descends (prefixWord ++ tailWord_114076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114078 : List Nat := [4, 3, 1, 2, 9]
def baseStart_114078 : Nat := 118140960795 + 114078 * 2 ^ 59
def prefixEnd_114078 : Nat := 4983230072969 + 3 ^ 40 * 114078 * 2
def baseEnd_114078 : Nat := 1285637225870176197539

theorem tailTrace_114078 : CollatzResearch.WordTrace tailWord_114078 prefixEnd_114078 1285637225870176197539 := by
  unfold tailWord_114078
  simp only [CollatzResearch.WordTrace]
  refine ⟨520095810090295477048861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2773844320481575877593925 520095810090295477048861)
  ·
    refine ⟨195035928783860803893323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 520095810090295477048861 195035928783860803893323)
    ·
      refine ⟨292553893175791205839985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195035928783860803893323 292553893175791205839985)
      ·
        refine ⟨219415419881843404379989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 292553893175791205839985 219415419881843404379989)
        ·
          refine ⟨1285637225870176197539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 219415419881843404379989 1285637225870176197539)
          ·
            rfl

theorem cell19_114078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 9].length) (baseStart_114078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114078 prefixEnd_114078 := by exact prefixLift 114078
  have htrace : WordTrace (prefixWord ++ tailWord_114078) baseStart_114078 baseEnd_114078 := by
    simpa [prefixWord, tailWord_114078, baseEnd_114078] using wordTrace_append hprefix tailTrace_114078
  have hstable : (prefixWord ++ tailWord_114078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114078).length < 2 ^ (prefixWord ++ tailWord_114078).sum := by decide
  have hdescent : baseEnd_114078 < baseStart_114078 := by decide
  rcases family_descends (prefixWord ++ tailWord_114078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114137 : List Nat := [1, 2, 1, 2, 4, 3, 6]
def baseStart_114137 : Nat := 118140960795 + 114137 * 2 ^ 59
def prefixEnd_114137 : Nat := 4983230072969 + 3 ^ 40 * 114137 * 2
def baseEnd_114137 : Nat := 11576719301200034007427

theorem tailTrace_114137 : CollatzResearch.WordTrace tailWord_114137 prefixEnd_114137 11576719301200034007427 := by
  unfold tailWord_114137
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162918387508616892788665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2775278925005744595192443 4162918387508616892788665)
  ·
    refine ⟨3122188790631462669591499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4162918387508616892788665 3122188790631462669591499)
    ·
      refine ⟨4683283185947194004387249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3122188790631462669591499 4683283185947194004387249)
      ·
        refine ⟨3512462389460395503290437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4683283185947194004387249 3512462389460395503290437)
        ·
          refine ⟨658586698023824156866957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3512462389460395503290437 658586698023824156866957)
          ·
            refine ⟨246970011758934058825109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 658586698023824156866957 246970011758934058825109)
            ·
              refine ⟨11576719301200034007427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 246970011758934058825109 11576719301200034007427)
              ·
                rfl

theorem cell19_114137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 6].length) (baseStart_114137 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114137 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114137 prefixEnd_114137 := by exact prefixLift 114137
  have htrace : WordTrace (prefixWord ++ tailWord_114137) baseStart_114137 baseEnd_114137 := by
    simpa [prefixWord, tailWord_114137, baseEnd_114137] using wordTrace_append hprefix tailTrace_114137
  have hstable : (prefixWord ++ tailWord_114137).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114137).length < 2 ^ (prefixWord ++ tailWord_114137).sum := by decide
  have hdescent : baseEnd_114137 < baseStart_114137 := by decide
  rcases family_descends (prefixWord ++ tailWord_114137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114173 : List Nat := [1, 4, 1, 1, 1, 4, 4, 3]
def baseStart_114173 : Nat := 118140960795 + 114173 * 2 ^ 59
def prefixEnd_114173 : Nat := 4983230072969 + 3 ^ 40 * 114173 * 2
def baseEnd_114173 : Nat := 34741112157562685222183

theorem tailTrace_114173 : CollatzResearch.WordTrace tailWord_114173 prefixEnd_114173 34741112157562685222183 := by
  unfold tailWord_114173
  simp only [CollatzResearch.WordTrace]
  refine ⟨4164231415378195041099173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2776154276918796694066115 4164231415378195041099173)
  ·
    refine ⟨780793390383411570206095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4164231415378195041099173 780793390383411570206095)
    ·
      refine ⟨1171190085575117355309143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780793390383411570206095 1171190085575117355309143)
      ·
        refine ⟨1756785128362676032963715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1171190085575117355309143 1756785128362676032963715)
        ·
          refine ⟨2635177692544014049445573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1756785128362676032963715 2635177692544014049445573)
          ·
            refine ⟨494095817352002634271045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2635177692544014049445573 494095817352002634271045)
            ·
              refine ⟨92642965753500493925821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 494095817352002634271045 92642965753500493925821)
              ·
                refine ⟨34741112157562685222183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92642965753500493925821 34741112157562685222183)
                ·
                  rfl

theorem cell19_114173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 3].length) (baseStart_114173 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114173 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114173 prefixEnd_114173 := by exact prefixLift 114173
  have htrace : WordTrace (prefixWord ++ tailWord_114173) baseStart_114173 baseEnd_114173 := by
    simpa [prefixWord, tailWord_114173, baseEnd_114173] using wordTrace_append hprefix tailTrace_114173
  have hstable : (prefixWord ++ tailWord_114173).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114173).length < 2 ^ (prefixWord ++ tailWord_114173).sum := by decide
  have hdescent : baseEnd_114173 < baseStart_114173 := by decide
  rcases family_descends (prefixWord ++ tailWord_114173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114190 : List Nat := [4, 1, 1, 2, 5, 1, 5]
def baseStart_114190 : Nat := 118140960795 + 114190 * 2 ^ 59
def prefixEnd_114190 : Nat := 4983230072969 + 3 ^ 40 * 114190 * 2
def baseEnd_114190 : Nat := 11582094999903894281453

theorem tailTrace_114190 : CollatzResearch.WordTrace tailWord_114190 prefixEnd_114190 11582094999903894281453 := by
  unfold tailWord_114190
  simp only [CollatzResearch.WordTrace]
  refine ⟨520606432039575868058503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2776567637544404629645349 520606432039575868058503)
  ·
    refine ⟨780909648059363802087755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 520606432039575868058503 780909648059363802087755)
    ·
      refine ⟨1171364472089045703131633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 780909648059363802087755 1171364472089045703131633)
      ·
        refine ⟨878523354066784277348725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1171364472089045703131633 878523354066784277348725)
        ·
          refine ⟨82361564443761026001443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 878523354066784277348725 82361564443761026001443)
          ·
            refine ⟨123542346665641539002165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82361564443761026001443 123542346665641539002165)
            ·
              refine ⟨11582094999903894281453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 123542346665641539002165 11582094999903894281453)
              ·
                rfl

theorem cell19_114190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_114190 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114190 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114190 prefixEnd_114190 := by exact prefixLift 114190
  have htrace : WordTrace (prefixWord ++ tailWord_114190) baseStart_114190 baseEnd_114190 := by
    simpa [prefixWord, tailWord_114190, baseEnd_114190] using wordTrace_append hprefix tailTrace_114190
  have hstable : (prefixWord ++ tailWord_114190).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114190).length < 2 ^ (prefixWord ++ tailWord_114190).sum := by decide
  have hdescent : baseEnd_114190 < baseStart_114190 := by decide
  rcases family_descends (prefixWord ++ tailWord_114190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114211 : List Nat := [1, 1, 1, 4, 5, 1, 2, 4]
def baseStart_114211 : Nat := 118140960795 + 114211 * 2 ^ 59
def prefixEnd_114211 : Nat := 4983230072969 + 3 ^ 40 * 114211 * 2
def baseEnd_114211 : Nat := 34752674981189856377635

theorem tailTrace_114211 : CollatzResearch.WordTrace tailWord_114211 prefixEnd_114211 34752674981189856377635 := by
  unfold tailWord_114211
  simp only [CollatzResearch.WordTrace]
  refine ⟨4165617389240527530982487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2777078259493685020654991 4165617389240527530982487)
  ·
    refine ⟨6248426083860791296473731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4165617389240527530982487 6248426083860791296473731)
    ·
      refine ⟨9372639125791186944710597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6248426083860791296473731 9372639125791186944710597)
      ·
        refine ⟨1757369836085847552133237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9372639125791186944710597 1757369836085847552133237)
        ·
          refine ⟨164753422133048208012491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1757369836085847552133237 164753422133048208012491)
          ·
            refine ⟨247130133199572312018737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164753422133048208012491 247130133199572312018737)
            ·
              refine ⟨185347599899679234014053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 247130133199572312018737 185347599899679234014053)
              ·
                refine ⟨34752674981189856377635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185347599899679234014053 34752674981189856377635)
                ·
                  rfl

theorem cell19_114211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 4].length) (baseStart_114211 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114211 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114211 prefixEnd_114211 := by exact prefixLift 114211
  have htrace : WordTrace (prefixWord ++ tailWord_114211) baseStart_114211 baseEnd_114211 := by
    simpa [prefixWord, tailWord_114211, baseEnd_114211] using wordTrace_append hprefix tailTrace_114211
  have hstable : (prefixWord ++ tailWord_114211).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114211).length < 2 ^ (prefixWord ++ tailWord_114211).sum := by decide
  have hdescent : baseEnd_114211 < baseStart_114211 := by decide
  rcases family_descends (prefixWord ++ tailWord_114211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114232 : List Nat := [2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_114232 : Nat := 118140960795 + 114232 * 2 ^ 59
def prefixEnd_114232 : Nat := 4983230072969 + 3 ^ 40 * 114232 * 2
def baseEnd_114232 : Nat := 34759064962668029910911

theorem tailTrace_114232 : CollatzResearch.WordTrace tailWord_114232 prefixEnd_114232 34759064962668029910911 := by
  unfold tailWord_114232
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083191661082224058748475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2777588881442965411664633 2083191661082224058748475)
  ·
    refine ⟨3124787491623336088122713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2083191661082224058748475 3124787491623336088122713)
    ·
      refine ⟨2343590618717502066092035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3124787491623336088122713 2343590618717502066092035)
      ·
        refine ⟨3515385928076253099138053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2343590618717502066092035 3515385928076253099138053)
        ·
          refine ⟨659134861514297456088385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3515385928076253099138053 659134861514297456088385)
          ·
            refine ⟨494351146135723092066289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 659134861514297456088385 494351146135723092066289)
            ·
              refine ⟨370763359601792319049717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 494351146135723092066289 370763359601792319049717)
              ·
                refine ⟨34759064962668029910911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 370763359601792319049717 34759064962668029910911)
                ·
                  rfl

theorem cell19_114232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_114232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114232 prefixEnd_114232 := by exact prefixLift 114232
  have htrace : WordTrace (prefixWord ++ tailWord_114232) baseStart_114232 baseEnd_114232 := by
    simpa [prefixWord, tailWord_114232, baseEnd_114232] using wordTrace_append hprefix tailTrace_114232
  have hstable : (prefixWord ++ tailWord_114232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114232).length < 2 ^ (prefixWord ++ tailWord_114232).sum := by decide
  have hdescent : baseEnd_114232 < baseStart_114232 := by decide
  rcases family_descends (prefixWord ++ tailWord_114232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114262 : List Nat := [5, 2, 2, 2, 1, 2, 1, 4]
def baseStart_114262 : Nat := 118140960795 + 114262 * 2 ^ 59
def prefixEnd_114262 : Nat := 4983230072969 + 3 ^ 40 * 114262 * 2
def baseEnd_114262 : Nat := 34768193507636849244163

theorem tailTrace_114262 : CollatzResearch.WordTrace tailWord_114262 prefixEnd_114262 34768193507636849244163 := by
  unfold tailWord_114262
  simp only [CollatzResearch.WordTrace]
  refine ⟨260467344503485202568065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2778318341370508827392693 260467344503485202568065)
  ·
    refine ⟨195350508377613901926049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 260467344503485202568065 195350508377613901926049)
    ·
      refine ⟨146512881283210426444537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195350508377613901926049 146512881283210426444537)
      ·
        refine ⟨109884660962407819833403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146512881283210426444537 109884660962407819833403)
        ·
          refine ⟨164826991443611729750105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 109884660962407819833403 164826991443611729750105)
          ·
            refine ⟨123620243582708797312579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 164826991443611729750105 123620243582708797312579)
            ·
              refine ⟨185430365374063195968869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123620243582708797312579 185430365374063195968869)
              ·
                refine ⟨34768193507636849244163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185430365374063195968869 34768193507636849244163)
                ·
                  rfl

theorem cell19_114262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_114262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114262 prefixEnd_114262 := by exact prefixLift 114262
  have htrace : WordTrace (prefixWord ++ tailWord_114262) baseStart_114262 baseEnd_114262 := by
    simpa [prefixWord, tailWord_114262, baseEnd_114262] using wordTrace_append hprefix tailTrace_114262
  have hstable : (prefixWord ++ tailWord_114262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114262).length < 2 ^ (prefixWord ++ tailWord_114262).sum := by decide
  have hdescent : baseEnd_114262 < baseStart_114262 := by decide
  rcases family_descends (prefixWord ++ tailWord_114262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114268 : List Nat := [2, 2, 4, 1, 2, 1, 3, 4]
def baseStart_114268 : Nat := 118140960795 + 114268 * 2 ^ 59
def prefixEnd_114268 : Nat := 4983230072969 + 3 ^ 40 * 114268 * 2
def baseEnd_114268 : Nat := 34770019216630613110813

theorem tailTrace_114268 : CollatzResearch.WordTrace tailWord_114268 prefixEnd_114268 34770019216630613110813 := by
  unfold tailWord_114268
  simp only [CollatzResearch.WordTrace]
  refine ⟨2083848175017013132903729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2778464233356017510538305 2083848175017013132903729)
  ·
    refine ⟨1562886131262759849677797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2083848175017013132903729 1562886131262759849677797)
    ·
      refine ⟨293041149611767471814587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1562886131262759849677797 293041149611767471814587)
      ·
        refine ⟨439561724417651207721881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293041149611767471814587 439561724417651207721881)
        ·
          refine ⟨329671293313238405791411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 439561724417651207721881 329671293313238405791411)
          ·
            refine ⟨494506939969857608687117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 329671293313238405791411 494506939969857608687117)
            ·
              refine ⟨185440102488696603257669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 494506939969857608687117 185440102488696603257669)
              ·
                refine ⟨34770019216630613110813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 185440102488696603257669 34770019216630613110813)
                ·
                  rfl

theorem cell19_114268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_114268 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114268 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114268 prefixEnd_114268 := by exact prefixLift 114268
  have htrace : WordTrace (prefixWord ++ tailWord_114268) baseStart_114268 baseEnd_114268 := by
    simpa [prefixWord, tailWord_114268, baseEnd_114268] using wordTrace_append hprefix tailTrace_114268
  have hstable : (prefixWord ++ tailWord_114268).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114268).length < 2 ^ (prefixWord ++ tailWord_114268).sum := by decide
  have hdescent : baseEnd_114268 < baseStart_114268 := by decide
  rcases family_descends (prefixWord ++ tailWord_114268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114285 : List Nat := [1, 5, 1, 1, 4, 1, 3, 3]
def baseStart_114285 : Nat := 118140960795 + 114285 * 2 ^ 59
def prefixEnd_114285 : Nat := 4983230072969 + 3 ^ 40 * 114285 * 2
def baseEnd_114285 : Nat := 34775192058779610732989

theorem tailTrace_114285 : CollatzResearch.WordTrace tailWord_114285 prefixEnd_114285 34775192058779610732989 := by
  unfold tailWord_114285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4168316390972438169176309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2778877593981625446117539 4168316390972438169176309)
  ·
    refine ⟨390779661653666078360279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4168316390972438169176309 390779661653666078360279)
    ·
      refine ⟨586169492480499117540419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390779661653666078360279 586169492480499117540419)
      ·
        refine ⟨879254238720748676310629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586169492480499117540419 879254238720748676310629)
        ·
          refine ⟨164860169760140376808243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 879254238720748676310629 164860169760140376808243)
          ·
            refine ⟨247290254640210565212365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 164860169760140376808243 247290254640210565212365)
            ·
              refine ⟨92733845490078961954637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247290254640210565212365 92733845490078961954637)
              ·
                refine ⟨34775192058779610732989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92733845490078961954637 34775192058779610732989)
                ·
                  rfl

theorem cell19_114285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 3, 3].length) (baseStart_114285 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114285 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114285 prefixEnd_114285 := by exact prefixLift 114285
  have htrace : WordTrace (prefixWord ++ tailWord_114285) baseStart_114285 baseEnd_114285 := by
    simpa [prefixWord, tailWord_114285, baseEnd_114285] using wordTrace_append hprefix tailTrace_114285
  have hstable : (prefixWord ++ tailWord_114285).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114285).length < 2 ^ (prefixWord ++ tailWord_114285).sum := by decide
  have hdescent : baseEnd_114285 < baseStart_114285 := by decide
  rcases family_descends (prefixWord ++ tailWord_114285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114338 : List Nat := [3, 3, 1, 4, 2, 1, 2, 3]
def baseStart_114338 : Nat := 118140960795 + 114338 * 2 ^ 59
def prefixEnd_114338 : Nat := 4983230072969 + 3 ^ 40 * 114338 * 2
def baseEnd_114338 : Nat := 34791319154891191555067

theorem tailTrace_114338 : CollatzResearch.WordTrace tailWord_114338 prefixEnd_114338 34791319154891191555067 := by
  unfold tailWord_114338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1042562364945107055213917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2780166306520285480570445 1042562364945107055213917)
  ·
    refine ⟨390960886854415145705219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1042562364945107055213917 390960886854415145705219)
    ·
      refine ⟨586441330281622718557829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 390960886854415145705219 586441330281622718557829)
      ·
        refine ⟨109957749427804259729593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 586441330281622718557829 109957749427804259729593)
        ·
          refine ⟨82468312070853194797195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 109957749427804259729593 82468312070853194797195)
          ·
            refine ⟨123702468106279792195793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82468312070853194797195 123702468106279792195793)
            ·
              refine ⟨92776851079709844146845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123702468106279792195793 92776851079709844146845)
              ·
                refine ⟨34791319154891191555067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92776851079709844146845 34791319154891191555067)
                ·
                  rfl

theorem cell19_114338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_114338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114338 prefixEnd_114338 := by exact prefixLift 114338
  have htrace : WordTrace (prefixWord ++ tailWord_114338) baseStart_114338 baseEnd_114338 := by
    simpa [prefixWord, tailWord_114338, baseEnd_114338] using wordTrace_append hprefix tailTrace_114338
  have hstable : (prefixWord ++ tailWord_114338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114338).length < 2 ^ (prefixWord ++ tailWord_114338).sum := by decide
  have hdescent : baseEnd_114338 < baseStart_114338 := by decide
  rcases family_descends (prefixWord ++ tailWord_114338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114422 : List Nat := [5, 1, 1, 1, 1, 10]
def baseStart_114422 : Nat := 118140960795 + 114422 * 2 ^ 59
def prefixEnd_114422 : Nat := 4983230072969 + 3 ^ 40 * 114422 * 2
def baseEnd_114422 : Nat := 3868542120089320632019

theorem tailTrace_114422 : CollatzResearch.WordTrace tailWord_114422 prefixEnd_114422 3868542120089320632019 := by
  unfold tailWord_114422
  simp only [CollatzResearch.WordTrace]
  refine ⟨260832074467256910432095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2782208794317407044609013 260832074467256910432095)
  ·
    refine ⟨391248111700885365648143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 260832074467256910432095 391248111700885365648143)
    ·
      refine ⟨586872167551328048472215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 391248111700885365648143 586872167551328048472215)
      ·
        refine ⟨880308251326992072708323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 586872167551328048472215 880308251326992072708323)
        ·
          refine ⟨1320462376990488109062485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 880308251326992072708323 1320462376990488109062485)
          ·
            refine ⟨3868542120089320632019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1320462376990488109062485 3868542120089320632019)
            ·
              rfl

theorem cell19_114422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 10].length) (baseStart_114422 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114422 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114422 prefixEnd_114422 := by exact prefixLift 114422
  have htrace : WordTrace (prefixWord ++ tailWord_114422) baseStart_114422 baseEnd_114422 := by
    simpa [prefixWord, tailWord_114422, baseEnd_114422] using wordTrace_append hprefix tailTrace_114422
  have hstable : (prefixWord ++ tailWord_114422).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114422).length < 2 ^ (prefixWord ++ tailWord_114422).sum := by decide
  have hdescent : baseEnd_114422 < baseStart_114422 := by decide
  rcases family_descends (prefixWord ++ tailWord_114422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114452 : List Nat := [2, 4, 4, 1, 1, 1, 3, 3]
def baseStart_114452 : Nat := 118140960795 + 114452 * 2 ^ 59
def prefixEnd_114452 : Nat := 4983230072969 + 3 ^ 40 * 114452 * 2
def baseEnd_114452 : Nat := 34826007625772705021423

theorem tailTrace_114452 : CollatzResearch.WordTrace tailWord_114452 prefixEnd_114452 34826007625772705021423 := by
  unfold tailWord_114452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2087203690683712845252805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2782938254244950460337073 2087203690683712845252805)
  ·
    refine ⟨391350692003196158484901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2087203690683712845252805 391350692003196158484901)
    ·
      refine ⟨73378254750599279715919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 391350692003196158484901 73378254750599279715919)
      ·
        refine ⟨110067382125898919573879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73378254750599279715919 110067382125898919573879)
        ·
          refine ⟨165101073188848379360819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110067382125898919573879 165101073188848379360819)
          ·
            refine ⟨247651609783272569041229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165101073188848379360819 247651609783272569041229)
            ·
              refine ⟨92869353668727213390461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247651609783272569041229 92869353668727213390461)
              ·
                refine ⟨34826007625772705021423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92869353668727213390461 34826007625772705021423)
                ·
                  rfl

theorem cell19_114452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_114452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114452 prefixEnd_114452 := by exact prefixLift 114452
  have htrace : WordTrace (prefixWord ++ tailWord_114452) baseStart_114452 baseEnd_114452 := by
    simpa [prefixWord, tailWord_114452, baseEnd_114452] using wordTrace_append hprefix tailTrace_114452
  have hstable : (prefixWord ++ tailWord_114452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114452).length < 2 ^ (prefixWord ++ tailWord_114452).sum := by decide
  have hdescent : baseEnd_114452 < baseStart_114452 := by decide
  rcases family_descends (prefixWord ++ tailWord_114452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114458 : List Nat := [3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_114458 : Nat := 118140960795 + 114458 * 2 ^ 59
def prefixEnd_114458 : Nat := 4983230072969 + 3 ^ 40 * 114458 * 2
def baseEnd_114458 : Nat := 34827833334766468888073

theorem tailTrace_114458 : CollatzResearch.WordTrace tailWord_114458 prefixEnd_114458 34827833334766468888073 := by
  unfold tailWord_114458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1043656554836422178806007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2783084146230459143482685 1043656554836422178806007)
  ·
    refine ⟨1565484832254633268209011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1043656554836422178806007 1565484832254633268209011)
    ·
      refine ⟨2348227248381949902313517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1565484832254633268209011 2348227248381949902313517)
      ·
        refine ⟨880585218143231213367569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2348227248381949902313517 880585218143231213367569)
        ·
          refine ⟨660438913607423410025677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 880585218143231213367569 660438913607423410025677)
          ·
            refine ⟨247664592602783778759629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660438913607423410025677 247664592602783778759629)
            ·
              refine ⟨92874222226043917034861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247664592602783778759629 92874222226043917034861)
              ·
                refine ⟨34827833334766468888073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92874222226043917034861 34827833334766468888073)
                ·
                  rfl

theorem cell19_114458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_114458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114458 prefixEnd_114458 := by exact prefixLift 114458
  have htrace : WordTrace (prefixWord ++ tailWord_114458) baseStart_114458 baseEnd_114458 := by
    simpa [prefixWord, tailWord_114458, baseEnd_114458] using wordTrace_append hprefix tailTrace_114458
  have hstable : (prefixWord ++ tailWord_114458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114458).length < 2 ^ (prefixWord ++ tailWord_114458).sum := by decide
  have hdescent : baseEnd_114458 < baseStart_114458 := by decide
  rcases family_descends (prefixWord ++ tailWord_114458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114517 : List Nat := [1, 3, 2, 2, 2, 3, 1, 5]
def baseStart_114517 : Nat := 118140960795 + 114517 * 2 ^ 59
def prefixEnd_114517 : Nat := 4983230072969 + 3 ^ 40 * 114517 * 2
def baseEnd_114517 : Nat := 34845786139871813576801

theorem tailTrace_114517 : CollatzResearch.WordTrace tailWord_114517 prefixEnd_114517 34845786139871813576801 := by
  unfold tailWord_114517
  simp only [CollatzResearch.WordTrace]
  refine ⟨4176778126131941791621805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2784518750754627861081203 4176778126131941791621805)
  ·
    refine ⟨1566291797299478171858177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4176778126131941791621805 1566291797299478171858177)
    ·
      refine ⟨1174718847974608628893633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1566291797299478171858177 1174718847974608628893633)
      ·
        refine ⟨881039135980956471670225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1174718847974608628893633 881039135980956471670225)
        ·
          refine ⟨660779351985717353752669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 881039135980956471670225 660779351985717353752669)
          ·
            refine ⟨247792256994644007657251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 660779351985717353752669 247792256994644007657251)
            ·
              refine ⟨371688385491966011485877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247792256994644007657251 371688385491966011485877)
              ·
                refine ⟨34845786139871813576801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 371688385491966011485877 34845786139871813576801)
                ·
                  rfl

theorem cell19_114517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 5].length) (baseStart_114517 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114517 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114517 prefixEnd_114517 := by exact prefixLift 114517
  have htrace : WordTrace (prefixWord ++ tailWord_114517) baseStart_114517 baseEnd_114517 := by
    simpa [prefixWord, tailWord_114517, baseEnd_114517] using wordTrace_append hprefix tailTrace_114517
  have hstable : (prefixWord ++ tailWord_114517).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114517).length < 2 ^ (prefixWord ++ tailWord_114517).sum := by decide
  have hdescent : baseEnd_114517 < baseStart_114517 := by decide
  rcases family_descends (prefixWord ++ tailWord_114517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114593 : List Nat := [1, 2, 3, 4, 2, 7]
def baseStart_114593 : Nat := 118140960795 + 114593 * 2 ^ 59
def prefixEnd_114593 : Nat := 4983230072969 + 3 ^ 40 * 114593 * 2
def baseEnd_114593 : Nat := 3874323531902906209745

theorem tailTrace_114593 : CollatzResearch.WordTrace tailWord_114593 prefixEnd_114593 3874323531902906209745 := by
  unfold tailWord_114593
  simp only [CollatzResearch.WordTrace]
  refine ⟨4179550073856606771388433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2786366715904404514258955 4179550073856606771388433)
  ·
    refine ⟨3134662555392455078541325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4179550073856606771388433 3134662555392455078541325)
    ·
      refine ⟨1175498458272170654452997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3134662555392455078541325 1175498458272170654452997)
      ·
        refine ⟨220405960926031997709937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1175498458272170654452997 220405960926031997709937)
        ·
          refine ⟨165304470694523998282453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220405960926031997709937 165304470694523998282453)
          ·
            refine ⟨3874323531902906209745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165304470694523998282453 3874323531902906209745)
            ·
              rfl

theorem cell19_114593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_114593 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114593 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114593 prefixEnd_114593 := by exact prefixLift 114593
  have htrace : WordTrace (prefixWord ++ tailWord_114593) baseStart_114593 baseEnd_114593 := by
    simpa [prefixWord, tailWord_114593, baseEnd_114593] using wordTrace_append hprefix tailTrace_114593
  have hstable : (prefixWord ++ tailWord_114593).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114593).length < 2 ^ (prefixWord ++ tailWord_114593).sum := by decide
  have hdescent : baseEnd_114593 < baseStart_114593 := by decide
  rcases family_descends (prefixWord ++ tailWord_114593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114650 : List Nat := [3, 1, 1, 2, 5, 1, 6]
def baseStart_114650 : Nat := 118140960795 + 114650 * 2 ^ 59
def prefixEnd_114650 : Nat := 4983230072969 + 3 ^ 40 * 114650 * 2
def baseEnd_114650 : Nat := 11628752007522304206961

theorem tailTrace_114650 : CollatzResearch.WordTrace tailWord_114650 prefixEnd_114650 11628752007522304206961 := by
  unfold tailWord_114650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1045407258662526376553351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2787752689766737004142269 1045407258662526376553351)
  ·
    refine ⟨1568110887993789564830027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1045407258662526376553351 1568110887993789564830027)
    ·
      refine ⟨2352166331990684347245041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568110887993789564830027 2352166331990684347245041)
      ·
        refine ⟨1764124748993013260433781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352166331990684347245041 1764124748993013260433781)
        ·
          refine ⟨165386695218094993165667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1764124748993013260433781 165386695218094993165667)
          ·
            refine ⟨248080042827142489748501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165386695218094993165667 248080042827142489748501)
            ·
              refine ⟨11628752007522304206961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248080042827142489748501 11628752007522304206961)
              ·
                rfl

theorem cell19_114650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 6].length) (baseStart_114650 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114650 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114650 prefixEnd_114650 := by exact prefixLift 114650
  have htrace : WordTrace (prefixWord ++ tailWord_114650) baseStart_114650 baseEnd_114650 := by
    simpa [prefixWord, tailWord_114650, baseEnd_114650] using wordTrace_append hprefix tailTrace_114650
  have hstable : (prefixWord ++ tailWord_114650).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114650).length < 2 ^ (prefixWord ++ tailWord_114650).sum := by decide
  have hdescent : baseEnd_114650 < baseStart_114650 := by decide
  rcases family_descends (prefixWord ++ tailWord_114650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114671 : List Nat := [1, 1, 2, 1, 4, 2, 2, 6]
def baseStart_114671 : Nat := 118140960795 + 114671 * 2 ^ 59
def prefixEnd_114671 : Nat := 4983230072969 + 3 ^ 40 * 114671 * 2
def baseEnd_114671 : Nat := 34892646004045086154159

theorem tailTrace_114671 : CollatzResearch.WordTrace tailWord_114671 prefixEnd_114671 34892646004045086154159 := by
  unfold tailWord_114671
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182394967574026092727867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2788263311716017395151911 4182394967574026092727867)
  ·
    refine ⟨6273592451361039139091801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182394967574026092727867 6273592451361039139091801)
    ·
      refine ⟨4705194338520779354318851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273592451361039139091801 4705194338520779354318851)
      ·
        refine ⟨7057791507781169031478277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705194338520779354318851 7057791507781169031478277)
        ·
          refine ⟨1323335907708969193402177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7057791507781169031478277 1323335907708969193402177)
          ·
            refine ⟨992501930781726895051633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1323335907708969193402177 992501930781726895051633)
            ·
              refine ⟨744376448086295171288725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 992501930781726895051633 744376448086295171288725)
              ·
                refine ⟨34892646004045086154159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 744376448086295171288725 34892646004045086154159)
                ·
                  rfl

theorem cell19_114671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_114671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114671 prefixEnd_114671 := by exact prefixLift 114671
  have htrace : WordTrace (prefixWord ++ tailWord_114671) baseStart_114671 baseEnd_114671 := by
    simpa [prefixWord, tailWord_114671, baseEnd_114671] using wordTrace_append hprefix tailTrace_114671
  have hstable : (prefixWord ++ tailWord_114671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114671).length < 2 ^ (prefixWord ++ tailWord_114671).sum := by decide
  have hdescent : baseEnd_114671 < baseStart_114671 := by decide
  rcases family_descends (prefixWord ++ tailWord_114671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114686 : List Nat := [4, 2, 2, 2, 1, 2, 1, 5]
def baseStart_114686 : Nat := 118140960795 + 114686 * 2 ^ 59
def prefixEnd_114686 : Nat := 4983230072969 + 3 ^ 40 * 114686 * 2
def baseEnd_114686 : Nat := 34897210276529495820785

theorem tailTrace_114686 : CollatzResearch.WordTrace tailWord_114686 prefixEnd_114686 34897210276529495820785 := by
  unfold tailWord_114686
  simp only [CollatzResearch.WordTrace]
  refine ⟨522867757814960456815489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2788628041679789103015941 522867757814960456815489)
  ·
    refine ⟨392150818361220342611617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 522867757814960456815489 392150818361220342611617)
    ·
      refine ⟨294113113770915256958713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392150818361220342611617 294113113770915256958713)
      ·
        refine ⟨220584835328186442719035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294113113770915256958713 220584835328186442719035)
        ·
          refine ⟨330877252992279664078553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220584835328186442719035 330877252992279664078553)
          ·
            refine ⟨248157939744209748058915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330877252992279664078553 248157939744209748058915)
            ·
              refine ⟨372236909616314622088373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248157939744209748058915 372236909616314622088373)
              ·
                refine ⟨34897210276529495820785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 372236909616314622088373 34897210276529495820785)
                ·
                  rfl

theorem cell19_114686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_114686 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114686 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114686 prefixEnd_114686 := by exact prefixLift 114686
  have htrace : WordTrace (prefixWord ++ tailWord_114686) baseStart_114686 baseEnd_114686 := by
    simpa [prefixWord, tailWord_114686, baseEnd_114686] using wordTrace_append hprefix tailTrace_114686
  have hstable : (prefixWord ++ tailWord_114686).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114686).length < 2 ^ (prefixWord ++ tailWord_114686).sum := by decide
  have hdescent : baseEnd_114686 < baseStart_114686 := by decide
  rcases family_descends (prefixWord ++ tailWord_114686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114701 : List Nat := [1, 7, 1, 2, 1, 2, 5]
def baseStart_114701 : Nat := 118140960795 + 114701 * 2 ^ 59
def prefixEnd_114701 : Nat := 4983230072969 + 3 ^ 40 * 114701 * 2
def baseEnd_114701 : Nat := 11633924849671301829137

theorem tailTrace_114701 : CollatzResearch.WordTrace tailWord_114701 prefixEnd_114701 11633924849671301829137 := by
  unfold tailWord_114701
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183489157465341216319957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2788992771643560810879971 4183489157465341216319957)
  ·
    refine ⟨98050527128093934757499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 4183489157465341216319957 98050527128093934757499)
    ·
      refine ⟨147075790692140902136249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98050527128093934757499 147075790692140902136249)
      ·
        refine ⟨110306843019105676602187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147075790692140902136249 110306843019105676602187)
        ·
          refine ⟨165460264528658514903281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110306843019105676602187 165460264528658514903281)
          ·
            refine ⟨124095198396493886177461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165460264528658514903281 124095198396493886177461)
            ·
              refine ⟨11633924849671301829137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124095198396493886177461 11633924849671301829137)
              ·
                rfl

theorem cell19_114701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_114701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114701 prefixEnd_114701 := by exact prefixLift 114701
  have htrace : WordTrace (prefixWord ++ tailWord_114701) baseStart_114701 baseEnd_114701 := by
    simpa [prefixWord, tailWord_114701, baseEnd_114701] using wordTrace_append hprefix tailTrace_114701
  have hstable : (prefixWord ++ tailWord_114701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114701).length < 2 ^ (prefixWord ++ tailWord_114701).sum := by decide
  have hdescent : baseEnd_114701 < baseStart_114701 := by decide
  rcases family_descends (prefixWord ++ tailWord_114701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114724 : List Nat := [2, 3, 1, 4, 2, 1, 2, 4]
def baseStart_114724 : Nat := 118140960795 + 114724 * 2 ^ 59
def prefixEnd_114724 : Nat := 4983230072969 + 3 ^ 40 * 114724 * 2
def baseEnd_114724 : Nat := 34908773100156666976237

theorem tailTrace_114724 : CollatzResearch.WordTrace tailWord_114724 prefixEnd_114724 34908773100156666976237 := by
  unfold tailWord_114724
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092164018191008072203613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2789552024254677429604817 2092164018191008072203613)
  ·
    refine ⟨784561506821628027076355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2092164018191008072203613 784561506821628027076355)
    ·
      refine ⟨1176842260232442040614533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784561506821628027076355 1176842260232442040614533)
      ·
        refine ⟨220657923793582882615225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1176842260232442040614533 220657923793582882615225)
        ·
          refine ⟨165493442845187161961419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220657923793582882615225 165493442845187161961419)
          ·
            refine ⟨248240164267780742942129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165493442845187161961419 248240164267780742942129)
            ·
              refine ⟨186180123200835557206597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248240164267780742942129 186180123200835557206597)
              ·
                refine ⟨34908773100156666976237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186180123200835557206597 34908773100156666976237)
                ·
                  rfl

theorem cell19_114724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_114724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114724 prefixEnd_114724 := by exact prefixLift 114724
  have htrace : WordTrace (prefixWord ++ tailWord_114724) baseStart_114724 baseEnd_114724 := by
    simpa [prefixWord, tailWord_114724, baseEnd_114724] using wordTrace_append hprefix tailTrace_114724
  have hstable : (prefixWord ++ tailWord_114724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114724).length < 2 ^ (prefixWord ++ tailWord_114724).sum := by decide
  have hdescent : baseEnd_114724 < baseStart_114724 := by decide
  rcases family_descends (prefixWord ++ tailWord_114724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114766 : List Nat := [4, 1, 1, 1, 1, 11]
def baseStart_114766 : Nat := 118140960795 + 114766 * 2 ^ 59
def prefixEnd_114766 : Nat := 4983230072969 + 3 ^ 40 * 114766 * 2
def baseEnd_114766 : Nat := 3880172562568112671421

theorem tailTrace_114766 : CollatzResearch.WordTrace tailWord_114766 prefixEnd_114766 3880172562568112671421 := by
  unfold tailWord_114766
  simp only [CollatzResearch.WordTrace]
  refine ⟨523232487778732164679519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2790573268153238211624101 523232487778732164679519)
  ·
    refine ⟨784848731668098247019279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 523232487778732164679519 784848731668098247019279)
    ·
      refine ⟨1177273097502147370528919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 784848731668098247019279 1177273097502147370528919)
      ·
        refine ⟨1765909646253221055793379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177273097502147370528919 1765909646253221055793379)
        ·
          refine ⟨2648864469379831583690069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765909646253221055793379 2648864469379831583690069)
          ·
            refine ⟨3880172562568112671421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2648864469379831583690069 3880172562568112671421)
            ·
              rfl

theorem cell19_114766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_114766 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114766 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114766 prefixEnd_114766 := by exact prefixLift 114766
  have htrace : WordTrace (prefixWord ++ tailWord_114766) baseStart_114766 baseEnd_114766 := by
    simpa [prefixWord, tailWord_114766, baseEnd_114766] using wordTrace_append hprefix tailTrace_114766
  have hstable : (prefixWord ++ tailWord_114766).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114766).length < 2 ^ (prefixWord ++ tailWord_114766).sum := by decide
  have hdescent : baseEnd_114766 < baseStart_114766 := by decide
  rcases family_descends (prefixWord ++ tailWord_114766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114781 : List Nat := [1, 4, 4, 1, 1, 1, 3, 4]
def baseStart_114781 : Nat := 118140960795 + 114781 * 2 ^ 59
def prefixEnd_114781 : Nat := 4983230072969 + 3 ^ 40 * 114781 * 2
def baseEnd_114781 : Nat := 34926117335597423709415

theorem tailTrace_114781 : CollatzResearch.WordTrace tailWord_114781 prefixEnd_114781 34926117335597423709415 := by
  unfold tailWord_114781
  simp only [CollatzResearch.WordTrace]
  refine ⟨4186406997175514879232197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2790937998117009919488131 4186406997175514879232197)
  ·
    refine ⟨784951311970409039856037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4186406997175514879232197 784951311970409039856037)
    ·
      refine ⟨147178370994451694973007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 784951311970409039856037 147178370994451694973007)
      ·
        refine ⟨220767556491677542459511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147178370994451694973007 220767556491677542459511)
        ·
          refine ⟨331151334737516313689267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220767556491677542459511 331151334737516313689267)
          ·
            refine ⟨496727002106274470533901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331151334737516313689267 496727002106274470533901)
            ·
              refine ⟨186272625789852926450213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 496727002106274470533901 186272625789852926450213)
              ·
                refine ⟨34926117335597423709415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186272625789852926450213 34926117335597423709415)
                ·
                  rfl

theorem cell19_114781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 4].length) (baseStart_114781 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114781 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114781 prefixEnd_114781 := by exact prefixLift 114781
  have htrace : WordTrace (prefixWord ++ tailWord_114781) baseStart_114781 baseEnd_114781 := by
    simpa [prefixWord, tailWord_114781, baseEnd_114781] using wordTrace_append hprefix tailTrace_114781
  have hstable : (prefixWord ++ tailWord_114781).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114781).length < 2 ^ (prefixWord ++ tailWord_114781).sum := by decide
  have hdescent : baseEnd_114781 < baseStart_114781 := by decide
  rcases family_descends (prefixWord ++ tailWord_114781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114855 : List Nat := [1, 1, 6, 2, 2, 2, 2, 3]
def baseStart_114855 : Nat := 118140960795 + 114855 * 2 ^ 59
def prefixEnd_114855 : Nat := 4983230072969 + 3 ^ 40 * 114855 * 2
def baseEnd_114855 : Nat := 34948634413187178064769

theorem tailTrace_114855 : CollatzResearch.WordTrace tailWord_114855 prefixEnd_114855 34948634413187178064769 := by
  unfold tailWord_114855
  simp only [CollatzResearch.WordTrace]
  refine ⟨4189105998907425517426019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2792737332604950344950679 4189105998907425517426019)
  ·
    refine ⟨6283658998361138276139029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4189105998907425517426019 6283658998361138276139029)
    ·
      refine ⟨294546515548178356694017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6283658998361138276139029 294546515548178356694017)
      ·
        refine ⟨220909886661133767520513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294546515548178356694017 220909886661133767520513)
        ·
          refine ⟨165682414995850325640385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220909886661133767520513 165682414995850325640385)
          ·
            refine ⟨124261811246887744230289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165682414995850325640385 124261811246887744230289)
            ·
              refine ⟨93196358435165808172717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124261811246887744230289 93196358435165808172717)
              ·
                refine ⟨34948634413187178064769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93196358435165808172717 34948634413187178064769)
                ·
                  rfl

theorem cell19_114855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 3].length) (baseStart_114855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114855 prefixEnd_114855 := by exact prefixLift 114855
  have htrace : WordTrace (prefixWord ++ tailWord_114855) baseStart_114855 baseEnd_114855 := by
    simpa [prefixWord, tailWord_114855, baseEnd_114855] using wordTrace_append hprefix tailTrace_114855
  have hstable : (prefixWord ++ tailWord_114855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114855).length < 2 ^ (prefixWord ++ tailWord_114855).sum := by decide
  have hdescent : baseEnd_114855 < baseStart_114855 := by decide
  rcases family_descends (prefixWord ++ tailWord_114855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114876 : List Nat := [2, 2, 2, 3, 4, 1, 5]
def baseStart_114876 : Nat := 118140960795 + 114876 * 2 ^ 59
def prefixEnd_114876 : Nat := 4983230072969 + 3 ^ 40 * 114876 * 2
def baseEnd_114876 : Nat := 11651674798221783866015

theorem tailTrace_114876 : CollatzResearch.WordTrace tailWord_114876 prefixEnd_114876 11651674798221783866015 := by
  unfold tailWord_114876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2094935965915673051970241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2793247954554230735960321 2094935965915673051970241)
  ·
    refine ⟨1571201974436754788977681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2094935965915673051970241 1571201974436754788977681)
    ·
      refine ⟨1178401480827566091733261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1571201974436754788977681 1178401480827566091733261)
      ·
        refine ⟨441900555310337284399973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1178401480827566091733261 441900555310337284399973)
        ·
          refine ⟨82856354120688240824995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 441900555310337284399973 82856354120688240824995)
          ·
            refine ⟨124284531181032361237493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82856354120688240824995 124284531181032361237493)
            ·
              refine ⟨11651674798221783866015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124284531181032361237493 11651674798221783866015)
              ·
                rfl

theorem cell19_114876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 5].length) (baseStart_114876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114876 prefixEnd_114876 := by exact prefixLift 114876
  have htrace : WordTrace (prefixWord ++ tailWord_114876) baseStart_114876 baseEnd_114876 := by
    simpa [prefixWord, tailWord_114876, baseEnd_114876] using wordTrace_append hprefix tailTrace_114876
  have hstable : (prefixWord ++ tailWord_114876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114876).length < 2 ^ (prefixWord ++ tailWord_114876).sum := by decide
  have hdescent : baseEnd_114876 < baseStart_114876 := by decide
  rcases family_descends (prefixWord ++ tailWord_114876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114880 : List Nat := [2, 1, 1, 2, 5, 1, 7]
def baseStart_114880 : Nat := 118140960795 + 114880 * 2 ^ 59
def prefixEnd_114880 : Nat := 4983230072969 + 3 ^ 40 * 114880 * 2
def baseEnd_114880 : Nat := 11652080511331509169715

theorem tailTrace_114880 : CollatzResearch.WordTrace tailWord_114880 prefixEnd_114880 11652080511331509169715 := by
  unfold tailWord_114880
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095008911908427393543047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2793345215877903191390729 2095008911908427393543047)
  ·
    refine ⟨3142513367862641090314571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2095008911908427393543047 3142513367862641090314571)
    ·
      refine ⟨4713770051793961635471857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3142513367862641090314571 4713770051793961635471857)
      ·
        refine ⟨3535327538845471226603893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4713770051793961635471857 3535327538845471226603893)
        ·
          refine ⟨331436956766762927494115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3535327538845471226603893 331436956766762927494115)
          ·
            refine ⟨497155435150144391241173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331436956766762927494115 497155435150144391241173)
            ·
              refine ⟨11652080511331509169715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 497155435150144391241173 11652080511331509169715)
              ·
                rfl

theorem cell19_114880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_114880 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114880 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114880 prefixEnd_114880 := by exact prefixLift 114880
  have htrace : WordTrace (prefixWord ++ tailWord_114880) baseStart_114880 baseEnd_114880 := by
    simpa [prefixWord, tailWord_114880, baseEnd_114880] using wordTrace_append hprefix tailTrace_114880
  have hstable : (prefixWord ++ tailWord_114880).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114880).length < 2 ^ (prefixWord ++ tailWord_114880).sum := by decide
  have hdescent : baseEnd_114880 < baseStart_114880 := by decide
  rcases family_descends (prefixWord ++ tailWord_114880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_114990 : List Nat := [4, 1, 3, 3, 1, 1, 6]
def baseStart_114990 : Nat := 118140960795 + 114990 * 2 ^ 59
def prefixEnd_114990 : Nat := 4983230072969 + 3 ^ 40 * 114990 * 2
def baseEnd_114990 : Nat := 11663237621848955021467

theorem tailTrace_114990 : CollatzResearch.WordTrace tailWord_114990 prefixEnd_114990 11663237621848955021467 := by
  unfold tailWord_114990
  simp only [CollatzResearch.WordTrace]
  refine ⟨524253731677292946698803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2796019902278895715726949 524253731677292946698803)
  ·
    refine ⟨786380597515939420048205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 524253731677292946698803 786380597515939420048205)
    ·
      refine ⟨294892724068477282518077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 786380597515939420048205 294892724068477282518077)
      ·
        refine ⟨110584771525678980944279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294892724068477282518077 110584771525678980944279)
        ·
          refine ⟨165877157288518471416419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110584771525678980944279 165877157288518471416419)
          ·
            refine ⟨248815735932777707124629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165877157288518471416419 248815735932777707124629)
            ·
              refine ⟨11663237621848955021467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 248815735932777707124629 11663237621848955021467)
              ·
                rfl

theorem cell19_114990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_114990 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_114990 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_114990 prefixEnd_114990 := by exact prefixLift 114990
  have htrace : WordTrace (prefixWord ++ tailWord_114990) baseStart_114990 baseEnd_114990 := by
    simpa [prefixWord, tailWord_114990, baseEnd_114990] using wordTrace_append hprefix tailTrace_114990
  have hstable : (prefixWord ++ tailWord_114990).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_114990).length < 2 ^ (prefixWord ++ tailWord_114990).sum := by decide
  have hdescent : baseEnd_114990 < baseStart_114990 := by decide
  rcases family_descends (prefixWord ++ tailWord_114990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115028 : List Nat := [2, 4, 1, 1, 2, 4, 2, 3]
def baseStart_115028 : Nat := 118140960795 + 115028 * 2 ^ 59
def prefixEnd_115028 : Nat := 4983230072969 + 3 ^ 40 * 115028 * 2
def baseEnd_115028 : Nat := 35001275689174036219853

theorem tailTrace_115028 : CollatzResearch.WordTrace tailWord_115028 prefixEnd_115028 35001275689174036219853 := by
  unfold tailWord_115028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2097707913640338031736869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2796943884853784042315825 2097707913640338031736869)
  ·
    refine ⟨393320233807563380950663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2097707913640338031736869 393320233807563380950663)
    ·
      refine ⟨589980350711345071425995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393320233807563380950663 589980350711345071425995)
      ·
        refine ⟨884970526067017607138993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589980350711345071425995 884970526067017607138993)
        ·
          refine ⟨663727894550263205354245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884970526067017607138993 663727894550263205354245)
          ·
            refine ⟨124448980228174351003921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663727894550263205354245 124448980228174351003921)
            ·
              refine ⟨93336735171130763252941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124448980228174351003921 93336735171130763252941)
              ·
                refine ⟨35001275689174036219853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93336735171130763252941 35001275689174036219853)
                ·
                  rfl

theorem cell19_115028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_115028 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115028 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115028 prefixEnd_115028 := by exact prefixLift 115028
  have htrace : WordTrace (prefixWord ++ tailWord_115028) baseStart_115028 baseEnd_115028 := by
    simpa [prefixWord, tailWord_115028, baseEnd_115028] using wordTrace_append hprefix tailTrace_115028
  have hstable : (prefixWord ++ tailWord_115028).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115028).length < 2 ^ (prefixWord ++ tailWord_115028).sum := by decide
  have hdescent : baseEnd_115028 < baseStart_115028 := by decide
  rcases family_descends (prefixWord ++ tailWord_115028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115110 : List Nat := [19]
def baseStart_115110 : Nat := 118140960795 + 115110 * 2 ^ 59
def prefixEnd_115110 : Nat := 4983230072969 + 3 ^ 40 * 115110 * 2
def baseEnd_115110 : Nat := 16015650226530472061

theorem tailTrace_115110 : CollatzResearch.WordTrace tailWord_115110 prefixEnd_115110 16015650226530472061 := by
  unfold tailWord_115110
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015650226530472061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 19 2798937741989069378639189 16015650226530472061)
  ·
    rfl

theorem cell19_115110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 19].length) (baseStart_115110 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115110 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115110 prefixEnd_115110 := by exact prefixLift 115110
  have htrace : WordTrace (prefixWord ++ tailWord_115110) baseStart_115110 baseEnd_115110 := by
    simpa [prefixWord, tailWord_115110, baseEnd_115110] using wordTrace_append hprefix tailTrace_115110
  have hstable : (prefixWord ++ tailWord_115110).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115110).length < 2 ^ (prefixWord ++ tailWord_115110).sum := by decide
  have hdescent : baseEnd_115110 < baseStart_115110 := by decide
  rcases family_descends (prefixWord ++ tailWord_115110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115127 : List Nat := [1, 1, 3, 1, 3, 3, 3, 4]
def baseStart_115127 : Nat := 118140960795 + 115127 * 2 ^ 59
def prefixEnd_115127 : Nat := 4983230072969 + 3 ^ 40 * 115127 * 2
def baseEnd_115127 : Nat := 35031399887571140019583

theorem tailTrace_115127 : CollatzResearch.WordTrace tailWord_115127 prefixEnd_115127 35031399887571140019583 := by
  unfold tailWord_115127
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199026653922015971327635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2799351102614677314218423 4199026653922015971327635)
  ·
    refine ⟨6298539980883023956991453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4199026653922015971327635 6298539980883023956991453)
    ·
      refine ⟨2361952492831133983871795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6298539980883023956991453 2361952492831133983871795)
      ·
        refine ⟨3542928739246700975807693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361952492831133983871795 3542928739246700975807693)
        ·
          refine ⟨1328598277217512865927885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3542928739246700975807693 1328598277217512865927885)
          ·
            refine ⟨498224353956567324722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1328598277217512865927885 498224353956567324722957)
            ·
              refine ⟨186834132733712746771109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 498224353956567324722957 186834132733712746771109)
              ·
                refine ⟨35031399887571140019583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186834132733712746771109 35031399887571140019583)
                ·
                  rfl

theorem cell19_115127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 4].length) (baseStart_115127 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115127 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115127 prefixEnd_115127 := by exact prefixLift 115127
  have htrace : WordTrace (prefixWord ++ tailWord_115127) baseStart_115127 baseEnd_115127 := by
    simpa [prefixWord, tailWord_115127, baseEnd_115127] using wordTrace_append hprefix tailTrace_115127
  have hstable : (prefixWord ++ tailWord_115127).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115127).length < 2 ^ (prefixWord ++ tailWord_115127).sum := by decide
  have hdescent : baseEnd_115127 < baseStart_115127 := by decide
  rcases family_descends (prefixWord ++ tailWord_115127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115144 : List Nat := [2, 1, 3, 1, 3, 3, 3, 3]
def baseStart_115144 : Nat := 118140960795 + 115144 * 2 ^ 59
def prefixEnd_115144 : Nat := 4983230072969 + 3 ^ 40 * 115144 * 2
def baseEnd_115144 : Nat := 35036572729720137641759

theorem tailTrace_115144 : CollatzResearch.WordTrace tailWord_115144 prefixEnd_115144 35036572729720137641759 := by
  unfold tailWord_115144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2099823347430213937348243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2799764463240285249797657 2099823347430213937348243)
  ·
    refine ⟨3149735021145320906022365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2099823347430213937348243 3149735021145320906022365)
    ·
      refine ⟨1181150632929495339758387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3149735021145320906022365 1181150632929495339758387)
      ·
        refine ⟨1771725949394243009637581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1181150632929495339758387 1771725949394243009637581)
        ·
          refine ⟨664397231022841128614093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1771725949394243009637581 664397231022841128614093)
          ·
            refine ⟨249148961633565423230285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 664397231022841128614093 249148961633565423230285)
            ·
              refine ⟨93430860612587033711357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 249148961633565423230285 93430860612587033711357)
              ·
                refine ⟨35036572729720137641759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93430860612587033711357 35036572729720137641759)
                ·
                  rfl

theorem cell19_115144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_115144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115144 prefixEnd_115144 := by exact prefixLift 115144
  have htrace : WordTrace (prefixWord ++ tailWord_115144) baseStart_115144 baseEnd_115144 := by
    simpa [prefixWord, tailWord_115144, baseEnd_115144] using wordTrace_append hprefix tailTrace_115144
  have hstable : (prefixWord ++ tailWord_115144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115144).length < 2 ^ (prefixWord ++ tailWord_115144).sum := by decide
  have hdescent : baseEnd_115144 < baseStart_115144 := by decide
  rcases family_descends (prefixWord ++ tailWord_115144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115165 : List Nat := [1, 4, 3, 1, 1, 1, 8]
def baseStart_115165 : Nat := 118140960795 + 115165 * 2 ^ 59
def prefixEnd_115165 : Nat := 4983230072969 + 3 ^ 40 * 115165 * 2
def baseEnd_115165 : Nat := 11680987570399437058345

theorem tailTrace_115165 : CollatzResearch.WordTrace tailWord_115165 prefixEnd_115165 11680987570399437058345 := by
  unfold tailWord_115165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4200412627784348461210949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2800275085189565640807299 4200412627784348461210949)
  ·
    refine ⟨787577367709565336477053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4200412627784348461210949 787577367709565336477053)
    ·
      refine ⟨295341512891087001178895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 787577367709565336477053 295341512891087001178895)
      ·
        refine ⟨443012269336630501768343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 295341512891087001178895 443012269336630501768343)
        ·
          refine ⟨664518404004945752652515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 443012269336630501768343 664518404004945752652515)
          ·
            refine ⟨996777606007418628978773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664518404004945752652515 996777606007418628978773)
            ·
              refine ⟨11680987570399437058345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 996777606007418628978773 11680987570399437058345)
              ·
                rfl

theorem cell19_115165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 8].length) (baseStart_115165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115165 prefixEnd_115165 := by exact prefixLift 115165
  have htrace : WordTrace (prefixWord ++ tailWord_115165) baseStart_115165 baseEnd_115165 := by
    simpa [prefixWord, tailWord_115165, baseEnd_115165] using wordTrace_append hprefix tailTrace_115165
  have hstable : (prefixWord ++ tailWord_115165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115165).length < 2 ^ (prefixWord ++ tailWord_115165).sum := by decide
  have hdescent : baseEnd_115165 < baseStart_115165 := by decide
  rcases family_descends (prefixWord ++ tailWord_115165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115201 : List Nat := [1, 2, 4, 1, 3, 1, 4, 3]
def baseStart_115201 : Nat := 118140960795 + 115201 * 2 ^ 59
def prefixEnd_115201 : Nat := 4983230072969 + 3 ^ 40 * 115201 * 2
def baseEnd_115201 : Nat := 35053916965160894374937

theorem tailTrace_115201 : CollatzResearch.WordTrace tailWord_115201 prefixEnd_115201 35053916965160894374937 := by
  unfold tailWord_115201
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201725655653926609521457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2801150437102617739680971 4201725655653926609521457)
  ·
    refine ⟨3151294241740444957141093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4201725655653926609521457 3151294241740444957141093)
    ·
      refine ⟨590867670326333429463955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3151294241740444957141093 590867670326333429463955)
      ·
        refine ⟨886301505489500144195933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590867670326333429463955 886301505489500144195933)
        ·
          refine ⟨332363064558562554073475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886301505489500144195933 332363064558562554073475)
          ·
            refine ⟨498544596837843831110213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332363064558562554073475 498544596837843831110213)
            ·
              refine ⟨93477111907095718333165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 498544596837843831110213 93477111907095718333165)
              ·
                refine ⟨35053916965160894374937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93477111907095718333165 35053916965160894374937)
                ·
                  rfl

theorem cell19_115201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 3].length) (baseStart_115201 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115201 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115201 prefixEnd_115201 := by exact prefixLift 115201
  have htrace : WordTrace (prefixWord ++ tailWord_115201) baseStart_115201 baseEnd_115201 := by
    simpa [prefixWord, tailWord_115201, baseEnd_115201] using wordTrace_append hprefix tailTrace_115201
  have hstable : (prefixWord ++ tailWord_115201).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115201).length < 2 ^ (prefixWord ++ tailWord_115201).sum := by decide
  have hdescent : baseEnd_115201 < baseStart_115201 := by decide
  rcases family_descends (prefixWord ++ tailWord_115201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115220 : List Nat := [2, 4, 3, 1, 1, 1, 7]
def baseStart_115220 : Nat := 118140960795 + 115220 * 2 ^ 59
def prefixEnd_115220 : Nat := 4983230072969 + 3 ^ 40 * 115220 * 2
def baseEnd_115220 : Nat := 11686566125658159984221

theorem tailTrace_115220 : CollatzResearch.WordTrace tailWord_115220 prefixEnd_115220 11686566125658159984221 := by
  unfold tailWord_115220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101209321292546427231557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2801612428390061902975409 2101209321292546427231557)
  ·
    refine ⟨393976747742352455105917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2101209321292546427231557 393976747742352455105917)
    ·
      refine ⟨147741280403382170664719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393976747742352455105917 147741280403382170664719)
      ·
        refine ⟨221611920605073255997079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147741280403382170664719 221611920605073255997079)
        ·
          refine ⟨332417880907609883995619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221611920605073255997079 332417880907609883995619)
          ·
            refine ⟨498626821361414825993429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332417880907609883995619 498626821361414825993429)
            ·
              refine ⟨11686566125658159984221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 498626821361414825993429 11686566125658159984221)
              ·
                rfl

theorem cell19_115220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_115220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115220 prefixEnd_115220 := by exact prefixLift 115220
  have htrace : WordTrace (prefixWord ++ tailWord_115220) baseStart_115220 baseEnd_115220 := by
    simpa [prefixWord, tailWord_115220, baseEnd_115220] using wordTrace_append hprefix tailTrace_115220
  have hstable : (prefixWord ++ tailWord_115220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115220).length < 2 ^ (prefixWord ++ tailWord_115220).sum := by decide
  have hdescent : baseEnd_115220 < baseStart_115220 := by decide
  rcases family_descends (prefixWord ++ tailWord_115220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115260 : List Nat := [2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_115260 : Nat := 118140960795 + 115260 * 2 ^ 59
def prefixEnd_115260 : Nat := 4983230072969 + 3 ^ 40 * 115260 * 2
def baseEnd_115260 : Nat := 35071869770266239063665

theorem tailTrace_115260 : CollatzResearch.WordTrace tailWord_115260 prefixEnd_115260 35071869770266239063665 := by
  unfold tailWord_115260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2101938781220089842959617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2802585041626786457279489 2101938781220089842959617)
  ·
    refine ⟨1576454085915067382219713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2101938781220089842959617 1576454085915067382219713)
    ·
      refine ⟨1182340564436300536664785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1576454085915067382219713 1182340564436300536664785)
      ·
        refine ⟨886755423327225402498589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182340564436300536664785 886755423327225402498589)
        ·
          refine ⟨332533283747709525936971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 886755423327225402498589 332533283747709525936971)
          ·
            refine ⟨498799925621564288905457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 332533283747709525936971 498799925621564288905457)
            ·
              refine ⟨374099944216173216679093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 498799925621564288905457 374099944216173216679093)
              ·
                refine ⟨35071869770266239063665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374099944216173216679093 35071869770266239063665)
                ·
                  rfl

theorem cell19_115260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_115260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115260 prefixEnd_115260 := by exact prefixLift 115260
  have htrace : WordTrace (prefixWord ++ tailWord_115260) baseStart_115260 baseEnd_115260 := by
    simpa [prefixWord, tailWord_115260, baseEnd_115260] using wordTrace_append hprefix tailTrace_115260
  have hstable : (prefixWord ++ tailWord_115260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115260).length < 2 ^ (prefixWord ++ tailWord_115260).sum := by decide
  have hdescent : baseEnd_115260 < baseStart_115260 := by decide
  rcases family_descends (prefixWord ++ tailWord_115260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115281 : List Nat := [1, 2, 2, 1, 3, 10]
def baseStart_115281 : Nat := 118140960795 + 115281 * 2 ^ 59
def prefixEnd_115281 : Nat := 4983230072969 + 3 ^ 40 * 115281 * 2
def baseEnd_115281 : Nat := 3897584416860490288549

theorem tailTrace_115281 : CollatzResearch.WordTrace tailWord_115281 prefixEnd_115281 3897584416860490288549 := by
  unfold tailWord_115281
  simp only [CollatzResearch.WordTrace]
  refine ⟨4204643495364100272433697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2803095663576066848289131 4204643495364100272433697)
  ·
    refine ⟨3153482621523075204325273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4204643495364100272433697 3153482621523075204325273)
    ·
      refine ⟨2365111966142306403243955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3153482621523075204325273 2365111966142306403243955)
      ·
        refine ⟨3547667949213459604865933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365111966142306403243955 3547667949213459604865933)
        ·
          refine ⟨1330375480955047351824725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547667949213459604865933 1330375480955047351824725)
          ·
            refine ⟨3897584416860490288549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1330375480955047351824725 3897584416860490288549)
            ·
              rfl

theorem cell19_115281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 10].length) (baseStart_115281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115281 prefixEnd_115281 := by exact prefixLift 115281
  have htrace : WordTrace (prefixWord ++ tailWord_115281) baseStart_115281 baseEnd_115281 := by
    simpa [prefixWord, tailWord_115281, baseEnd_115281] using wordTrace_append hprefix tailTrace_115281
  have hstable : (prefixWord ++ tailWord_115281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115281).length < 2 ^ (prefixWord ++ tailWord_115281).sum := by decide
  have hdescent : baseEnd_115281 < baseStart_115281 := by decide
  rcases family_descends (prefixWord ++ tailWord_115281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115319 : List Nat := [1, 1, 3, 1, 1, 3, 2, 7]
def baseStart_115319 : Nat := 118140960795 + 115319 * 2 ^ 59
def prefixEnd_115319 : Nat := 4983230072969 + 3 ^ 40 * 115319 * 2
def baseEnd_115319 : Nat := 35089822575371583752393

theorem tailTrace_115319 : CollatzResearch.WordTrace tailWord_115319 prefixEnd_115319 35089822575371583752393 := by
  unfold tailWord_115319
  simp only [CollatzResearch.WordTrace]
  refine ⟨4206029469226432762317011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2804019646150955174878007 4206029469226432762317011)
  ·
    refine ⟨6309044203839649143475517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4206029469226432762317011 6309044203839649143475517)
    ·
      refine ⟨2365891576439868428803319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6309044203839649143475517 2365891576439868428803319)
      ·
        refine ⟨3548837364659802643204979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365891576439868428803319 3548837364659802643204979)
        ·
          refine ⟨5323256046989703964807469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548837364659802643204979 5323256046989703964807469)
          ·
            refine ⟨1996221017621138986802801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5323256046989703964807469 1996221017621138986802801)
            ·
              refine ⟨1497165763215854240102101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996221017621138986802801 1497165763215854240102101)
              ·
                refine ⟨35089822575371583752393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1497165763215854240102101 35089822575371583752393)
                ·
                  rfl

theorem cell19_115319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_115319 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115319 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115319 prefixEnd_115319 := by exact prefixLift 115319
  have htrace : WordTrace (prefixWord ++ tailWord_115319) baseStart_115319 baseEnd_115319 := by
    simpa [prefixWord, tailWord_115319, baseEnd_115319] using wordTrace_append hprefix tailTrace_115319
  have hstable : (prefixWord ++ tailWord_115319).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115319).length < 2 ^ (prefixWord ++ tailWord_115319).sum := by decide
  have hdescent : baseEnd_115319 < baseStart_115319 := by decide
  rcases family_descends (prefixWord ++ tailWord_115319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115330 : List Nat := [3, 4, 3, 1, 1, 1, 6]
def baseStart_115330 : Nat := 118140960795 + 115330 * 2 ^ 59
def prefixEnd_115330 : Nat := 4983230072969 + 3 ^ 40 * 115330 * 2
def baseEnd_115330 : Nat := 11697723236175605835973

theorem tailTrace_115330 : CollatzResearch.WordTrace tailWord_115330 prefixEnd_115330 11697723236175605835973 := by
  unfold tailWord_115330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051607668046645410241861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2804287114791054427311629 1051607668046645410241861)
  ·
    refine ⟨197176437758746014420349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1051607668046645410241861 197176437758746014420349)
    ·
      refine ⟨73941164159529755407631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 197176437758746014420349 73941164159529755407631)
      ·
        refine ⟨110911746239294633111447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73941164159529755407631 110911746239294633111447)
        ·
          refine ⟨166367619358941949667171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110911746239294633111447 166367619358941949667171)
          ·
            refine ⟨249551429038412924500757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166367619358941949667171 249551429038412924500757)
            ·
              refine ⟨11697723236175605835973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 249551429038412924500757 11697723236175605835973)
              ·
                rfl

theorem cell19_115330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 6].length) (baseStart_115330 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115330 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115330 prefixEnd_115330 := by exact prefixLift 115330
  have htrace : WordTrace (prefixWord ++ tailWord_115330) baseStart_115330 baseEnd_115330 := by
    simpa [prefixWord, tailWord_115330, baseEnd_115330] using wordTrace_append hprefix tailTrace_115330
  have hstable : (prefixWord ++ tailWord_115330).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115330).length < 2 ^ (prefixWord ++ tailWord_115330).sum := by decide
  have hdescent : baseEnd_115330 < baseStart_115330 := by decide
  rcases family_descends (prefixWord ++ tailWord_115330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115370 : List Nat := [3, 1, 5, 2, 1, 1, 1, 5]
def baseStart_115370 : Nat := 118140960795 + 115370 * 2 ^ 59
def prefixEnd_115370 : Nat := 4983230072969 + 3 ^ 40 * 115370 * 2
def baseEnd_115370 : Nat := 35105341101818576618921

theorem tailTrace_115370 : CollatzResearch.WordTrace tailWord_115370 prefixEnd_115370 35105341101818576618921 := by
  unfold tailWord_115370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1051972398010417118105891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2805259728027778981615709 1051972398010417118105891)
  ·
    refine ⟨1577958597015625677158837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1051972398010417118105891 1577958597015625677158837)
    ·
      refine ⟨147933618470214907233641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1577958597015625677158837 147933618470214907233641)
      ·
        refine ⟨110950213852661180425231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147933618470214907233641 110950213852661180425231)
        ·
          refine ⟨166425320778991770637847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110950213852661180425231 166425320778991770637847)
          ·
            refine ⟨249637981168487655956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166425320778991770637847 249637981168487655956771)
            ·
              refine ⟨374456971752731483935157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 249637981168487655956771 374456971752731483935157)
              ·
                refine ⟨35105341101818576618921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374456971752731483935157 35105341101818576618921)
                ·
                  rfl

theorem cell19_115370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_115370 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115370 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115370 prefixEnd_115370 := by exact prefixLift 115370
  have htrace : WordTrace (prefixWord ++ tailWord_115370) baseStart_115370 baseEnd_115370 := by
    simpa [prefixWord, tailWord_115370, baseEnd_115370] using wordTrace_append hprefix tailTrace_115370
  have hstable : (prefixWord ++ tailWord_115370).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115370).length < 2 ^ (prefixWord ++ tailWord_115370).sum := by decide
  have hdescent : baseEnd_115370 < baseStart_115370 := by decide
  rcases family_descends (prefixWord ++ tailWord_115370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115410 : List Nat := [3, 2, 2, 2, 3, 1, 2, 4]
def baseStart_115410 : Nat := 118140960795 + 115410 * 2 ^ 59
def prefixEnd_115410 : Nat := 4983230072969 + 3 ^ 40 * 115410 * 2
def baseEnd_115410 : Nat := 35117512495110335729923

theorem tailTrace_115410 : CollatzResearch.WordTrace tailWord_115410 prefixEnd_115410 35117512495110335729923 := by
  unfold tailWord_115410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1052337127974188825969921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2806232341264503535919789 1052337127974188825969921)
  ·
    refine ⟨789252845980641619477441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1052337127974188825969921 789252845980641619477441)
    ·
      refine ⟨591939634485481214608081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 789252845980641619477441 591939634485481214608081)
      ·
        refine ⟨443954725864110910956061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 591939634485481214608081 443954725864110910956061)
        ·
          refine ⟨166483022199041591608523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 443954725864110910956061 166483022199041591608523)
          ·
            refine ⟨249724533298562387412785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 166483022199041591608523 249724533298562387412785)
            ·
              refine ⟨187293399973921790559589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 249724533298562387412785 187293399973921790559589)
              ·
                refine ⟨35117512495110335729923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187293399973921790559589 35117512495110335729923)
                ·
                  rfl

theorem cell19_115410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_115410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115410 prefixEnd_115410 := by exact prefixLift 115410
  have htrace : WordTrace (prefixWord ++ tailWord_115410) baseStart_115410 baseEnd_115410 := by
    simpa [prefixWord, tailWord_115410, baseEnd_115410] using wordTrace_append hprefix tailTrace_115410
  have hstable : (prefixWord ++ tailWord_115410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115410).length < 2 ^ (prefixWord ++ tailWord_115410).sum := by decide
  have hdescent : baseEnd_115410 < baseStart_115410 := by decide
  rcases family_descends (prefixWord ++ tailWord_115410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115433 : List Nat := [1, 2, 1, 1, 1, 2, 6, 5]
def baseStart_115433 : Nat := 118140960795 + 115433 * 2 ^ 59
def prefixEnd_115433 : Nat := 4983230072969 + 3 ^ 40 * 115433 * 2
def baseEnd_115433 : Nat := 35124511046253097218749

theorem tailTrace_115433 : CollatzResearch.WordTrace tailWord_115433 prefixEnd_115433 35124511046253097218749 := by
  unfold tailWord_115433
  simp only [CollatzResearch.WordTrace]
  refine ⟨4210187390813430231966953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2806791593875620154644635 4210187390813430231966953)
  ·
    refine ⟨3157640543110072673975215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4210187390813430231966953 3157640543110072673975215)
    ·
      refine ⟨4736460814665109010962823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3157640543110072673975215 4736460814665109010962823)
      ·
        refine ⟨7104691221997663516444235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4736460814665109010962823 7104691221997663516444235)
        ·
          refine ⟨10657036832996495274666353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104691221997663516444235 10657036832996495274666353)
          ·
            refine ⟨7992777624747371455999765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10657036832996495274666353 7992777624747371455999765)
            ·
              refine ⟨374661451160033036999989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7992777624747371455999765 374661451160033036999989)
              ·
                refine ⟨35124511046253097218749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 374661451160033036999989 35124511046253097218749)
                ·
                  rfl

theorem cell19_115433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_115433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115433 prefixEnd_115433 := by exact prefixLift 115433
  have htrace : WordTrace (prefixWord ++ tailWord_115433) baseStart_115433 baseEnd_115433 := by
    simpa [prefixWord, tailWord_115433, baseEnd_115433] using wordTrace_append hprefix tailTrace_115433
  have hstable : (prefixWord ++ tailWord_115433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115433).length < 2 ^ (prefixWord ++ tailWord_115433).sum := by decide
  have hdescent : baseEnd_115433 < baseStart_115433 := by decide
  rcases family_descends (prefixWord ++ tailWord_115433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115452 : List Nat := [2, 2, 2, 1, 3, 9]
def baseStart_115452 : Nat := 118140960795 + 115452 * 2 ^ 59
def prefixEnd_115452 : Nat := 4983230072969 + 3 ^ 40 * 115452 * 2
def baseEnd_115452 : Nat := 3903365828674075866275

theorem tailTrace_115452 : CollatzResearch.WordTrace tailWord_115452 prefixEnd_115452 3903365828674075866275 := by
  unfold tailWord_115452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2105440188872298238454305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2807253585163064317939073 2105440188872298238454305)
  ·
    refine ⟨1579080141654223678840729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2105440188872298238454305 1579080141654223678840729)
    ·
      refine ⟨1184310106240667759130547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1579080141654223678840729 1184310106240667759130547)
      ·
        refine ⟨1776465159361001638695821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184310106240667759130547 1776465159361001638695821)
        ·
          refine ⟨666174434760375614510933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776465159361001638695821 666174434760375614510933)
          ·
            refine ⟨3903365828674075866275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 666174434760375614510933 3903365828674075866275)
            ·
              rfl

theorem cell19_115452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_115452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115452 prefixEnd_115452 := by exact prefixLift 115452
  have htrace : WordTrace (prefixWord ++ tailWord_115452) baseStart_115452 baseEnd_115452 := by
    simpa [prefixWord, tailWord_115452, baseEnd_115452] using wordTrace_append hprefix tailTrace_115452
  have hstable : (prefixWord ++ tailWord_115452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115452).length < 2 ^ (prefixWord ++ tailWord_115452).sum := by decide
  have hdescent : baseEnd_115452 < baseStart_115452 := by decide
  rcases family_descends (prefixWord ++ tailWord_115452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115528 : List Nat := [2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_115528 : Nat := 118140960795 + 115528 * 2 ^ 59
def prefixEnd_115528 : Nat := 4983230072969 + 3 ^ 40 * 115528 * 2
def baseEnd_115528 : Nat := 35153418105321025107379

theorem tailTrace_115528 : CollatzResearch.WordTrace tailWord_115528 prefixEnd_115528 35153418105321025107379 := by
  unfold tailWord_115528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2106826162734630728337619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2809101550312840971116825 2106826162734630728337619)
  ·
    refine ⟨3160239244101946092506429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2106826162734630728337619 3160239244101946092506429)
    ·
      refine ⟨1185089716538229784689911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3160239244101946092506429 1185089716538229784689911)
      ·
        refine ⟨1777634574807344677034867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185089716538229784689911 1777634574807344677034867)
        ·
          refine ⟨2666451862211017015552301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777634574807344677034867 2666451862211017015552301)
          ·
            refine ⟨999919448329131380832113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2666451862211017015552301 999919448329131380832113)
            ·
              refine ⟨749939586246848535624085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999919448329131380832113 749939586246848535624085)
              ·
                refine ⟨35153418105321025107379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 749939586246848535624085 35153418105321025107379)
                ·
                  rfl

theorem cell19_115528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_115528 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115528 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115528 prefixEnd_115528 := by exact prefixLift 115528
  have htrace : WordTrace (prefixWord ++ tailWord_115528) baseStart_115528 baseEnd_115528 := by
    simpa [prefixWord, tailWord_115528, baseEnd_115528] using wordTrace_append hprefix tailTrace_115528
  have hstable : (prefixWord ++ tailWord_115528).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115528).length < 2 ^ (prefixWord ++ tailWord_115528).sum := by decide
  have hdescent : baseEnd_115528 < baseStart_115528 := by decide
  rcases family_descends (prefixWord ++ tailWord_115528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115543 : List Nat := [1, 1, 3, 2, 4, 3, 2, 3]
def baseStart_115543 : Nat := 118140960795 + 115543 * 2 ^ 59
def prefixEnd_115543 : Nat := 4983230072969 + 3 ^ 40 * 115543 * 2
def baseEnd_115543 : Nat := 35157982377805434774005

theorem tailTrace_115543 : CollatzResearch.WordTrace tailWord_115543 prefixEnd_115543 35157982377805434774005 := by
  unfold tailWord_115543
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214199420414919018471283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2809466280276612678980855 4214199420414919018471283)
  ·
    refine ⟨6321299130622378527706925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4214199420414919018471283 6321299130622378527706925)
    ·
      refine ⟨2370487173983391947890097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6321299130622378527706925 2370487173983391947890097)
      ·
        refine ⟨1777865380487543960917573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2370487173983391947890097 1777865380487543960917573)
        ·
          refine ⟨333349758841414492672045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1777865380487543960917573 333349758841414492672045)
          ·
            refine ⟨125006159565530434752017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333349758841414492672045 125006159565530434752017)
            ·
              refine ⟨93754619674147826064013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125006159565530434752017 93754619674147826064013)
              ·
                refine ⟨35157982377805434774005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93754619674147826064013 35157982377805434774005)
                ·
                  rfl

theorem cell19_115543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 3].length) (baseStart_115543 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115543 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115543 prefixEnd_115543 := by exact prefixLift 115543
  have htrace : WordTrace (prefixWord ++ tailWord_115543) baseStart_115543 baseEnd_115543 := by
    simpa [prefixWord, tailWord_115543, baseEnd_115543] using wordTrace_append hprefix tailTrace_115543
  have hstable : (prefixWord ++ tailWord_115543).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115543).length < 2 ^ (prefixWord ++ tailWord_115543).sum := by decide
  have hdescent : baseEnd_115543 < baseStart_115543 := by decide
  rcases family_descends (prefixWord ++ tailWord_115543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115545 : List Nat := [1, 2, 1, 2, 2, 4, 4, 3]
def baseStart_115545 : Nat := 118140960795 + 115545 * 2 ^ 59
def prefixEnd_115545 : Nat := 4983230072969 + 3 ^ 40 * 115545 * 2
def baseEnd_115545 : Nat := 35158590947470022729555

theorem tailTrace_115545 : CollatzResearch.WordTrace tailWord_115545 prefixEnd_115545 35158590947470022729555 := by
  unfold tailWord_115545
  simp only [CollatzResearch.WordTrace]
  refine ⟨4214272366407673360044089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2809514910938448906696059 4214272366407673360044089)
  ·
    refine ⟨3160704274805755020033067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4214272366407673360044089 3160704274805755020033067)
    ·
      refine ⟨4741056412208632530049601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3160704274805755020033067 4741056412208632530049601)
      ·
        refine ⟨3555792309156474397537201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4741056412208632530049601 3555792309156474397537201)
        ·
          refine ⟨2666844231867355798152901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555792309156474397537201 2666844231867355798152901)
          ·
            refine ⟨500033293475129212153669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2666844231867355798152901 500033293475129212153669)
            ·
              refine ⟨93756242526586727278813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 500033293475129212153669 93756242526586727278813)
              ·
                refine ⟨35158590947470022729555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93756242526586727278813 35158590947470022729555)
                ·
                  rfl

theorem cell19_115545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 4, 3].length) (baseStart_115545 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115545 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115545 prefixEnd_115545 := by exact prefixLift 115545
  have htrace : WordTrace (prefixWord ++ tailWord_115545) baseStart_115545 baseEnd_115545 := by
    simpa [prefixWord, tailWord_115545, baseEnd_115545] using wordTrace_append hprefix tailTrace_115545
  have hstable : (prefixWord ++ tailWord_115545).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115545).length < 2 ^ (prefixWord ++ tailWord_115545).sum := by decide
  have hdescent : baseEnd_115545 < baseStart_115545 := by decide
  rcases family_descends (prefixWord ++ tailWord_115545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115623 : List Nat := [1, 1, 6, 1, 10]
def baseStart_115623 : Nat := 118140960795 + 115623 * 2 ^ 59
def prefixEnd_115623 : Nat := 4983230072969 + 3 ^ 40 * 115623 * 2
def baseEnd_115623 : Nat := 1303049080162553814667

theorem tailTrace_115623 : CollatzResearch.WordTrace tailWord_115623 prefixEnd_115623 1303049080162553814667 := by
  unfold tailWord_115623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4217117260125092681383523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2811411506750061787589015 4217117260125092681383523)
  ·
    refine ⟨6325675890187639022075285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4217117260125092681383523 6325675890187639022075285)
    ·
      refine ⟨296516057352545579159779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6325675890187639022075285 296516057352545579159779)
      ·
        refine ⟨444774086028818368739669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 296516057352545579159779 444774086028818368739669)
        ·
          refine ⟨1303049080162553814667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 444774086028818368739669 1303049080162553814667)
          ·
            rfl

theorem cell19_115623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_115623 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115623 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115623 prefixEnd_115623 := by exact prefixLift 115623
  have htrace : WordTrace (prefixWord ++ tailWord_115623) baseStart_115623 baseEnd_115623 := by
    simpa [prefixWord, tailWord_115623, baseEnd_115623] using wordTrace_append hprefix tailTrace_115623
  have hstable : (prefixWord ++ tailWord_115623).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115623).length < 2 ^ (prefixWord ++ tailWord_115623).sum := by decide
  have hdescent : baseEnd_115623 < baseStart_115623 := by decide
  rcases family_descends (prefixWord ++ tailWord_115623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115636 : List Nat := [2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_115636 : Nat := 118140960795 + 115636 * 2 ^ 59
def prefixEnd_115636 : Nat := 4983230072969 + 3 ^ 40 * 115636 * 2
def baseEnd_115636 : Nat := 35186280867208774707085

theorem tailTrace_115636 : CollatzResearch.WordTrace tailWord_115636 prefixEnd_115636 35186280867208774707085 := by
  unfold tailWord_115636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108795704538997950803381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2811727606051997267737841 2108795704538997950803381)
  ·
    refine ⟨197699597300531057887817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2108795704538997950803381 197699597300531057887817)
    ·
      refine ⟨148274697975398293415863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 197699597300531057887817 148274697975398293415863)
      ·
        refine ⟨222412046963097440123795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148274697975398293415863 222412046963097440123795)
        ·
          refine ⟨333618070444646160185693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222412046963097440123795 333618070444646160185693)
          ·
            refine ⟨125106776416742310069635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333618070444646160185693 125106776416742310069635)
            ·
              refine ⟨187660164625113465104453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125106776416742310069635 187660164625113465104453)
              ·
                refine ⟨35186280867208774707085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187660164625113465104453 35186280867208774707085)
                ·
                  rfl

theorem cell19_115636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_115636 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115636 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115636 prefixEnd_115636 := by exact prefixLift 115636
  have htrace : WordTrace (prefixWord ++ tailWord_115636) baseStart_115636 baseEnd_115636 := by
    simpa [prefixWord, tailWord_115636, baseEnd_115636] using wordTrace_append hprefix tailTrace_115636
  have hstable : (prefixWord ++ tailWord_115636).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115636).length < 2 ^ (prefixWord ++ tailWord_115636).sum := by decide
  have hdescent : baseEnd_115636 < baseStart_115636 := by decide
  rcases family_descends (prefixWord ++ tailWord_115636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115640 : List Nat := [2, 1, 2, 1, 2, 6, 1, 4]
def baseStart_115640 : Nat := 118140960795 + 115640 * 2 ^ 59
def prefixEnd_115640 : Nat := 4983230072969 + 3 ^ 40 * 115640 * 2
def baseEnd_115640 : Nat := 35187498006537950618185

theorem tailTrace_115640 : CollatzResearch.WordTrace tailWord_115640 prefixEnd_115640 35187498006537950618185 := by
  unfold tailWord_115640
  simp only [CollatzResearch.WordTrace]
  refine ⟨2108868650531752292376187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2811824867375669723168249 2108868650531752292376187)
  ·
    refine ⟨3163302975797628438564281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2108868650531752292376187 3163302975797628438564281)
    ·
      refine ⟨2372477231848221328923211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3163302975797628438564281 2372477231848221328923211)
      ·
        refine ⟨3558715847772331993384817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2372477231848221328923211 3558715847772331993384817)
        ·
          refine ⟨2669036885829248995038613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558715847772331993384817 2669036885829248995038613)
          ·
            refine ⟨125111104023246046642435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2669036885829248995038613 125111104023246046642435)
            ·
              refine ⟨187666656034869069963653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125111104023246046642435 187666656034869069963653)
              ·
                refine ⟨35187498006537950618185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187666656034869069963653 35187498006537950618185)
                ·
                  rfl

theorem cell19_115640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_115640 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115640 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115640 prefixEnd_115640 := by exact prefixLift 115640
  have htrace : WordTrace (prefixWord ++ tailWord_115640) baseStart_115640 baseEnd_115640 := by
    simpa [prefixWord, tailWord_115640, baseEnd_115640] using wordTrace_append hprefix tailTrace_115640
  have hstable : (prefixWord ++ tailWord_115640).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115640).length < 2 ^ (prefixWord ++ tailWord_115640).sum := by decide
  have hdescent : baseEnd_115640 < baseStart_115640 := by decide
  rcases family_descends (prefixWord ++ tailWord_115640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115659 : List Nat := [1, 1, 1, 1, 3, 6, 3, 3]
def baseStart_115659 : Nat := 118140960795 + 115659 * 2 ^ 59
def prefixEnd_115659 : Nat := 4983230072969 + 3 ^ 40 * 115659 * 2
def baseEnd_115659 : Nat := 35193279418351536195911

theorem tailTrace_115659 : CollatzResearch.WordTrace tailWord_115659 prefixEnd_115659 35193279418351536195911 := by
  unfold tailWord_115659
  simp only [CollatzResearch.WordTrace]
  refine ⟨4218430287994670829694031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2812286858663113886462687 4218430287994670829694031)
  ·
    refine ⟨6327645431992006244541047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4218430287994670829694031 6327645431992006244541047)
    ·
      refine ⟨9491468147988009366811571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6327645431992006244541047 9491468147988009366811571)
      ·
        refine ⟨14237202221982014050217357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9491468147988009366811571 14237202221982014050217357)
        ·
          refine ⟨5338950833243255268831509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14237202221982014050217357 5338950833243255268831509)
          ·
            refine ⟨250263320308277590726477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5338950833243255268831509 250263320308277590726477)
            ·
              refine ⟨93848745115604096522429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 250263320308277590726477 93848745115604096522429)
              ·
                refine ⟨35193279418351536195911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93848745115604096522429 35193279418351536195911)
                ·
                  rfl

theorem cell19_115659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 3].length) (baseStart_115659 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115659 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115659 prefixEnd_115659 := by exact prefixLift 115659
  have htrace : WordTrace (prefixWord ++ tailWord_115659) baseStart_115659 baseEnd_115659 := by
    simpa [prefixWord, tailWord_115659, baseEnd_115659] using wordTrace_append hprefix tailTrace_115659
  have hstable : (prefixWord ++ tailWord_115659).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115659).length < 2 ^ (prefixWord ++ tailWord_115659).sum := by decide
  have hdescent : baseEnd_115659 < baseStart_115659 := by decide
  rcases family_descends (prefixWord ++ tailWord_115659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115710 : List Nat := [4, 2, 2, 2, 3, 1, 2, 3]
def baseStart_115710 : Nat := 118140960795 + 115710 * 2 ^ 59
def prefixEnd_115710 : Nat := 4983230072969 + 3 ^ 40 * 115710 * 2
def baseEnd_115710 : Nat := 35208797944798529062439

theorem tailTrace_115710 : CollatzResearch.WordTrace tailWord_115710 prefixEnd_115710 35208797944798529062439 := by
  unfold tailWord_115710
  simp only [CollatzResearch.WordTrace]
  refine ⟨527536301351238317475073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2813526940539937693200389 527536301351238317475073)
  ·
    refine ⟨395652226013428738106305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 527536301351238317475073 395652226013428738106305)
    ·
      refine ⟨296739169510071553579729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 395652226013428738106305 296739169510071553579729)
      ·
        refine ⟨222554377132553665184797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 296739169510071553579729 222554377132553665184797)
        ·
          refine ⟨83457891424707624444299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 222554377132553665184797 83457891424707624444299)
          ·
            refine ⟨125186837137061436666449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83457891424707624444299 125186837137061436666449)
            ·
              refine ⟨93890127852796077499837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125186837137061436666449 93890127852796077499837)
              ·
                refine ⟨35208797944798529062439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93890127852796077499837 35208797944798529062439)
                ·
                  rfl

theorem cell19_115710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_115710 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115710 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115710 prefixEnd_115710 := by exact prefixLift 115710
  have htrace : WordTrace (prefixWord ++ tailWord_115710) baseStart_115710 baseEnd_115710 := by
    simpa [prefixWord, tailWord_115710, baseEnd_115710] using wordTrace_append hprefix tailTrace_115710
  have hstable : (prefixWord ++ tailWord_115710).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115710).length < 2 ^ (prefixWord ++ tailWord_115710).sum := by decide
  have hdescent : baseEnd_115710 < baseStart_115710 := by decide
  rcases family_descends (prefixWord ++ tailWord_115710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115735 : List Nat := [1, 1, 3, 5, 1, 3, 5]
def baseStart_115735 : Nat := 118140960795 + 115735 * 2 ^ 59
def prefixEnd_115735 : Nat := 4983230072969 + 3 ^ 40 * 115735 * 2
def baseEnd_115735 : Nat := 11738801688535292835605

theorem tailTrace_115735 : CollatzResearch.WordTrace tailWord_115735 prefixEnd_115735 11738801688535292835605 := by
  unfold tailWord_115735
  simp only [CollatzResearch.WordTrace]
  refine ⟨4221202235719335809460659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2814134823812890539640439 4221202235719335809460659)
  ·
    refine ⟨6331803353579003714190989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4221202235719335809460659 6331803353579003714190989)
    ·
      refine ⟨2374426257592126392821621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6331803353579003714190989 2374426257592126392821621)
      ·
        refine ⟨222602461649261849327027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2374426257592126392821621 222602461649261849327027)
        ·
          refine ⟨333903692473892773990541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222602461649261849327027 333903692473892773990541)
          ·
            refine ⟨125213884677709790246453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 333903692473892773990541 125213884677709790246453)
            ·
              refine ⟨11738801688535292835605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125213884677709790246453 11738801688535292835605)
              ·
                rfl

theorem cell19_115735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 5].length) (baseStart_115735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115735 prefixEnd_115735 := by exact prefixLift 115735
  have htrace : WordTrace (prefixWord ++ tailWord_115735) baseStart_115735 baseEnd_115735 := by
    simpa [prefixWord, tailWord_115735, baseEnd_115735] using wordTrace_append hprefix tailTrace_115735
  have hstable : (prefixWord ++ tailWord_115735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115735).length < 2 ^ (prefixWord ++ tailWord_115735).sum := by decide
  have hdescent : baseEnd_115735 < baseStart_115735 := by decide
  rcases family_descends (prefixWord ++ tailWord_115735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115756 : List Nat := [2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_115756 : Nat := 118140960795 + 115756 * 2 ^ 59
def prefixEnd_115756 : Nat := 4983230072969 + 3 ^ 40 * 115756 * 2
def baseEnd_115756 : Nat := 35222795047084052040091

theorem tailTrace_115756 : CollatzResearch.WordTrace tailWord_115756 prefixEnd_115756 35222795047084052040091 := by
  unfold tailWord_115756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2110984084321628197987561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2814645445762170930650081 2110984084321628197987561)
  ·
    refine ⟨1583238063241221148490671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2110984084321628197987561 1583238063241221148490671)
    ·
      refine ⟨2374857094861831722736007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1583238063241221148490671 2374857094861831722736007)
      ·
        refine ⟨3562285642292747584104011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2374857094861831722736007 3562285642292747584104011)
        ·
          refine ⟨5343428463439121376156017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3562285642292747584104011 5343428463439121376156017)
          ·
            refine ⟨4007571347579341032117013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5343428463439121376156017 4007571347579341032117013)
            ·
              refine ⟨187854906917781610880485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4007571347579341032117013 187854906917781610880485)
              ·
                refine ⟨35222795047084052040091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 187854906917781610880485 35222795047084052040091)
                ·
                  rfl

theorem cell19_115756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_115756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115756 prefixEnd_115756 := by exact prefixLift 115756
  have htrace : WordTrace (prefixWord ++ tailWord_115756) baseStart_115756 baseEnd_115756 := by
    simpa [prefixWord, tailWord_115756, baseEnd_115756] using wordTrace_append hprefix tailTrace_115756
  have hstable : (prefixWord ++ tailWord_115756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115756).length < 2 ^ (prefixWord ++ tailWord_115756).sum := by decide
  have hdescent : baseEnd_115756 < baseStart_115756 := by decide
  rcases family_descends (prefixWord ++ tailWord_115756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115794 : List Nat := [3, 2, 2, 1, 3, 8]
def baseStart_115794 : Nat := 118140960795 + 115794 * 2 ^ 59
def prefixEnd_115794 : Nat := 4983230072969 + 3 ^ 40 * 115794 * 2
def baseEnd_115794 : Nat := 3914928652301247021727

theorem tailTrace_115794 : CollatzResearch.WordTrace tailWord_115794 prefixEnd_115794 3914928652301247021727 := by
  unfold tailWord_115794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1055838535626397221464609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2815569428337059257238957 1055838535626397221464609)
  ·
    refine ⟨791878901719797916098457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1055838535626397221464609 791878901719797916098457)
    ·
      refine ⟨593909176289848437073843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 791878901719797916098457 593909176289848437073843)
      ·
        refine ⟨890863764434772655610765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 593909176289848437073843 890863764434772655610765)
        ·
          refine ⟨334073911663039745854037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 890863764434772655610765 334073911663039745854037)
          ·
            refine ⟨3914928652301247021727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 334073911663039745854037 3914928652301247021727)
            ·
              rfl

theorem cell19_115794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 8].length) (baseStart_115794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115794 prefixEnd_115794 := by exact prefixLift 115794
  have htrace : WordTrace (prefixWord ++ tailWord_115794) baseStart_115794 baseEnd_115794 := by
    simpa [prefixWord, tailWord_115794, baseEnd_115794] using wordTrace_append hprefix tailTrace_115794
  have hstable : (prefixWord ++ tailWord_115794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115794).length < 2 ^ (prefixWord ++ tailWord_115794).sum := by decide
  have hdescent : baseEnd_115794 < baseStart_115794 := by decide
  rcases family_descends (prefixWord ++ tailWord_115794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115925 : List Nat := [1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_115925 : Nat := 118140960795 + 115925 * 2 ^ 59
def prefixEnd_115925 : Nat := 4983230072969 + 3 ^ 40 * 115925 * 2
def baseEnd_115925 : Nat := 35274219183741734284075

theorem tailTrace_115925 : CollatzResearch.WordTrace tailWord_115925 prefixEnd_115925 35274219183741734284075 := by
  unfold tailWord_115925
  simp only [CollatzResearch.WordTrace]
  refine ⟨4228132105030998258877229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2818754736687332172584819 4228132105030998258877229)
  ·
    refine ⟨1585549539386624347078961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4228132105030998258877229 1585549539386624347078961)
    ·
      refine ⟨1189162154539968260309221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1585549539386624347078961 1189162154539968260309221)
      ·
        refine ⟨222967903976244048807979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1189162154539968260309221 222967903976244048807979)
        ·
          refine ⟨334451855964366073211969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 222967903976244048807979 334451855964366073211969)
          ·
            refine ⟨250838891973274554908977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 334451855964366073211969 250838891973274554908977)
            ·
              refine ⟨188129168979955916181733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 250838891973274554908977 188129168979955916181733)
              ·
                refine ⟨35274219183741734284075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188129168979955916181733 35274219183741734284075)
                ·
                  rfl

theorem cell19_115925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_115925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115925 prefixEnd_115925 := by exact prefixLift 115925
  have htrace : WordTrace (prefixWord ++ tailWord_115925) baseStart_115925 baseEnd_115925 := by
    simpa [prefixWord, tailWord_115925, baseEnd_115925] using wordTrace_append hprefix tailTrace_115925
  have hstable : (prefixWord ++ tailWord_115925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115925).length < 2 ^ (prefixWord ++ tailWord_115925).sum := by decide
  have hdescent : baseEnd_115925 < baseStart_115925 := by decide
  rcases family_descends (prefixWord ++ tailWord_115925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115946 : List Nat := [3, 1, 3, 1, 1, 3, 2, 5]
def baseStart_115946 : Nat := 118140960795 + 115946 * 2 ^ 59
def prefixEnd_115946 : Nat := 4983230072969 + 3 ^ 40 * 115946 * 2
def baseEnd_115946 : Nat := 35280609165219907817351

theorem tailTrace_115946 : CollatzResearch.WordTrace tailWord_115946 prefixEnd_115946 35280609165219907817351 := by
  unfold tailWord_115946
  simp only [CollatzResearch.WordTrace]
  refine ⟨1057224509488729711347923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2819265358636612563594461 1057224509488729711347923)
  ·
    refine ⟨1585836764233094567021885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1057224509488729711347923 1585836764233094567021885)
    ·
      refine ⟨594688786587410462633207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1585836764233094567021885 594688786587410462633207)
      ·
        refine ⟨892033179881115693949811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 594688786587410462633207 892033179881115693949811)
        ·
          refine ⟨1338049769821673540924717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892033179881115693949811 1338049769821673540924717)
          ·
            refine ⟨501768663683127577846769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1338049769821673540924717 501768663683127577846769)
            ·
              refine ⟨376326497762345683385077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 501768663683127577846769 376326497762345683385077)
              ·
                refine ⟨35280609165219907817351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 376326497762345683385077 35280609165219907817351)
                ·
                  rfl

theorem cell19_115946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_115946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115946 prefixEnd_115946 := by exact prefixLift 115946
  have htrace : WordTrace (prefixWord ++ tailWord_115946) baseStart_115946 baseEnd_115946 := by
    simpa [prefixWord, tailWord_115946, baseEnd_115946] using wordTrace_append hprefix tailTrace_115946
  have hstable : (prefixWord ++ tailWord_115946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115946).length < 2 ^ (prefixWord ++ tailWord_115946).sum := by decide
  have hdescent : baseEnd_115946 < baseStart_115946 := by decide
  rcases family_descends (prefixWord ++ tailWord_115946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115967 : List Nat := [1, 1, 2, 2, 1, 12]
def baseStart_115967 : Nat := 118140960795 + 115967 * 2 ^ 59
def prefixEnd_115967 : Nat := 4983230072969 + 3 ^ 40 * 115967 * 2
def baseEnd_115967 : Nat := 3920777682966453483403

theorem tailTrace_115967 : CollatzResearch.WordTrace tailWord_115967 prefixEnd_115967 3920777682966453483403 := by
  unfold tailWord_115967
  simp only [CollatzResearch.WordTrace]
  refine ⟨4229663970878839431906155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2819775980585892954604103 4229663970878839431906155)
  ·
    refine ⟨6344495956318259147859233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4229663970878839431906155 6344495956318259147859233)
    ·
      refine ⟨4758371967238694360894425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344495956318259147859233 4758371967238694360894425)
      ·
        refine ⟨3568778975429020770670819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4758371967238694360894425 3568778975429020770670819)
        ·
          refine ⟨5353168463143531156006229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3568778975429020770670819 5353168463143531156006229)
          ·
            refine ⟨3920777682966453483403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 5353168463143531156006229 3920777682966453483403)
            ·
              rfl

theorem cell19_115967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_115967 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115967 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115967 prefixEnd_115967 := by exact prefixLift 115967
  have htrace : WordTrace (prefixWord ++ tailWord_115967) baseStart_115967 baseEnd_115967 := by
    simpa [prefixWord, tailWord_115967, baseEnd_115967] using wordTrace_append hprefix tailTrace_115967
  have hstable : (prefixWord ++ tailWord_115967).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115967).length < 2 ^ (prefixWord ++ tailWord_115967).sum := by decide
  have hdescent : baseEnd_115967 < baseStart_115967 := by decide
  rcases family_descends (prefixWord ++ tailWord_115967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_115982 : List Nat := [4, 1, 1, 2, 1, 5, 1, 4]
def baseStart_115982 : Nat := 118140960795 + 115982 * 2 ^ 59
def prefixEnd_115982 : Nat := 4983230072969 + 3 ^ 40 * 115982 * 2
def baseEnd_115982 : Nat := 35291563419182491017253

theorem tailTrace_115982 : CollatzResearch.WordTrace tailWord_115982 prefixEnd_115982 35291563419182491017253 := by
  unfold tailWord_115982
  simp only [CollatzResearch.WordTrace]
  refine ⟨528776383228062124212775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2820140710549664662468133 528776383228062124212775)
  ·
    refine ⟨793164574842093186319163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 528776383228062124212775 793164574842093186319163)
    ·
      refine ⟨1189746862263139779478745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 793164574842093186319163 1189746862263139779478745)
      ·
        refine ⟨892310146697354834609059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1189746862263139779478745 892310146697354834609059)
        ·
          refine ⟨1338465220046032251913589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 892310146697354834609059 1338465220046032251913589)
          ·
            refine ⟨125481114379315523616899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1338465220046032251913589 125481114379315523616899)
            ·
              refine ⟨188221671568973285425349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125481114379315523616899 188221671568973285425349)
              ·
                refine ⟨35291563419182491017253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188221671568973285425349 35291563419182491017253)
                ·
                  rfl

theorem cell19_115982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_115982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_115982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_115982 prefixEnd_115982 := by exact prefixLift 115982
  have htrace : WordTrace (prefixWord ++ tailWord_115982) baseStart_115982 baseEnd_115982 := by
    simpa [prefixWord, tailWord_115982, baseEnd_115982] using wordTrace_append hprefix tailTrace_115982
  have hstable : (prefixWord ++ tailWord_115982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_115982).length < 2 ^ (prefixWord ++ tailWord_115982).sum := by decide
  have hdescent : baseEnd_115982 < baseStart_115982 := by decide
  rcases family_descends (prefixWord ++ tailWord_115982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116081 : List Nat := [1, 2, 2, 2, 1, 2, 9]
def baseStart_116081 : Nat := 118140960795 + 116081 * 2 ^ 59
def prefixEnd_116081 : Nat := 4983230072969 + 3 ^ 40 * 116081 * 2
def baseEnd_116081 : Nat := 11773895872526531605661

theorem tailTrace_116081 : CollatzResearch.WordTrace tailWord_116081 prefixEnd_116081 11773895872526531605661 := by
  unfold tailWord_116081
  simp only [CollatzResearch.WordTrace]
  refine ⟨4233821892465836901556097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2822547928310557934370731 4233821892465836901556097)
  ·
    refine ⟨3175366419349377676167073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4233821892465836901556097 3175366419349377676167073)
    ·
      refine ⟨2381524814512033257125305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3175366419349377676167073 2381524814512033257125305)
      ·
        refine ⟨1786143610884024942843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2381524814512033257125305 1786143610884024942843979)
        ·
          refine ⟨2679215416326037414265969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1786143610884024942843979 2679215416326037414265969)
          ·
            refine ⟨2009411562244528060699477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2679215416326037414265969 2009411562244528060699477)
            ·
              refine ⟨11773895872526531605661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2009411562244528060699477 11773895872526531605661)
              ·
                rfl

theorem cell19_116081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 9].length) (baseStart_116081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116081 prefixEnd_116081 := by exact prefixLift 116081
  have htrace : WordTrace (prefixWord ++ tailWord_116081) baseStart_116081 baseEnd_116081 := by
    simpa [prefixWord, tailWord_116081, baseEnd_116081] using wordTrace_append hprefix tailTrace_116081
  have hstable : (prefixWord ++ tailWord_116081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116081).length < 2 ^ (prefixWord ++ tailWord_116081).sum := by decide
  have hdescent : baseEnd_116081 < baseStart_116081 := by decide
  rcases family_descends (prefixWord ++ tailWord_116081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116136 : List Nat := [2, 1, 6, 1, 9]
def baseStart_116136 : Nat := 118140960795 + 116136 * 2 ^ 59
def prefixEnd_116136 : Nat := 4983230072969 + 3 ^ 40 * 116136 * 2
def baseEnd_116136 : Nat := 1308830491976139392393

theorem tailTrace_116136 : CollatzResearch.WordTrace tailWord_116136 prefixEnd_116136 1308830491976139392393 := by
  unfold tailWord_116136
  simp only [CollatzResearch.WordTrace]
  refine ⟨2117913953633290647404131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2823885271511054196538841 2117913953633290647404131)
  ·
    refine ⟨3176870930449935971106197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2117913953633290647404131 3176870930449935971106197)
    ·
      refine ⟨148915824864840748645603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3176870930449935971106197 148915824864840748645603)
      ·
        refine ⟨223373737297261122968405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148915824864840748645603 223373737297261122968405)
        ·
          refine ⟨1308830491976139392393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 223373737297261122968405 1308830491976139392393)
          ·
            rfl

theorem cell19_116136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_116136 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116136 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116136 prefixEnd_116136 := by exact prefixLift 116136
  have htrace : WordTrace (prefixWord ++ tailWord_116136) baseStart_116136 baseEnd_116136 := by
    simpa [prefixWord, tailWord_116136, baseEnd_116136] using wordTrace_append hprefix tailTrace_116136
  have hstable : (prefixWord ++ tailWord_116136).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116136).length < 2 ^ (prefixWord ++ tailWord_116136).sum := by decide
  have hdescent : baseEnd_116136 < baseStart_116136 := by decide
  rcases family_descends (prefixWord ++ tailWord_116136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116153 : List Nat := [1, 2, 1, 4, 4, 2, 1, 4]
def baseStart_116153 : Nat := 118140960795 + 116153 * 2 ^ 59
def prefixEnd_116153 : Nat := 4983230072969 + 3 ^ 40 * 116153 * 2
def baseEnd_116153 : Nat := 35343596125504761216787

theorem tailTrace_116153 : CollatzResearch.WordTrace tailWord_116153 prefixEnd_116153 35343596125504761216787 := by
  unfold tailWord_116153
  simp only [CollatzResearch.WordTrace]
  refine ⟨4236447948204993198177113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2824298632136662132118075 4236447948204993198177113)
  ·
    refine ⟨3177335961153744898632835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4236447948204993198177113 3177335961153744898632835)
    ·
      refine ⟨4766003941730617347949253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3177335961153744898632835 4766003941730617347949253)
      ·
        refine ⟨893625739074490752740485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4766003941730617347949253 893625739074490752740485)
        ·
          refine ⟨167554826076467016138841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 893625739074490752740485 167554826076467016138841)
          ·
            refine ⟨125666119557350262104131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167554826076467016138841 125666119557350262104131)
            ·
              refine ⟨188499179336025393156197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125666119557350262104131 188499179336025393156197)
              ·
                refine ⟨35343596125504761216787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188499179336025393156197 35343596125504761216787)
                ·
                  rfl

theorem cell19_116153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 4].length) (baseStart_116153 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116153 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116153 prefixEnd_116153 := by exact prefixLift 116153
  have htrace : WordTrace (prefixWord ++ tailWord_116153) baseStart_116153 baseEnd_116153 := by
    simpa [prefixWord, tailWord_116153, baseEnd_116153] using wordTrace_append hprefix tailTrace_116153
  have hstable : (prefixWord ++ tailWord_116153).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116153).length < 2 ^ (prefixWord ++ tailWord_116153).sum := by decide
  have hdescent : baseEnd_116153 < baseStart_116153 := by decide
  rcases family_descends (prefixWord ++ tailWord_116153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116172 : List Nat := [2, 2, 1, 4, 2, 2, 3, 3]
def baseStart_116172 : Nat := 118140960795 + 116172 * 2 ^ 59
def prefixEnd_116172 : Nat := 4983230072969 + 3 ^ 40 * 116172 * 2
def baseEnd_116172 : Nat := 35349377537318346794513

theorem tailTrace_116172 : CollatzResearch.WordTrace tailWord_116172 prefixEnd_116172 35349377537318346794513 := by
  unfold tailWord_116172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2118570467568079721559385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2824760623424106295412513 2118570467568079721559385)
  ·
    refine ⟨1588927850676059791169539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2118570467568079721559385 1588927850676059791169539)
    ·
      refine ⟨2383391776014089686754309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1588927850676059791169539 2383391776014089686754309)
      ·
        refine ⟨446885958002641816266433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2383391776014089686754309 446885958002641816266433)
        ·
          refine ⟨335164468501981362199825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446885958002641816266433 335164468501981362199825)
          ·
            refine ⟨251373351376486021649869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335164468501981362199825 251373351376486021649869)
            ·
              refine ⟨94265006766182258118701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251373351376486021649869 94265006766182258118701)
              ·
                refine ⟨35349377537318346794513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94265006766182258118701 35349377537318346794513)
                ·
                  rfl

theorem cell19_116172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 3, 3].length) (baseStart_116172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116172 prefixEnd_116172 := by exact prefixLift 116172
  have htrace : WordTrace (prefixWord ++ tailWord_116172) baseStart_116172 baseEnd_116172 := by
    simpa [prefixWord, tailWord_116172, baseEnd_116172] using wordTrace_append hprefix tailTrace_116172
  have hstable : (prefixWord ++ tailWord_116172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116172).length < 2 ^ (prefixWord ++ tailWord_116172).sum := by decide
  have hdescent : baseEnd_116172 < baseStart_116172 := by decide
  rcases family_descends (prefixWord ++ tailWord_116172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116231 : List Nat := [1, 1, 4, 3, 2, 2, 1, 5]
def baseStart_116231 : Nat := 118140960795 + 116231 * 2 ^ 59
def prefixEnd_116231 : Nat := 4983230072969 + 3 ^ 40 * 116231 * 2
def baseEnd_116231 : Nat := 35367330342423691483241

theorem tailTrace_116231 : CollatzResearch.WordTrace tailWord_116231 prefixEnd_116231 35367330342423691483241 := by
  unfold tailWord_116231
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239292841922412519516547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2826195227948275013011031 4239292841922412519516547)
  ·
    refine ⟨6358939262883618779274821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4239292841922412519516547 6358939262883618779274821)
    ·
      refine ⟨1192301111790678521114029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6358939262883618779274821 1192301111790678521114029)
      ·
        refine ⟨447112916921504445417761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1192301111790678521114029 447112916921504445417761)
        ·
          refine ⟨335334687691128334063321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447112916921504445417761 335334687691128334063321)
          ·
            refine ⟨251501015768346250547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335334687691128334063321 251501015768346250547491)
            ·
              refine ⟨377251523652519375821237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251501015768346250547491 377251523652519375821237)
              ·
                refine ⟨35367330342423691483241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377251523652519375821237 35367330342423691483241)
                ·
                  rfl

theorem cell19_116231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 5].length) (baseStart_116231 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116231 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116231 prefixEnd_116231 := by exact prefixLift 116231
  have htrace : WordTrace (prefixWord ++ tailWord_116231) baseStart_116231 baseEnd_116231 := by
    simpa [prefixWord, tailWord_116231, baseEnd_116231] using wordTrace_append hprefix tailTrace_116231
  have hstable : (prefixWord ++ tailWord_116231).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116231).length < 2 ^ (prefixWord ++ tailWord_116231).sum := by decide
  have hdescent : baseEnd_116231 < baseStart_116231 := by decide
  rcases family_descends (prefixWord ++ tailWord_116231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116233 : List Nat := [1, 2, 1, 1, 3, 1, 5, 5]
def baseStart_116233 : Nat := 118140960795 + 116233 * 2 ^ 59
def prefixEnd_116233 : Nat := 4983230072969 + 3 ^ 40 * 116233 * 2
def baseEnd_116233 : Nat := 35367938912088279438791

theorem tailTrace_116233 : CollatzResearch.WordTrace tailWord_116233 prefixEnd_116233 35367938912088279438791 := by
  unfold tailWord_116233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4239365787915166861089353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2826243858610111240726235 4239365787915166861089353)
  ·
    refine ⟨3179524340936375145817015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4239365787915166861089353 3179524340936375145817015)
    ·
      refine ⟨4769286511404562718725523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3179524340936375145817015 4769286511404562718725523)
      ·
        refine ⟨7153929767106844078088285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4769286511404562718725523 7153929767106844078088285)
        ·
          refine ⟨2682723662665066529283107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7153929767106844078088285 2682723662665066529283107)
          ·
            refine ⟨4024085493997599793924661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2682723662665066529283107 4024085493997599793924661)
            ·
              refine ⟨377258015062274980680437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4024085493997599793924661 377258015062274980680437)
              ·
                refine ⟨35367938912088279438791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377258015062274980680437 35367938912088279438791)
                ·
                  rfl

theorem cell19_116233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 5].length) (baseStart_116233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116233 prefixEnd_116233 := by exact prefixLift 116233
  have htrace : WordTrace (prefixWord ++ tailWord_116233) baseStart_116233 baseEnd_116233 := by
    simpa [prefixWord, tailWord_116233, baseEnd_116233] using wordTrace_append hprefix tailTrace_116233
  have hstable : (prefixWord ++ tailWord_116233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116233).length < 2 ^ (prefixWord ++ tailWord_116233).sum := by decide
  have hdescent : baseEnd_116233 < baseStart_116233 := by decide
  rcases family_descends (prefixWord ++ tailWord_116233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116248 : List Nat := [2, 1, 2, 3, 5, 1, 5]
def baseStart_116248 : Nat := 118140960795 + 116248 * 2 ^ 59
def prefixEnd_116248 : Nat := 4983230072969 + 3 ^ 40 * 116248 * 2
def baseEnd_116248 : Nat := 11790834394857563035139

theorem tailTrace_116248 : CollatzResearch.WordTrace tailWord_116248 prefixEnd_116248 11790834394857563035139 := by
  unfold tailWord_116248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2119956441430412211442699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2826608588573882948590265 2119956441430412211442699)
  ·
    refine ⟨3179934662145618317164049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2119956441430412211442699 3179934662145618317164049)
    ·
      refine ⟨2384950996609213737873037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3179934662145618317164049 2384950996609213737873037)
      ·
        refine ⟨894356623728455151702389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2384950996609213737873037 894356623728455151702389)
        ·
          refine ⟨83845933474542670472099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 894356623728455151702389 83845933474542670472099)
          ·
            refine ⟨125768900211814005708149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83845933474542670472099 125768900211814005708149)
            ·
              refine ⟨11790834394857563035139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125768900211814005708149 11790834394857563035139)
              ·
                rfl

theorem cell19_116248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 5].length) (baseStart_116248 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116248 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116248 prefixEnd_116248 := by exact prefixLift 116248
  have htrace : WordTrace (prefixWord ++ tailWord_116248) baseStart_116248 baseEnd_116248 := by
    simpa [prefixWord, tailWord_116248, baseEnd_116248] using wordTrace_append hprefix tailTrace_116248
  have hstable : (prefixWord ++ tailWord_116248).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116248).length < 2 ^ (prefixWord ++ tailWord_116248).sum := by decide
  have hdescent : baseEnd_116248 < baseStart_116248 := by decide
  rcases family_descends (prefixWord ++ tailWord_116248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116345 : List Nat := [1, 2, 1, 3, 3, 1, 5, 3]
def baseStart_116345 : Nat := 118140960795 + 116345 * 2 ^ 59
def prefixEnd_116345 : Nat := 4983230072969 + 3 ^ 40 * 116345 * 2
def baseEnd_116345 : Nat := 35402018813305204949597

theorem tailTrace_116345 : CollatzResearch.WordTrace tailWord_116345 prefixEnd_116345 35402018813305204949597 := by
  unfold tailWord_116345
  simp only [CollatzResearch.WordTrace]
  refine ⟨4243450763509409989166489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2828967175672939992777659 4243450763509409989166489)
  ·
    refine ⟨3182588072632057491874867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4243450763509409989166489 3182588072632057491874867)
    ·
      refine ⟨4773882108948086237812301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3182588072632057491874867 4773882108948086237812301)
      ·
        refine ⟨1790205790855532339179613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4773882108948086237812301 1790205790855532339179613)
        ·
          refine ⟨671327171570824627192355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1790205790855532339179613 671327171570824627192355)
          ·
            refine ⟨1006990757356236940788533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 671327171570824627192355 1006990757356236940788533)
            ·
              refine ⟨94405383502147213198925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1006990757356236940788533 94405383502147213198925)
              ·
                refine ⟨35402018813305204949597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94405383502147213198925 35402018813305204949597)
                ·
                  rfl

theorem cell19_116345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_116345 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116345 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116345 prefixEnd_116345 := by exact prefixLift 116345
  have htrace : WordTrace (prefixWord ++ tailWord_116345) baseStart_116345 baseEnd_116345 := by
    simpa [prefixWord, tailWord_116345, baseEnd_116345] using wordTrace_append hprefix tailTrace_116345
  have hstable : (prefixWord ++ tailWord_116345).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116345).length < 2 ^ (prefixWord ++ tailWord_116345).sum := by decide
  have hdescent : baseEnd_116345 < baseStart_116345 := by decide
  rcases family_descends (prefixWord ++ tailWord_116345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116402 : List Nat := [3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_116402 : Nat := 118140960795 + 116402 * 2 ^ 59
def prefixEnd_116402 : Nat := 4983230072969 + 3 ^ 40 * 116402 * 2
def baseEnd_116402 : Nat := 35419363048745961682775

theorem tailTrace_116402 : CollatzResearch.WordTrace tailWord_116402 prefixEnd_116402 35419363048745961682775 := by
  unfold tailWord_116402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061382431075727180997865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2830353149535272482660973 1061382431075727180997865)
  ·
    refine ⟨796036823306795385748399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1061382431075727180997865 796036823306795385748399)
    ·
      refine ⟨1194055234960193078622599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 796036823306795385748399 1194055234960193078622599)
      ·
        refine ⟨1791082852440289617933899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1194055234960193078622599 1791082852440289617933899)
        ·
          refine ⟨2686624278660434426900849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1791082852440289617933899 2686624278660434426900849)
          ·
            refine ⟨2014968208995325820175637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2686624278660434426900849 2014968208995325820175637)
            ·
              refine ⟨94451634796655897820733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2014968208995325820175637 94451634796655897820733)
              ·
                refine ⟨35419363048745961682775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94451634796655897820733 35419363048745961682775)
                ·
                  rfl

theorem cell19_116402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_116402 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116402 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116402 prefixEnd_116402 := by exact prefixLift 116402
  have htrace : WordTrace (prefixWord ++ tailWord_116402) baseStart_116402 baseEnd_116402 := by
    simpa [prefixWord, tailWord_116402, baseEnd_116402] using wordTrace_append hprefix tailTrace_116402
  have hstable : (prefixWord ++ tailWord_116402).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116402).length < 2 ^ (prefixWord ++ tailWord_116402).sum := by decide
  have hdescent : baseEnd_116402 < baseStart_116402 := by decide
  rcases family_descends (prefixWord ++ tailWord_116402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116442 : List Nat := [3, 1, 1, 2, 2, 3, 1, 6]
def baseStart_116442 : Nat := 118140960795 + 116442 * 2 ^ 59
def prefixEnd_116442 : Nat := 4983230072969 + 3 ^ 40 * 116442 * 2
def baseEnd_116442 : Nat := 35431534442037720793777

theorem tailTrace_116442 : CollatzResearch.WordTrace tailWord_116442 prefixEnd_116442 35431534442037720793777 := by
  unfold tailWord_116442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1061747161039498888861895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2831325762771997036965053 1061747161039498888861895)
  ·
    refine ⟨1592620741559248333292843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1061747161039498888861895 1592620741559248333292843)
    ·
      refine ⟨2388931112338872499939265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1592620741559248333292843 2388931112338872499939265)
      ·
        refine ⟨1791698334254154374954449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2388931112338872499939265 1791698334254154374954449)
        ·
          refine ⟨1343773750690615781215837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1791698334254154374954449 1343773750690615781215837)
          ·
            refine ⟨503915156508980917955939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1343773750690615781215837 503915156508980917955939)
            ·
              refine ⟨755872734763471376933909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 503915156508980917955939 755872734763471376933909)
              ·
                refine ⟨35431534442037720793777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 755872734763471376933909 35431534442037720793777)
                ·
                  rfl

theorem cell19_116442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 6].length) (baseStart_116442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116442 prefixEnd_116442 := by exact prefixLift 116442
  have htrace : WordTrace (prefixWord ++ tailWord_116442) baseStart_116442 baseEnd_116442 := by
    simpa [prefixWord, tailWord_116442, baseEnd_116442] using wordTrace_append hprefix tailTrace_116442
  have hstable : (prefixWord ++ tailWord_116442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116442).length < 2 ^ (prefixWord ++ tailWord_116442).sum := by decide
  have hdescent : baseEnd_116442 < baseStart_116442 := by decide
  rcases family_descends (prefixWord ++ tailWord_116442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116478 : List Nat := [4, 2, 2, 1, 3, 7]
def baseStart_116478 : Nat := 118140960795 + 116478 * 2 ^ 59
def prefixEnd_116478 : Nat := 4983230072969 + 3 ^ 40 * 116478 * 2
def baseEnd_116478 : Nat := 3938054299555589332631

theorem tailTrace_116478 : CollatzResearch.WordTrace tailWord_116478 prefixEnd_116478 3938054299555589332631 := by
  unfold tailWord_116478
  simp only [CollatzResearch.WordTrace]
  refine ⟨531037709003446712969761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2832201114685049135838725 531037709003446712969761)
  ·
    refine ⟨398278281752585034727321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 531037709003446712969761 398278281752585034727321)
    ·
      refine ⟨298708711314438776045491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 398278281752585034727321 298708711314438776045491)
      ·
        refine ⟨448063066971658164068237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298708711314438776045491 448063066971658164068237)
        ·
          refine ⟨168023650114371811525589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 448063066971658164068237 168023650114371811525589)
          ·
            refine ⟨3938054299555589332631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 168023650114371811525589 3938054299555589332631)
            ·
              rfl

theorem cell19_116478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 7].length) (baseStart_116478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116478 prefixEnd_116478 := by exact prefixLift 116478
  have htrace : WordTrace (prefixWord ++ tailWord_116478) baseStart_116478 baseEnd_116478 := by
    simpa [prefixWord, tailWord_116478, baseEnd_116478] using wordTrace_append hprefix tailTrace_116478
  have hstable : (prefixWord ++ tailWord_116478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116478).length < 2 ^ (prefixWord ++ tailWord_116478).sum := by decide
  have hdescent : baseEnd_116478 < baseStart_116478 := by decide
  rcases family_descends (prefixWord ++ tailWord_116478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116510 : List Nat := [4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_116510 : Nat := 118140960795 + 116510 * 2 ^ 59
def prefixEnd_116510 : Nat := 4983230072969 + 3 ^ 40 * 116510 * 2
def baseEnd_116510 : Nat := 35452225810633711282481

theorem tailTrace_116510 : CollatzResearch.WordTrace tailWord_116510 prefixEnd_116510 35452225810633711282481 := by
  unfold tailWord_116510
  simp only [CollatzResearch.WordTrace]
  refine ⟨531183600988955396115373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2832979205274428779281989 531183600988955396115373)
  ·
    refine ⟨199193850370858273543265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 531183600988955396115373 199193850370858273543265)
    ·
      refine ⟨149395387778143705157449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199193850370858273543265 149395387778143705157449)
      ·
        refine ⟨112046540833607778868087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149395387778143705157449 112046540833607778868087)
        ·
          refine ⟨168069811250411668302131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112046540833607778868087 168069811250411668302131)
          ·
            refine ⟨252104716875617502453197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168069811250411668302131 252104716875617502453197)
            ·
              refine ⟨94539268828356563419949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252104716875617502453197 94539268828356563419949)
              ·
                refine ⟨35452225810633711282481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94539268828356563419949 35452225810633711282481)
                ·
                  rfl

theorem cell19_116510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_116510 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116510 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116510 prefixEnd_116510 := by exact prefixLift 116510
  have htrace : WordTrace (prefixWord ++ tailWord_116510) baseStart_116510 baseEnd_116510 := by
    simpa [prefixWord, tailWord_116510, baseEnd_116510] using wordTrace_append hprefix tailTrace_116510
  have hstable : (prefixWord ++ tailWord_116510).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116510).length < 2 ^ (prefixWord ++ tailWord_116510).sum := by decide
  have hdescent : baseEnd_116510 < baseStart_116510 := by decide
  rcases family_descends (prefixWord ++ tailWord_116510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116575 : List Nat := [1, 1, 2, 3, 1, 5, 1, 5]
def baseStart_116575 : Nat := 118140960795 + 116575 * 2 ^ 59
def prefixEnd_116575 : Nat := 4983230072969 + 3 ^ 40 * 116575 * 2
def baseEnd_116575 : Nat := 35472004324732819837859

theorem tailTrace_116575 : CollatzResearch.WordTrace tailWord_116575 prefixEnd_116575 35472004324732819837859 := by
  unfold tailWord_116575
  simp only [CollatzResearch.WordTrace]
  refine ⟨4251839552676159270039179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2834559701784106180026119 4251839552676159270039179)
  ·
    refine ⟨6377759329014238905058769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4251839552676159270039179 6377759329014238905058769)
    ·
      refine ⟨4783319496760679178794077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6377759329014238905058769 4783319496760679178794077)
      ·
        refine ⟨1793744811285254692047779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4783319496760679178794077 1793744811285254692047779)
        ·
          refine ⟨2690617216927882038071669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1793744811285254692047779 2690617216927882038071669)
          ·
            refine ⟨252245364086988941069219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2690617216927882038071669 252245364086988941069219)
            ·
              refine ⟨378368046130483411603829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252245364086988941069219 378368046130483411603829)
              ·
                refine ⟨35472004324732819837859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 378368046130483411603829 35472004324732819837859)
                ·
                  rfl

theorem cell19_116575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 5].length) (baseStart_116575 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116575 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116575 prefixEnd_116575 := by exact prefixLift 116575
  have htrace : WordTrace (prefixWord ++ tailWord_116575) baseStart_116575 baseEnd_116575 := by
    simpa [prefixWord, tailWord_116575, baseEnd_116575] using wordTrace_append hprefix tailTrace_116575
  have hstable : (prefixWord ++ tailWord_116575).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116575).length < 2 ^ (prefixWord ++ tailWord_116575).sum := by decide
  have hdescent : baseEnd_116575 < baseStart_116575 := by decide
  rcases family_descends (prefixWord ++ tailWord_116575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116609 : List Nat := [1, 2, 4, 4, 1, 1, 2, 4]
def baseStart_116609 : Nat := 118140960795 + 116609 * 2 ^ 59
def prefixEnd_116609 : Nat := 4983230072969 + 3 ^ 40 * 116609 * 2
def baseEnd_116609 : Nat := 35482350009030815082211

theorem tailTrace_116609 : CollatzResearch.WordTrace tailWord_116609 prefixEnd_116609 35482350009030815082211 := by
  unfold tailWord_116609
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253079634552983076776881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2835386423035322051184587 4253079634552983076776881)
  ·
    refine ⟨3189809725914737307582661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4253079634552983076776881 3189809725914737307582661)
    ·
      refine ⟨598089323609013245171749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3189809725914737307582661 598089323609013245171749)
      ·
        refine ⟨112141748176689983469703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598089323609013245171749 112141748176689983469703)
        ·
          refine ⟨168212622265034975204555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112141748176689983469703 168212622265034975204555)
          ·
            refine ⟨252318933397552462806833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168212622265034975204555 252318933397552462806833)
            ·
              refine ⟨189239200048164347105125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252318933397552462806833 189239200048164347105125)
              ·
                refine ⟨35482350009030815082211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189239200048164347105125 35482350009030815082211)
                ·
                  rfl

theorem cell19_116609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 4].length) (baseStart_116609 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116609 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116609 prefixEnd_116609 := by exact prefixLift 116609
  have htrace : WordTrace (prefixWord ++ tailWord_116609) baseStart_116609 baseEnd_116609 := by
    simpa [prefixWord, tailWord_116609, baseEnd_116609] using wordTrace_append hprefix tailTrace_116609
  have hstable : (prefixWord ++ tailWord_116609).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116609).length < 2 ^ (prefixWord ++ tailWord_116609).sum := by decide
  have hdescent : baseEnd_116609 < baseStart_116609 := by decide
  rcases family_descends (prefixWord ++ tailWord_116609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116613 : List Nat := [1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_116613 : Nat := 118140960795 + 116613 * 2 ^ 59
def prefixEnd_116613 : Nat := 4983230072969 + 3 ^ 40 * 116613 * 2
def baseEnd_116613 : Nat := 35483567148359990993311

theorem tailTrace_116613 : CollatzResearch.WordTrace tailWord_116613 prefixEnd_116613 35483567148359990993311 := by
  unfold tailWord_116613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253225526538491759922493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2835483684358994506614995 4253225526538491759922493)
  ·
    refine ⟨1594959572451934409970935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4253225526538491759922493 1594959572451934409970935)
    ·
      refine ⟨2392439358677901614956403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1594959572451934409970935 2392439358677901614956403)
      ·
        refine ⟨3588659038016852422434605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2392439358677901614956403 3588659038016852422434605)
        ·
          refine ⟨1345747139256319658412977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3588659038016852422434605 1345747139256319658412977)
          ·
            refine ⟨1009310354442239743809733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1345747139256319658412977 1009310354442239743809733)
            ·
              refine ⟨189245691457919951964325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1009310354442239743809733 189245691457919951964325)
              ·
                refine ⟨35483567148359990993311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189245691457919951964325 35483567148359990993311)
                ·
                  rfl

theorem cell19_116613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_116613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116613 prefixEnd_116613 := by exact prefixLift 116613
  have htrace : WordTrace (prefixWord ++ tailWord_116613) baseStart_116613 baseEnd_116613 := by
    simpa [prefixWord, tailWord_116613, baseEnd_116613] using wordTrace_append hprefix tailTrace_116613
  have hstable : (prefixWord ++ tailWord_116613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116613).length < 2 ^ (prefixWord ++ tailWord_116613).sum := by decide
  have hdescent : baseEnd_116613 < baseStart_116613 := by decide
  rcases family_descends (prefixWord ++ tailWord_116613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116740 : List Nat := [2, 3, 2, 4, 1, 2, 2, 3]
def baseStart_116740 : Nat := 118140960795 + 116740 * 2 ^ 59
def prefixEnd_116740 : Nat := 4983230072969 + 3 ^ 40 * 116740 * 2
def baseEnd_116740 : Nat := 35522211322061326170743

theorem tailTrace_116740 : CollatzResearch.WordTrace tailWord_116740 prefixEnd_116740 35522211322061326170743 := by
  unfold tailWord_116740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2128928798539196224897837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2838571731385594966530449 2128928798539196224897837)
  ·
    refine ⟨798348299452198584336689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2128928798539196224897837 798348299452198584336689)
    ·
      refine ⟨598761224589148938252517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798348299452198584336689 598761224589148938252517)
      ·
        refine ⟨112267729610465425922347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 598761224589148938252517 112267729610465425922347)
        ·
          refine ⟨168401594415698138883521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112267729610465425922347 168401594415698138883521)
          ·
            refine ⟨126301195811773604162641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168401594415698138883521 126301195811773604162641)
            ·
              refine ⟨94725896858830203121981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126301195811773604162641 94725896858830203121981)
              ·
                refine ⟨35522211322061326170743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94725896858830203121981 35522211322061326170743)
                ·
                  rfl

theorem cell19_116740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_116740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116740 prefixEnd_116740 := by exact prefixLift 116740
  have htrace : WordTrace (prefixWord ++ tailWord_116740) baseStart_116740 baseEnd_116740 := by
    simpa [prefixWord, tailWord_116740, baseEnd_116740] using wordTrace_append hprefix tailTrace_116740
  have hstable : (prefixWord ++ tailWord_116740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116740).length < 2 ^ (prefixWord ++ tailWord_116740).sum := by decide
  have hdescent : baseEnd_116740 < baseStart_116740 := by decide
  rcases family_descends (prefixWord ++ tailWord_116740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116765 : List Nat := [1, 4, 2, 2, 2, 1, 7]
def baseStart_116765 : Nat := 118140960795 + 116765 * 2 ^ 59
def prefixEnd_116765 : Nat := 4983230072969 + 3 ^ 40 * 116765 * 2
def baseEnd_116765 : Nat := 11843272814289558538373

theorem tailTrace_116765 : CollatzResearch.WordTrace tailWord_116765 prefixEnd_116765 11843272814289558538373 := by
  unfold tailWord_116765
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258769421987821719455749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2839179614658547812970499 4258769421987821719455749)
  ·
    refine ⟨798519266622716572397953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4258769421987821719455749 798519266622716572397953)
    ·
      refine ⟨598889449967037429298465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 798519266622716572397953 598889449967037429298465)
      ·
        refine ⟨449167087475278071973849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 598889449967037429298465 449167087475278071973849)
        ·
          refine ⟨336875315606458553980387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449167087475278071973849 336875315606458553980387)
          ·
            refine ⟨505312973409687830970581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 336875315606458553980387 505312973409687830970581)
            ·
              refine ⟨11843272814289558538373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 505312973409687830970581 11843272814289558538373)
              ·
                rfl

theorem cell19_116765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 7].length) (baseStart_116765 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116765 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116765 prefixEnd_116765 := by exact prefixLift 116765
  have htrace : WordTrace (prefixWord ++ tailWord_116765) baseStart_116765 baseEnd_116765 := by
    simpa [prefixWord, tailWord_116765, baseEnd_116765] using wordTrace_append hprefix tailTrace_116765
  have hstable : (prefixWord ++ tailWord_116765).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116765).length < 2 ^ (prefixWord ++ tailWord_116765).sum := by decide
  have hdescent : baseEnd_116765 < baseStart_116765 := by decide
  rcases family_descends (prefixWord ++ tailWord_116765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116782 : List Nat := [4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_116782 : Nat := 118140960795 + 116782 * 2 ^ 59
def prefixEnd_116782 : Nat := 4983230072969 + 3 ^ 40 * 116782 * 2
def baseEnd_116782 : Nat := 35534991285017673237295

theorem tailTrace_116782 : CollatzResearch.WordTrace tailWord_116782 prefixEnd_116782 35534991285017673237295 := by
  unfold tailWord_116782
  simp only [CollatzResearch.WordTrace]
  refine ⟨532423682865779202853075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2839592975284155748549733 532423682865779202853075)
  ·
    refine ⟨798635524298668804279613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 532423682865779202853075 798635524298668804279613)
    ·
      refine ⟨299488321612000801604855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 798635524298668804279613 299488321612000801604855)
      ·
        refine ⟨449232482418001202407283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299488321612000801604855 449232482418001202407283)
        ·
          refine ⟨673848723627001803610925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449232482418001202407283 673848723627001803610925)
          ·
            refine ⟨252693271360125676354097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 673848723627001803610925 252693271360125676354097)
            ·
              refine ⟨189519953520094257265573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252693271360125676354097 189519953520094257265573)
              ·
                refine ⟨35534991285017673237295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189519953520094257265573 35534991285017673237295)
                ·
                  rfl

theorem cell19_116782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_116782 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116782 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116782 prefixEnd_116782 := by exact prefixLift 116782
  have htrace : WordTrace (prefixWord ++ tailWord_116782) baseStart_116782 baseEnd_116782 := by
    simpa [prefixWord, tailWord_116782, baseEnd_116782] using wordTrace_append hprefix tailTrace_116782
  have hstable : (prefixWord ++ tailWord_116782).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116782).length < 2 ^ (prefixWord ++ tailWord_116782).sum := by decide
  have hdescent : baseEnd_116782 < baseStart_116782 := by decide
  rcases family_descends (prefixWord ++ tailWord_116782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116784 : List Nat := [2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_116784 : Nat := 118140960795 + 116784 * 2 ^ 59
def prefixEnd_116784 : Nat := 4983230072969 + 3 ^ 40 * 116784 * 2
def baseEnd_116784 : Nat := 35535599854682261192845

theorem tailTrace_116784 : CollatzResearch.WordTrace tailWord_116784 prefixEnd_116784 35535599854682261192845 := by
  unfold tailWord_116784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2129731204459493982198703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2839641605945991976264937 2129731204459493982198703)
  ·
    refine ⟨3194596806689240973298055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2129731204459493982198703 3194596806689240973298055)
    ·
      refine ⟨4791895210033861459947083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3194596806689240973298055 4791895210033861459947083)
      ·
        refine ⟨7187842815050792189920625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4791895210033861459947083 7187842815050792189920625)
        ·
          refine ⟨5390882111288094142440469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7187842815050792189920625 5390882111288094142440469)
          ·
            refine ⟨252697598966629412926897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5390882111288094142440469 252697598966629412926897)
            ·
              refine ⟨189523199224972059695173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252697598966629412926897 189523199224972059695173)
              ·
                refine ⟨35535599854682261192845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189523199224972059695173 35535599854682261192845)
                ·
                  rfl

theorem cell19_116784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_116784 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116784 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116784 prefixEnd_116784 := by exact prefixLift 116784
  have htrace : WordTrace (prefixWord ++ tailWord_116784) baseStart_116784 baseEnd_116784 := by
    simpa [prefixWord, tailWord_116784, baseEnd_116784] using wordTrace_append hprefix tailTrace_116784
  have hstable : (prefixWord ++ tailWord_116784).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116784).length < 2 ^ (prefixWord ++ tailWord_116784).sum := by decide
  have hdescent : baseEnd_116784 < baseStart_116784 := by decide
  rcases family_descends (prefixWord ++ tailWord_116784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116824 : List Nat := [2, 1, 2, 2, 1, 11]
def baseStart_116824 : Nat := 118140960795 + 116824 * 2 ^ 59
def prefixEnd_116824 : Nat := 4983230072969 + 3 ^ 40 * 116824 * 2
def baseEnd_116824 : Nat := 3949752360886002255983

theorem tailTrace_116824 : CollatzResearch.WordTrace tailWord_116824 prefixEnd_116824 3949752360886002255983 := by
  unfold tailWord_116824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2130460664387037397926763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2840614219182716530569017 2130460664387037397926763)
  ·
    refine ⟨3195690996580556096890145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2130460664387037397926763 3195690996580556096890145)
    ·
      refine ⟨2396768247435417072667609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3195690996580556096890145 2396768247435417072667609)
      ·
        refine ⟨1797576185576562804500707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396768247435417072667609 1797576185576562804500707)
        ·
          refine ⟨2696364278364844206751061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797576185576562804500707 2696364278364844206751061)
          ·
            refine ⟨3949752360886002255983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2696364278364844206751061 3949752360886002255983)
            ·
              rfl

theorem cell19_116824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 11].length) (baseStart_116824 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116824 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116824 prefixEnd_116824 := by exact prefixLift 116824
  have htrace : WordTrace (prefixWord ++ tailWord_116824) baseStart_116824 baseEnd_116824 := by
    simpa [prefixWord, tailWord_116824, baseEnd_116824] using wordTrace_append hprefix tailTrace_116824
  have hstable : (prefixWord ++ tailWord_116824).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116824).length < 2 ^ (prefixWord ++ tailWord_116824).sum := by decide
  have hdescent : baseEnd_116824 < baseStart_116824 := by decide
  rcases family_descends (prefixWord ++ tailWord_116824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_116913 : List Nat := [1, 2, 2, 5, 2, 2, 2, 3]
def baseStart_116913 : Nat := 118140960795 + 116913 * 2 ^ 59
def prefixEnd_116913 : Nat := 4983230072969 + 3 ^ 40 * 116913 * 2
def baseEnd_116913 : Nat := 35574852598048184325827

theorem tailTrace_116913 : CollatzResearch.WordTrace tailWord_116913 prefixEnd_116913 35574852598048184325827 := by
  unfold tailWord_116913
  simp only [CollatzResearch.WordTrace]
  refine ⟨4264167425451642995843393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2842778283634428663895595 4264167425451642995843393)
  ·
    refine ⟨3198125569088732246882545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4264167425451642995843393 3198125569088732246882545)
    ·
      refine ⟨2398594176816549185161909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3198125569088732246882545 2398594176816549185161909)
      ·
        refine ⟨224868204076551486108929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2398594176816549185161909 224868204076551486108929)
        ·
          refine ⟨168651153057413614581697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224868204076551486108929 168651153057413614581697)
          ·
            refine ⟨126488364793060210936273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168651153057413614581697 126488364793060210936273)
            ·
              refine ⟨94866273594795158202205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126488364793060210936273 94866273594795158202205)
              ·
                refine ⟨35574852598048184325827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94866273594795158202205 35574852598048184325827)
                ·
                  rfl

theorem cell19_116913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 3].length) (baseStart_116913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_116913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_116913 prefixEnd_116913 := by exact prefixLift 116913
  have htrace : WordTrace (prefixWord ++ tailWord_116913) baseStart_116913 baseEnd_116913 := by
    simpa [prefixWord, tailWord_116913, baseEnd_116913] using wordTrace_append hprefix tailTrace_116913
  have hstable : (prefixWord ++ tailWord_116913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_116913).length < 2 ^ (prefixWord ++ tailWord_116913).sum := by decide
  have hdescent : baseEnd_116913 < baseStart_116913 := by decide
  rcases family_descends (prefixWord ++ tailWord_116913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117029 : List Nat := [1, 3, 1, 2, 5, 1, 3, 3]
def baseStart_117029 : Nat := 118140960795 + 117029 * 2 ^ 59
def prefixEnd_117029 : Nat := 4983230072969 + 3 ^ 40 * 117029 * 2
def baseEnd_117029 : Nat := 35610149638594285747733

theorem tailTrace_117029 : CollatzResearch.WordTrace tailWord_117029 prefixEnd_117029 35610149638594285747733 := by
  unfold tailWord_117029
  simp only [CollatzResearch.WordTrace]
  refine ⟨4268398293031394807066141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2845598862020929871377427 4268398293031394807066141)
  ·
    refine ⟨1600649359886773052649803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4268398293031394807066141 1600649359886773052649803)
    ·
      refine ⟨2400974039830159578974705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600649359886773052649803 2400974039830159578974705)
      ·
        refine ⟨1800730529872619684231029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2400974039830159578974705 1800730529872619684231029)
        ·
          refine ⟨168818487175558095396659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1800730529872619684231029 168818487175558095396659)
          ·
            refine ⟨253227730763337143094989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168818487175558095396659 253227730763337143094989)
            ·
              refine ⟨94960399036251428660621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253227730763337143094989 94960399036251428660621)
              ·
                refine ⟨35610149638594285747733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94960399036251428660621 35610149638594285747733)
                ·
                  rfl

theorem cell19_117029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 3].length) (baseStart_117029 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117029 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117029 prefixEnd_117029 := by exact prefixLift 117029
  have htrace : WordTrace (prefixWord ++ tailWord_117029) baseStart_117029 baseEnd_117029 := by
    simpa [prefixWord, tailWord_117029, baseEnd_117029] using wordTrace_append hprefix tailTrace_117029
  have hstable : (prefixWord ++ tailWord_117029).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117029).length < 2 ^ (prefixWord ++ tailWord_117029).sum := by decide
  have hdescent : baseEnd_117029 < baseStart_117029 := by decide
  rcases family_descends (prefixWord ++ tailWord_117029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117052 : List Nat := [2, 2, 2, 2, 1, 2, 8]
def baseStart_117052 : Nat := 118140960795 + 117052 * 2 ^ 59
def prefixEnd_117052 : Nat := 4983230072969 + 3 ^ 40 * 117052 * 2
def baseEnd_117052 : Nat := 11872382729912349078853

theorem tailTrace_117052 : CollatzResearch.WordTrace tailWord_117052 prefixEnd_117052 11872382729912349078853 := by
  unfold tailWord_117052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2134618585974034867576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2846158114632046490102273 2134618585974034867576705)
  ·
    refine ⟨1600963939480526150682529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2134618585974034867576705 1600963939480526150682529)
    ·
      refine ⟨1200722954610394613011897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1600963939480526150682529 1200722954610394613011897)
      ·
        refine ⟨900542215957795959758923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1200722954610394613011897 900542215957795959758923)
        ·
          refine ⟨1350813323936693939638385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 900542215957795959758923 1350813323936693939638385)
          ·
            refine ⟨1013109992952520454728789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1350813323936693939638385 1013109992952520454728789)
            ·
              refine ⟨11872382729912349078853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1013109992952520454728789 11872382729912349078853)
              ·
                rfl

theorem cell19_117052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_117052 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117052 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117052 prefixEnd_117052 := by exact prefixLift 117052
  have htrace : WordTrace (prefixWord ++ tailWord_117052) baseStart_117052 baseEnd_117052 := by
    simpa [prefixWord, tailWord_117052, baseEnd_117052] using wordTrace_append hprefix tailTrace_117052
  have hstable : (prefixWord ++ tailWord_117052).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117052).length < 2 ^ (prefixWord ++ tailWord_117052).sum := by decide
  have hdescent : baseEnd_117052 < baseStart_117052 := by decide
  rcases family_descends (prefixWord ++ tailWord_117052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117088 : List Nat := [2, 1, 1, 3, 5, 1, 1, 5]
def baseStart_117088 : Nat := 118140960795 + 117088 * 2 ^ 59
def prefixEnd_117088 : Nat := 4983230072969 + 3 ^ 40 * 117088 * 2
def baseEnd_117088 : Nat := 35628102443699630436461

theorem tailTrace_117088 : CollatzResearch.WordTrace tailWord_117088 prefixEnd_117088 35628102443699630436461 := by
  unfold tailWord_117088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135275099908823941731959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2847033466545098588975945 2135275099908823941731959)
  ·
    refine ⟨3202912649863235912597939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2135275099908823941731959 3202912649863235912597939)
    ·
      refine ⟨4804368974794853868896909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202912649863235912597939 4804368974794853868896909)
      ·
        refine ⟨1801638365548070200836341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4804368974794853868896909 1801638365548070200836341)
        ·
          refine ⟨168903596770131581328407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1801638365548070200836341 168903596770131581328407)
          ·
            refine ⟨253355395155197371992611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168903596770131581328407 253355395155197371992611)
            ·
              refine ⟨380033092732796057988917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253355395155197371992611 380033092732796057988917)
              ·
                refine ⟨35628102443699630436461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380033092732796057988917 35628102443699630436461)
                ·
                  rfl

theorem cell19_117088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_117088 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117088 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117088 prefixEnd_117088 := by exact prefixLift 117088
  have htrace : WordTrace (prefixWord ++ tailWord_117088) baseStart_117088 baseEnd_117088 := by
    simpa [prefixWord, tailWord_117088, baseEnd_117088] using wordTrace_append hprefix tailTrace_117088
  have hstable : (prefixWord ++ tailWord_117088).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117088).length < 2 ^ (prefixWord ++ tailWord_117088).sum := by decide
  have hdescent : baseEnd_117088 < baseStart_117088 := by decide
  rcases family_descends (prefixWord ++ tailWord_117088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117122 : List Nat := [3, 4, 2, 1, 2, 1, 2, 4]
def baseStart_117122 : Nat := 118140960795 + 117122 * 2 ^ 59
def prefixEnd_117122 : Nat := 4983230072969 + 3 ^ 40 * 117122 * 2
def baseEnd_117122 : Nat := 35638448127997625680813

theorem tailTrace_117122 : CollatzResearch.WordTrace tailWord_117122 prefixEnd_117122 35638448127997625680813 := by
  unfold tailWord_117122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1067947570423617922550405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2847860187796314460134413 1067947570423617922550405)
  ·
    refine ⟨200240169454428360478201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1067947570423617922550405 200240169454428360478201)
    ·
      refine ⟨150180127090821270358651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200240169454428360478201 150180127090821270358651)
      ·
        refine ⟨225270190636231905537977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150180127090821270358651 225270190636231905537977)
        ·
          refine ⟨168952642977173929153483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225270190636231905537977 168952642977173929153483)
          ·
            refine ⟨253428964465760893730225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168952642977173929153483 253428964465760893730225)
            ·
              refine ⟨190071723349320670297669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253428964465760893730225 190071723349320670297669)
              ·
                refine ⟨35638448127997625680813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190071723349320670297669 35638448127997625680813)
                ·
                  rfl

theorem cell19_117122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_117122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117122 prefixEnd_117122 := by exact prefixLift 117122
  have htrace : WordTrace (prefixWord ++ tailWord_117122) baseStart_117122 baseEnd_117122 := by
    simpa [prefixWord, tailWord_117122, baseEnd_117122] using wordTrace_append hprefix tailTrace_117122
  have hstable : (prefixWord ++ tailWord_117122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117122).length < 2 ^ (prefixWord ++ tailWord_117122).sum := by decide
  have hdescent : baseEnd_117122 < baseStart_117122 := by decide
  rcases family_descends (prefixWord ++ tailWord_117122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117162 : List Nat := [3, 1, 6, 1, 8]
def baseStart_117162 : Nat := 118140960795 + 117162 * 2 ^ 59
def prefixEnd_117162 : Nat := 4983230072969 + 3 ^ 40 * 117162 * 2
def baseEnd_117162 : Nat := 1320393315603310547845

theorem tailTrace_117162 : CollatzResearch.WordTrace tailWord_117162 prefixEnd_117162 1320393315603310547845 := by
  unfold tailWord_117162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1068312300387389630414435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2848832801033039014438493 1068312300387389630414435)
  ·
    refine ⟨1602468450581084445621653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1068312300387389630414435 1602468450581084445621653)
    ·
      refine ⟨75115708620988333388515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1602468450581084445621653 75115708620988333388515)
      ·
        refine ⟨112673562931482500082773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75115708620988333388515 112673562931482500082773)
        ·
          refine ⟨1320393315603310547845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 112673562931482500082773 1320393315603310547845)
          ·
            rfl

theorem cell19_117162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_117162 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117162 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117162 prefixEnd_117162 := by exact prefixLift 117162
  have htrace : WordTrace (prefixWord ++ tailWord_117162) baseStart_117162 baseEnd_117162 := by
    simpa [prefixWord, tailWord_117162, baseEnd_117162] using wordTrace_append hprefix tailTrace_117162
  have hstable : (prefixWord ++ tailWord_117162).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117162).length < 2 ^ (prefixWord ++ tailWord_117162).sum := by decide
  have hdescent : baseEnd_117162 < baseStart_117162 := by decide
  rcases family_descends (prefixWord ++ tailWord_117162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117221 : List Nat := [1, 3, 1, 5, 2, 1, 6]
def baseStart_117221 : Nat := 118140960795 + 117221 * 2 ^ 59
def prefixEnd_117221 : Nat := 4983230072969 + 3 ^ 40 * 117221 * 2
def baseEnd_117221 : Nat := 11889524108798243160181

theorem tailTrace_117221 : CollatzResearch.WordTrace tailWord_117221 prefixEnd_117221 11889524108798243160181 := by
  unfold tailWord_117221
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275401108335811598055517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2850267405557207732037011 4275401108335811598055517)
  ·
    refine ⟨1603275415625929349270819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4275401108335811598055517 1603275415625929349270819)
    ·
      refine ⟨2404913123438894023906229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603275415625929349270819 2404913123438894023906229)
      ·
        refine ⟨225460605322396314741209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2404913123438894023906229 225460605322396314741209)
        ·
          refine ⟨169095453991797236055907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225460605322396314741209 169095453991797236055907)
          ·
            refine ⟨253643180987695854083861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169095453991797236055907 253643180987695854083861)
            ·
              refine ⟨11889524108798243160181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 253643180987695854083861 11889524108798243160181)
              ·
                rfl

theorem cell19_117221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_117221 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117221 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117221 prefixEnd_117221 := by exact prefixLift 117221
  have htrace : WordTrace (prefixWord ++ tailWord_117221) baseStart_117221 baseEnd_117221 := by
    simpa [prefixWord, tailWord_117221, baseEnd_117221] using wordTrace_append hprefix tailTrace_117221
  have hstable : (prefixWord ++ tailWord_117221).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117221).length < 2 ^ (prefixWord ++ tailWord_117221).sum := by decide
  have hdescent : baseEnd_117221 < baseStart_117221 := by decide
  rcases family_descends (prefixWord ++ tailWord_117221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117223 : List Nat := [1, 1, 5, 2, 1, 1, 8]
def baseStart_117223 : Nat := 118140960795 + 117223 * 2 ^ 59
def prefixEnd_117223 : Nat := 4983230072969 + 3 ^ 40 * 117223 * 2
def baseEnd_117223 : Nat := 11889726965353105812031

theorem tailTrace_117223 : CollatzResearch.WordTrace tailWord_117223 prefixEnd_117223 11889726965353105812031 := by
  unfold tailWord_117223
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275474054328565939628323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2850316036219043959752215 4275474054328565939628323)
  ·
    refine ⟨6413211081492848909442485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275474054328565939628323 6413211081492848909442485)
    ·
      refine ⟨601238538889954585260233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6413211081492848909442485 601238538889954585260233)
      ·
        refine ⟨450928904167465938945175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601238538889954585260233 450928904167465938945175)
        ·
          refine ⟨676393356251198908417763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 450928904167465938945175 676393356251198908417763)
          ·
            refine ⟨1014590034376798362626645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676393356251198908417763 1014590034376798362626645)
            ·
              refine ⟨11889726965353105812031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1014590034376798362626645 11889726965353105812031)
              ·
                rfl

theorem cell19_117223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_117223 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117223 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117223 prefixEnd_117223 := by exact prefixLift 117223
  have htrace : WordTrace (prefixWord ++ tailWord_117223) baseStart_117223 baseEnd_117223 := by
    simpa [prefixWord, tailWord_117223, baseEnd_117223] using wordTrace_append hprefix tailTrace_117223
  have hstable : (prefixWord ++ tailWord_117223).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117223).length < 2 ^ (prefixWord ++ tailWord_117223).sum := by decide
  have hdescent : baseEnd_117223 < baseStart_117223 := by decide
  rcases family_descends (prefixWord ++ tailWord_117223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117255 : List Nat := [1, 1, 4, 3, 4, 1, 2, 3]
def baseStart_117255 : Nat := 118140960795 + 117255 * 2 ^ 59
def prefixEnd_117255 : Nat := 4983230072969 + 3 ^ 40 * 117255 * 2
def baseEnd_117255 : Nat := 35678918010692724724895

theorem tailTrace_117255 : CollatzResearch.WordTrace tailWord_117255 prefixEnd_117255 35678918010692724724895 := by
  unfold tailWord_117255
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276641190212635404793219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2851094126808423603195479 4276641190212635404793219)
  ·
    refine ⟨6414961785318953107189829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276641190212635404793219 6414961785318953107189829)
    ·
      refine ⟨1202805334747303707598093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6414961785318953107189829 1202805334747303707598093)
      ·
        refine ⟨451052000530238890349285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1202805334747303707598093 451052000530238890349285)
        ·
          refine ⟨84572250099419791940491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451052000530238890349285 84572250099419791940491)
          ·
            refine ⟨126858375149129687910737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84572250099419791940491 126858375149129687910737)
            ·
              refine ⟨95143781361847265933053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126858375149129687910737 95143781361847265933053)
              ·
                refine ⟨35678918010692724724895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95143781361847265933053 35678918010692724724895)
                ·
                  rfl

theorem cell19_117255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 2, 3].length) (baseStart_117255 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117255 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117255 prefixEnd_117255 := by exact prefixLift 117255
  have htrace : WordTrace (prefixWord ++ tailWord_117255) baseStart_117255 baseEnd_117255 := by
    simpa [prefixWord, tailWord_117255, baseEnd_117255] using wordTrace_append hprefix tailTrace_117255
  have hstable : (prefixWord ++ tailWord_117255).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117255).length < 2 ^ (prefixWord ++ tailWord_117255).sum := by decide
  have hdescent : baseEnd_117255 < baseStart_117255 := by decide
  rcases family_descends (prefixWord ++ tailWord_117255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117259 : List Nat := [1, 1, 1, 1, 7, 1, 4, 3]
def baseStart_117259 : Nat := 118140960795 + 117259 * 2 ^ 59
def prefixEnd_117259 : Nat := 4983230072969 + 3 ^ 40 * 117259 * 2
def baseEnd_117259 : Nat := 35680135150021900635995

theorem tailTrace_117259 : CollatzResearch.WordTrace tailWord_117259 prefixEnd_117259 35680135150021900635995 := by
  unfold tailWord_117259
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276787082198144087938831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2851191388132096058625887 4276787082198144087938831)
  ·
    refine ⟨6415180623297216131908247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276787082198144087938831 6415180623297216131908247)
    ·
      refine ⟨9622770934945824197862371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415180623297216131908247 9622770934945824197862371)
      ·
        refine ⟨14434156402418736296793557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622770934945824197862371 14434156402418736296793557)
        ·
          refine ⟨338300540681689131956099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 14434156402418736296793557 338300540681689131956099)
          ·
            refine ⟨507450811022533697934149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338300540681689131956099 507450811022533697934149)
            ·
              refine ⟨95147027066725068362653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 507450811022533697934149 95147027066725068362653)
              ·
                refine ⟨35680135150021900635995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95147027066725068362653 35680135150021900635995)
                ·
                  rfl

theorem cell19_117259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 3].length) (baseStart_117259 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117259 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117259 prefixEnd_117259 := by exact prefixLift 117259
  have htrace : WordTrace (prefixWord ++ tailWord_117259) baseStart_117259 baseEnd_117259 := by
    simpa [prefixWord, tailWord_117259, baseEnd_117259] using wordTrace_append hprefix tailTrace_117259
  have hstable : (prefixWord ++ tailWord_117259).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117259).length < 2 ^ (prefixWord ++ tailWord_117259).sum := by decide
  have hdescent : baseEnd_117259 < baseStart_117259 := by decide
  rcases family_descends (prefixWord ++ tailWord_117259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117299 : List Nat := [1, 1, 1, 2, 4, 2, 4, 4]
def baseStart_117299 : Nat := 118140960795 + 117299 * 2 ^ 59
def prefixEnd_117299 : Nat := 4983230072969 + 3 ^ 40 * 117299 * 2
def baseEnd_117299 : Nat := 35692306543313659746997

theorem tailTrace_117299 : CollatzResearch.WordTrace tailWord_117299 prefixEnd_117299 35692306543313659746997 := by
  unfold tailWord_117299
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278246002053230919394951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2852164001368820612929967 4278246002053230919394951)
  ·
    refine ⟨6417369003079846379092427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278246002053230919394951 6417369003079846379092427)
    ·
      refine ⟨9626053504619769568638641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417369003079846379092427 9626053504619769568638641)
      ·
        refine ⟨7219540128464827176478981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9626053504619769568638641 7219540128464827176478981)
        ·
          refine ⟨1353663774087155095589809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7219540128464827176478981 1353663774087155095589809)
          ·
            refine ⟨1015247830565366321692357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353663774087155095589809 1015247830565366321692357)
            ·
              refine ⟨190358968231006185317317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1015247830565366321692357 190358968231006185317317)
              ·
                refine ⟨35692306543313659746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190358968231006185317317 35692306543313659746997)
                ·
                  rfl

theorem cell19_117299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 4].length) (baseStart_117299 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117299 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117299 prefixEnd_117299 := by exact prefixLift 117299
  have htrace : WordTrace (prefixWord ++ tailWord_117299) baseStart_117299 baseEnd_117299 := by
    simpa [prefixWord, tailWord_117299, baseEnd_117299] using wordTrace_append hprefix tailTrace_117299
  have hstable : (prefixWord ++ tailWord_117299).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117299).length < 2 ^ (prefixWord ++ tailWord_117299).sum := by decide
  have hdescent : baseEnd_117299 < baseStart_117299 := by decide
  rcases family_descends (prefixWord ++ tailWord_117299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117352 : List Nat := [2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_117352 : Nat := 118140960795 + 117352 * 2 ^ 59
def prefixEnd_117352 : Nat := 4983230072969 + 3 ^ 40 * 117352 * 2
def baseEnd_117352 : Nat := 35708433639425240569075

theorem tailTrace_117352 : CollatzResearch.WordTrace tailWord_117352 prefixEnd_117352 35708433639425240569075 := by
  unfold tailWord_117352
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140089535430610485537155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2853452713907480647382873 2140089535430610485537155)
  ·
    refine ⟨3210134303145915728305733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2140089535430610485537155 3210134303145915728305733)
    ·
      refine ⟨601900181839859199057325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3210134303145915728305733 601900181839859199057325)
      ·
        refine ⟨225712568189947199646497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601900181839859199057325 225712568189947199646497)
        ·
          refine ⟨169284426142460399734873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225712568189947199646497 169284426142460399734873)
          ·
            refine ⟨126963319606845299801155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169284426142460399734873 126963319606845299801155)
            ·
              refine ⟨190444979410267949701733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126963319606845299801155 190444979410267949701733)
              ·
                refine ⟨35708433639425240569075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190444979410267949701733 35708433639425240569075)
                ·
                  rfl

theorem cell19_117352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_117352 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117352 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117352 prefixEnd_117352 := by exact prefixLift 117352
  have htrace : WordTrace (prefixWord ++ tailWord_117352) baseStart_117352 baseEnd_117352 := by
    simpa [prefixWord, tailWord_117352, baseEnd_117352] using wordTrace_append hprefix tailTrace_117352
  have hstable : (prefixWord ++ tailWord_117352).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117352).length < 2 ^ (prefixWord ++ tailWord_117352).sum := by decide
  have hdescent : baseEnd_117352 < baseStart_117352 := by decide
  rcases family_descends (prefixWord ++ tailWord_117352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117356 : List Nat := [2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_117356 : Nat := 118140960795 + 117356 * 2 ^ 59
def prefixEnd_117356 : Nat := 4983230072969 + 3 ^ 40 * 117356 * 2
def baseEnd_117356 : Nat := 35709650778754416480175

theorem tailTrace_117356 : CollatzResearch.WordTrace tailWord_117356 prefixEnd_117356 35709650778754416480175 := by
  unfold tailWord_117356
  simp only [CollatzResearch.WordTrace]
  refine ⟨2140162481423364827109961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2853549975231153102813281 2140162481423364827109961)
  ·
    refine ⟨1605121861067523620332471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2140162481423364827109961 1605121861067523620332471)
    ·
      refine ⟨2407682791601285430498707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1605121861067523620332471 2407682791601285430498707)
      ·
        refine ⟨3611524187401928145748061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407682791601285430498707 3611524187401928145748061)
        ·
          refine ⟨1354321570275723054655523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3611524187401928145748061 1354321570275723054655523)
          ·
            refine ⟨2031482355413584581983285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354321570275723054655523 2031482355413584581983285)
            ·
              refine ⟨190451470820023554560933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2031482355413584581983285 190451470820023554560933)
              ·
                refine ⟨35709650778754416480175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190451470820023554560933 35709650778754416480175)
                ·
                  rfl

theorem cell19_117356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_117356 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117356 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117356 prefixEnd_117356 := by exact prefixLift 117356
  have htrace : WordTrace (prefixWord ++ tailWord_117356) baseStart_117356 baseEnd_117356 := by
    simpa [prefixWord, tailWord_117356, baseEnd_117356] using wordTrace_append hprefix tailTrace_117356
  have hstable : (prefixWord ++ tailWord_117356).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117356).length < 2 ^ (prefixWord ++ tailWord_117356).sum := by decide
  have hdescent : baseEnd_117356 < baseStart_117356 := by decide
  rcases family_descends (prefixWord ++ tailWord_117356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117468 : List Nat := [2, 2, 5, 1, 1, 1, 1, 6]
def baseStart_117468 : Nat := 118140960795 + 117468 * 2 ^ 59
def prefixEnd_117468 : Nat := 4983230072969 + 3 ^ 40 * 117468 * 2
def baseEnd_117468 : Nat := 35743730679971341990981

theorem tailTrace_117468 : CollatzResearch.WordTrace tailWord_117468 prefixEnd_117468 35743730679971341990981 := by
  unfold tailWord_117468
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142204969220486391148529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2856273292293981854864705 2142204969220486391148529)
  ·
    refine ⟨1606653726915364793361397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2142204969220486391148529 1606653726915364793361397)
    ·
      refine ⟨150623786898315449377631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1606653726915364793361397 150623786898315449377631)
      ·
        refine ⟨225935680347473174066447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150623786898315449377631 225935680347473174066447)
        ·
          refine ⟨338903520521209761099671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225935680347473174066447 338903520521209761099671)
          ·
            refine ⟨508355280781814641649507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338903520521209761099671 508355280781814641649507)
            ·
              refine ⟨762532921172721962474261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508355280781814641649507 762532921172721962474261)
              ·
                refine ⟨35743730679971341990981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 762532921172721962474261 35743730679971341990981)
                ·
                  rfl

theorem cell19_117468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_117468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117468 prefixEnd_117468 := by exact prefixLift 117468
  have htrace : WordTrace (prefixWord ++ tailWord_117468) baseStart_117468 baseEnd_117468 := by
    simpa [prefixWord, tailWord_117468, baseEnd_117468] using wordTrace_append hprefix tailTrace_117468
  have hstable : (prefixWord ++ tailWord_117468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117468).length < 2 ^ (prefixWord ++ tailWord_117468).sum := by decide
  have hdescent : baseEnd_117468 < baseStart_117468 := by decide
  rcases family_descends (prefixWord ++ tailWord_117468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117529 : List Nat := [1, 2, 1, 2, 1, 1, 1, 10]
def baseStart_117529 : Nat := 118140960795 + 117529 * 2 ^ 59
def prefixEnd_117529 : Nat := 4983230072969 + 3 ^ 40 * 117529 * 2
def baseEnd_117529 : Nat := 35762292054741274635259

theorem tailTrace_117529 : CollatzResearch.WordTrace tailWord_117529 prefixEnd_117529 35762292054741274635259 := by
  unfold tailWord_117529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4286634791219980200267641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2857756527479986800178427 4286634791219980200267641)
  ·
    refine ⟨3214976093414985150200731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4286634791219980200267641 3214976093414985150200731)
    ·
      refine ⟨4822464140122477725301097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214976093414985150200731 4822464140122477725301097)
      ·
        refine ⟨3616848105091858293975823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4822464140122477725301097 3616848105091858293975823)
        ·
          refine ⟨5425272157637787440963735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616848105091858293975823 5425272157637787440963735)
          ·
            refine ⟨8137908236456681161445603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5425272157637787440963735 8137908236456681161445603)
            ·
              refine ⟨12206862354685021742168405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8137908236456681161445603 12206862354685021742168405)
              ·
                refine ⟨35762292054741274635259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 12206862354685021742168405 35762292054741274635259)
                ·
                  rfl

theorem cell19_117529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_117529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117529 prefixEnd_117529 := by exact prefixLift 117529
  have htrace : WordTrace (prefixWord ++ tailWord_117529) baseStart_117529 baseEnd_117529 := by
    simpa [prefixWord, tailWord_117529, baseEnd_117529] using wordTrace_append hprefix tailTrace_117529
  have hstable : (prefixWord ++ tailWord_117529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117529).length < 2 ^ (prefixWord ++ tailWord_117529).sum := by decide
  have hdescent : baseEnd_117529 < baseStart_117529 := by decide
  rcases family_descends (prefixWord ++ tailWord_117529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117544 : List Nat := [2, 1, 5, 1, 1, 1, 5, 3]
def baseStart_117544 : Nat := 118140960795 + 117544 * 2 ^ 59
def prefixEnd_117544 : Nat := 4983230072969 + 3 ^ 40 * 117544 * 2
def baseEnd_117544 : Nat := 35766856327225684301885

theorem tailTrace_117544 : CollatzResearch.WordTrace tailWord_117544 prefixEnd_117544 35766856327225684301885 := by
  unfold tailWord_117544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143590943082818881031843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2858121257443758508042457 2143590943082818881031843)
  ·
    refine ⟨3215386414624228321547765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2143590943082818881031843 3215386414624228321547765)
    ·
      refine ⟨301442476371021405145103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3215386414624228321547765 301442476371021405145103)
      ·
        refine ⟨452163714556532107717655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301442476371021405145103 452163714556532107717655)
        ·
          refine ⟨678245571834798161576483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452163714556532107717655 678245571834798161576483)
          ·
            refine ⟨1017368357752197242364725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678245571834798161576483 1017368357752197242364725)
            ·
              refine ⟨95378283539268491471693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1017368357752197242364725 95378283539268491471693)
              ·
                refine ⟨35766856327225684301885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95378283539268491471693 35766856327225684301885)
                ·
                  rfl

theorem cell19_117544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 3].length) (baseStart_117544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117544 prefixEnd_117544 := by exact prefixLift 117544
  have htrace : WordTrace (prefixWord ++ tailWord_117544) baseStart_117544 baseEnd_117544 := by
    simpa [prefixWord, tailWord_117544, baseEnd_117544] using wordTrace_append hprefix tailTrace_117544
  have hstable : (prefixWord ++ tailWord_117544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117544).length < 2 ^ (prefixWord ++ tailWord_117544).sum := by decide
  have hdescent : baseEnd_117544 < baseStart_117544 := by decide
  rcases family_descends (prefixWord ++ tailWord_117544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117603 : List Nat := [1, 1, 1, 5, 3, 2, 1, 5]
def baseStart_117603 : Nat := 118140960795 + 117603 * 2 ^ 59
def prefixEnd_117603 : Nat := 4983230072969 + 3 ^ 40 * 117603 * 2
def baseEnd_117603 : Nat := 35784809132331028990613

theorem tailTrace_117603 : CollatzResearch.WordTrace tailWord_117603 prefixEnd_117603 35784809132331028990613 := by
  unfold tailWord_117603
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289333792951890838461463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2859555861967927225640975 4289333792951890838461463)
  ·
    refine ⟨6434000689427836257692195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289333792951890838461463 6434000689427836257692195)
    ·
      refine ⟨9651001034141754386538293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434000689427836257692195 9651001034141754386538293)
      ·
        refine ⟨904781346950789473737965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9651001034141754386538293 904781346950789473737965)
        ·
          refine ⟨339293005106546052651737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904781346950789473737965 339293005106546052651737)
          ·
            refine ⟨254469753829909539488803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339293005106546052651737 254469753829909539488803)
            ·
              refine ⟨381704630744864309233205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254469753829909539488803 381704630744864309233205)
              ·
                refine ⟨35784809132331028990613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381704630744864309233205 35784809132331028990613)
                ·
                  rfl

theorem cell19_117603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_117603 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117603 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117603 prefixEnd_117603 := by exact prefixLift 117603
  have htrace : WordTrace (prefixWord ++ tailWord_117603) baseStart_117603 baseEnd_117603 := by
    simpa [prefixWord, tailWord_117603, baseEnd_117603] using wordTrace_append hprefix tailTrace_117603
  have hstable : (prefixWord ++ tailWord_117603).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117603).length < 2 ^ (prefixWord ++ tailWord_117603).sum := by decide
  have hdescent : baseEnd_117603 < baseStart_117603 := by decide
  rcases family_descends (prefixWord ++ tailWord_117603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117641 : List Nat := [1, 2, 1, 1, 5, 3, 2, 4]
def baseStart_117641 : Nat := 118140960795 + 117641 * 2 ^ 59
def prefixEnd_117641 : Nat := 4983230072969 + 3 ^ 40 * 117641 * 2
def baseEnd_117641 : Nat := 35796371955958200146065

theorem tailTrace_117641 : CollatzResearch.WordTrace tailWord_117641 prefixEnd_117641 35796371955958200146065 := by
  unfold tailWord_117641
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290719766814223328344777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2860479844542815552229851 4290719766814223328344777)
  ·
    refine ⟨3218039825110667496258583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4290719766814223328344777 3218039825110667496258583)
    ·
      refine ⟨4827059737666001244387875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218039825110667496258583 4827059737666001244387875)
      ·
        refine ⟨7240589606499001866581813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827059737666001244387875 7240589606499001866581813)
        ·
          refine ⟨678805275609281424992045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7240589606499001866581813 678805275609281424992045)
          ·
            refine ⟨254551978353480534372017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678805275609281424992045 254551978353480534372017)
            ·
              refine ⟨190913983765110400779013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254551978353480534372017 190913983765110400779013)
              ·
                refine ⟨35796371955958200146065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190913983765110400779013 35796371955958200146065)
                ·
                  rfl

theorem cell19_117641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_117641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117641 prefixEnd_117641 := by exact prefixLift 117641
  have htrace : WordTrace (prefixWord ++ tailWord_117641) baseStart_117641 baseEnd_117641 := by
    simpa [prefixWord, tailWord_117641, baseEnd_117641] using wordTrace_append hprefix tailTrace_117641
  have hstable : (prefixWord ++ tailWord_117641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117641).length < 2 ^ (prefixWord ++ tailWord_117641).sum := by decide
  have hdescent : baseEnd_117641 < baseStart_117641 := by decide
  rcases family_descends (prefixWord ++ tailWord_117641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117643 : List Nat := [1, 1, 1, 1, 4, 2, 3, 6]
def baseStart_117643 : Nat := 118140960795 + 117643 * 2 ^ 59
def prefixEnd_117643 : Nat := 4983230072969 + 3 ^ 40 * 117643 * 2
def baseEnd_117643 : Nat := 35796980525622788101615

theorem tailTrace_117643 : CollatzResearch.WordTrace tailWord_117643 prefixEnd_117643 35796980525622788101615 := by
  unfold tailWord_117643
  simp only [CollatzResearch.WordTrace]
  refine ⟨4290792712806977669917583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2860528475204651779945055 4290792712806977669917583)
  ·
    refine ⟨6436189069210466504876375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4290792712806977669917583 6436189069210466504876375)
    ·
      refine ⟨9654283603815699757314563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436189069210466504876375 9654283603815699757314563)
      ·
        refine ⟨14481425405723549635971845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654283603815699757314563 14481425405723549635971845)
        ·
          refine ⟨2715267263573165556744721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14481425405723549635971845 2715267263573165556744721)
          ·
            refine ⟨2036450447679874167558541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715267263573165556744721 2036450447679874167558541)
            ·
              refine ⟨763668917879952812834453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036450447679874167558541 763668917879952812834453)
              ·
                refine ⟨35796980525622788101615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 763668917879952812834453 35796980525622788101615)
                ·
                  rfl

theorem cell19_117643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_117643 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117643 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117643 prefixEnd_117643 := by exact prefixLift 117643
  have htrace : WordTrace (prefixWord ++ tailWord_117643) baseStart_117643 baseEnd_117643 := by
    simpa [prefixWord, tailWord_117643, baseEnd_117643] using wordTrace_append hprefix tailTrace_117643
  have hstable : (prefixWord ++ tailWord_117643).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117643).length < 2 ^ (prefixWord ++ tailWord_117643).sum := by decide
  have hdescent : baseEnd_117643 < baseStart_117643 := by decide
  rcases family_descends (prefixWord ++ tailWord_117643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117677 : List Nat := [1, 5, 2, 3, 1, 7]
def baseStart_117677 : Nat := 118140960795 + 117677 * 2 ^ 59
def prefixEnd_117677 : Nat := 4983230072969 + 3 ^ 40 * 117677 * 2
def baseEnd_117677 : Nat := 3978591801102309260663

theorem tailTrace_117677 : CollatzResearch.WordTrace tailWord_117677 prefixEnd_117677 3978591801102309260663 := by
  unfold tailWord_117677
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292032794683801476655285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2861355196455867651103523 4292032794683801476655285)
  ·
    refine ⟨402378074501606388436433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4292032794683801476655285 402378074501606388436433)
    ·
      refine ⟨301783555876204791327325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402378074501606388436433 301783555876204791327325)
      ·
        refine ⟨113168833453576796747747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301783555876204791327325 113168833453576796747747)
        ·
          refine ⟨169753250180365195121621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113168833453576796747747 169753250180365195121621)
          ·
            refine ⟨3978591801102309260663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 169753250180365195121621 3978591801102309260663)
            ·
              rfl

theorem cell19_117677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 7].length) (baseStart_117677 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117677 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117677 prefixEnd_117677 := by exact prefixLift 117677
  have htrace : WordTrace (prefixWord ++ tailWord_117677) baseStart_117677 baseEnd_117677 := by
    simpa [prefixWord, tailWord_117677, baseEnd_117677] using wordTrace_append hprefix tailTrace_117677
  have hstable : (prefixWord ++ tailWord_117677).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117677).length < 2 ^ (prefixWord ++ tailWord_117677).sum := by decide
  have hdescent : baseEnd_117677 < baseStart_117677 := by decide
  rcases family_descends (prefixWord ++ tailWord_117677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117681 : List Nat := [1, 2, 2, 4, 10]
def baseStart_117681 : Nat := 118140960795 + 117681 * 2 ^ 59
def prefixEnd_117681 : Nat := 4983230072969 + 3 ^ 40 * 117681 * 2
def baseEnd_117681 : Nat := 1326242346268517009521

theorem tailTrace_117681 : CollatzResearch.WordTrace tailWord_117681 prefixEnd_117681 1326242346268517009521 := by
  unfold tailWord_117681
  simp only [CollatzResearch.WordTrace]
  refine ⟨4292178686669310159800897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2861452457779540106533931 4292178686669310159800897)
  ·
    refine ⟨3219134015001982619850673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4292178686669310159800897 3219134015001982619850673)
    ·
      refine ⟨2414350511251486964888005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3219134015001982619850673 2414350511251486964888005)
      ·
        refine ⟨452690720859653805916501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2414350511251486964888005 452690720859653805916501)
        ·
          refine ⟨1326242346268517009521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 452690720859653805916501 1326242346268517009521)
          ·
            rfl

theorem cell19_117681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 10].length) (baseStart_117681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117681 prefixEnd_117681 := by exact prefixLift 117681
  have htrace : WordTrace (prefixWord ++ tailWord_117681) baseStart_117681 baseEnd_117681 := by
    simpa [prefixWord, tailWord_117681, baseEnd_117681] using wordTrace_append hprefix tailTrace_117681
  have hstable : (prefixWord ++ tailWord_117681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117681).length < 2 ^ (prefixWord ++ tailWord_117681).sum := by decide
  have hdescent : baseEnd_117681 < baseStart_117681 := by decide
  rcases family_descends (prefixWord ++ tailWord_117681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117709 : List Nat := [1, 6, 3, 1, 1, 1, 3, 3]
def baseStart_117709 : Nat := 118140960795 + 117709 * 2 ^ 59
def prefixEnd_117709 : Nat := 4983230072969 + 3 ^ 40 * 117709 * 2
def baseEnd_117709 : Nat := 35817063324554190634769

theorem tailTrace_117709 : CollatzResearch.WordTrace tailWord_117709 prefixEnd_117709 35817063324554190634769 := by
  unfold tailWord_117709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293199930567870941820181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2862133287045247294546787 4293199930567870941820181)
  ·
    refine ⟨201243746745368950397821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4293199930567870941820181 201243746745368950397821)
    ·
      refine ⟨75466405029513356399183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201243746745368950397821 75466405029513356399183)
      ·
        refine ⟨113199607544270034598775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75466405029513356399183 113199607544270034598775)
        ·
          refine ⟨169799411316405051898163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113199607544270034598775 169799411316405051898163)
          ·
            refine ⟨254699116974607577847245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169799411316405051898163 254699116974607577847245)
            ·
              refine ⟨95512168865477841692717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254699116974607577847245 95512168865477841692717)
              ·
                refine ⟨35817063324554190634769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95512168865477841692717 35817063324554190634769)
                ·
                  rfl

theorem cell19_117709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 3, 3].length) (baseStart_117709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117709 prefixEnd_117709 := by exact prefixLift 117709
  have htrace : WordTrace (prefixWord ++ tailWord_117709) baseStart_117709 baseEnd_117709 := by
    simpa [prefixWord, tailWord_117709, baseEnd_117709] using wordTrace_append hprefix tailTrace_117709
  have hstable : (prefixWord ++ tailWord_117709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117709).length < 2 ^ (prefixWord ++ tailWord_117709).sum := by decide
  have hdescent : baseEnd_117709 < baseStart_117709 := by decide
  rcases family_descends (prefixWord ++ tailWord_117709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117757 : List Nat := [1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_117757 : Nat := 118140960795 + 117757 * 2 ^ 59
def prefixEnd_117757 : Nat := 4983230072969 + 3 ^ 40 * 117757 * 2
def baseEnd_117757 : Nat := 35831668996504301567971

theorem tailTrace_117757 : CollatzResearch.WordTrace tailWord_117757 prefixEnd_117757 35831668996504301567971 := by
  unfold tailWord_117757
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294950634393975139567525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2863300422929316759711683 4294950634393975139567525)
  ·
    refine ⟨805303243948870338668911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4294950634393975139567525 805303243948870338668911)
    ·
      refine ⟨1207954865923305508003367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805303243948870338668911 1207954865923305508003367)
      ·
        refine ⟨1811932298884958262005051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207954865923305508003367 1811932298884958262005051)
        ·
          refine ⟨2717898448327437393007577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811932298884958262005051 2717898448327437393007577)
          ·
            refine ⟨2038423836245578044755683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717898448327437393007577 2038423836245578044755683)
            ·
              refine ⟨3057635754368367067133525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2038423836245578044755683 3057635754368367067133525)
              ·
                refine ⟨35831668996504301567971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3057635754368367067133525 35831668996504301567971)
                ·
                  rfl

theorem cell19_117757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_117757 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117757 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117757 prefixEnd_117757 := by exact prefixLift 117757
  have htrace : WordTrace (prefixWord ++ tailWord_117757) baseStart_117757 baseEnd_117757 := by
    simpa [prefixWord, tailWord_117757, baseEnd_117757] using wordTrace_append hprefix tailTrace_117757
  have hstable : (prefixWord ++ tailWord_117757).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117757).length < 2 ^ (prefixWord ++ tailWord_117757).sum := by decide
  have hdescent : baseEnd_117757 < baseStart_117757 := by decide
  rcases family_descends (prefixWord ++ tailWord_117757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117772 : List Nat := [2, 2, 1, 2, 3, 4, 2, 3]
def baseStart_117772 : Nat := 118140960795 + 117772 * 2 ^ 59
def prefixEnd_117772 : Nat := 4983230072969 + 3 ^ 40 * 117772 * 2
def baseEnd_117772 : Nat := 35836233268988711234597

theorem tailTrace_117772 : CollatzResearch.WordTrace tailWord_117772 prefixEnd_117772 35836233268988711234597 := by
  unfold tailWord_117772
  simp only [CollatzResearch.WordTrace]
  refine ⟨2147748864669816350681785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2863665152893088467575713 2147748864669816350681785)
  ·
    refine ⟨1610811648502362263011339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2147748864669816350681785 1610811648502362263011339)
    ·
      refine ⟨2416217472753543394517009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610811648502362263011339 2416217472753543394517009)
      ·
        refine ⟨1812163104565157545887757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416217472753543394517009 1812163104565157545887757)
        ·
          refine ⟨679561164211934079707909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1812163104565157545887757 679561164211934079707909)
          ·
            refine ⟨127417718289737639945233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 679561164211934079707909 127417718289737639945233)
            ·
              refine ⟨95563288717303229958925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127417718289737639945233 95563288717303229958925)
              ·
                refine ⟨35836233268988711234597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95563288717303229958925 35836233268988711234597)
                ·
                  rfl

theorem cell19_117772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_117772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117772 prefixEnd_117772 := by exact prefixLift 117772
  have htrace : WordTrace (prefixWord ++ tailWord_117772) baseStart_117772 baseEnd_117772 := by
    simpa [prefixWord, tailWord_117772, baseEnd_117772] using wordTrace_append hprefix tailTrace_117772
  have hstable : (prefixWord ++ tailWord_117772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117772).length < 2 ^ (prefixWord ++ tailWord_117772).sum := by decide
  have hdescent : baseEnd_117772 < baseStart_117772 := by decide
  rcases family_descends (prefixWord ++ tailWord_117772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117774 : List Nat := [4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_117774 : Nat := 118140960795 + 117774 * 2 ^ 59
def prefixEnd_117774 : Nat := 4983230072969 + 3 ^ 40 * 117774 * 2
def baseEnd_117774 : Nat := 35836841838653299190147

theorem tailTrace_117774 : CollatzResearch.WordTrace tailWord_117774 prefixEnd_117774 35836841838653299190147 := by
  unfold tailWord_117774
  simp only [CollatzResearch.WordTrace]
  refine ⟨536946334416548380367047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2863713783554924695290917 536946334416548380367047)
  ·
    refine ⟨805419501624822570550571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 536946334416548380367047 805419501624822570550571)
    ·
      refine ⟨1208129252437233855825857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 805419501624822570550571 1208129252437233855825857)
      ·
        refine ⟨906096939327925391869393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208129252437233855825857 906096939327925391869393)
        ·
          refine ⟨679572704495944043902045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906096939327925391869393 679572704495944043902045)
          ·
            refine ⟨254839764185979016463267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 679572704495944043902045 254839764185979016463267)
            ·
              refine ⟨382259646278968524694901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254839764185979016463267 382259646278968524694901)
              ·
                refine ⟨35836841838653299190147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 382259646278968524694901 35836841838653299190147)
                ·
                  rfl

theorem cell19_117774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_117774 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117774 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117774 prefixEnd_117774 := by exact prefixLift 117774
  have htrace : WordTrace (prefixWord ++ tailWord_117774) baseStart_117774 baseEnd_117774 := by
    simpa [prefixWord, tailWord_117774, baseEnd_117774] using wordTrace_append hprefix tailTrace_117774
  have hstable : (prefixWord ++ tailWord_117774).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117774).length < 2 ^ (prefixWord ++ tailWord_117774).sum := by decide
  have hdescent : baseEnd_117774 < baseStart_117774 := by decide
  rcases family_descends (prefixWord ++ tailWord_117774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117793 : List Nat := [1, 2, 3, 2, 3, 3, 5]
def baseStart_117793 : Nat := 118140960795 + 117793 * 2 ^ 59
def prefixEnd_117793 : Nat := 4983230072969 + 3 ^ 40 * 117793 * 2
def baseEnd_117793 : Nat := 11947541083488961589291

theorem tailTrace_117793 : CollatzResearch.WordTrace tailWord_117793 prefixEnd_117793 11947541083488961589291 := by
  unfold tailWord_117793
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296263662263553287878033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2864175774842368858585355 4296263662263553287878033)
  ·
    refine ⟨3222197746697664965908525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4296263662263553287878033 3222197746697664965908525)
    ·
      refine ⟨1208324155011624362215697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3222197746697664965908525 1208324155011624362215697)
      ·
        refine ⟨906243116258718271661773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208324155011624362215697 906243116258718271661773)
        ·
          refine ⟨339841168597019351873165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 906243116258718271661773 339841168597019351873165)
          ·
            refine ⟨127440438223882256952437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339841168597019351873165 127440438223882256952437)
            ·
              refine ⟨11947541083488961589291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127440438223882256952437 11947541083488961589291)
              ·
                rfl

theorem cell19_117793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_117793 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117793 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117793 prefixEnd_117793 := by exact prefixLift 117793
  have htrace : WordTrace (prefixWord ++ tailWord_117793) baseStart_117793 baseEnd_117793 := by
    simpa [prefixWord, tailWord_117793, baseEnd_117793] using wordTrace_append hprefix tailTrace_117793
  have hstable : (prefixWord ++ tailWord_117793).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117793).length < 2 ^ (prefixWord ++ tailWord_117793).sum := by decide
  have hdescent : baseEnd_117793 < baseStart_117793 := by decide
  rcases family_descends (prefixWord ++ tailWord_117793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117795 : List Nat := [1, 1, 1, 4, 3, 2, 7]
def baseStart_117795 : Nat := 118140960795 + 117795 * 2 ^ 59
def prefixEnd_117795 : Nat := 4983230072969 + 3 ^ 40 * 117795 * 2
def baseEnd_117795 : Nat := 11947743940043824241141

theorem tailTrace_117795 : CollatzResearch.WordTrace tailWord_117795 prefixEnd_117795 11947743940043824241141 := by
  unfold tailWord_117795
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296336608256307629450839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2864224405504205086300559 4296336608256307629450839)
  ·
    refine ⟨6444504912384461444176259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296336608256307629450839 6444504912384461444176259)
    ·
      refine ⟨9666757368576692166264389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6444504912384461444176259 9666757368576692166264389)
      ·
        refine ⟨1812517006608129781174573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9666757368576692166264389 1812517006608129781174573)
        ·
          refine ⟨679693877478048667940465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1812517006608129781174573 679693877478048667940465)
          ·
            refine ⟨509770408108536500955349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 679693877478048667940465 509770408108536500955349)
            ·
              refine ⟨11947743940043824241141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 509770408108536500955349 11947743940043824241141)
              ·
                rfl

theorem cell19_117795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_117795 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117795 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117795 prefixEnd_117795 := by exact prefixLift 117795
  have htrace : WordTrace (prefixWord ++ tailWord_117795) baseStart_117795 baseEnd_117795 := by
    simpa [prefixWord, tailWord_117795, baseEnd_117795] using wordTrace_append hprefix tailTrace_117795
  have hstable : (prefixWord ++ tailWord_117795).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117795).length < 2 ^ (prefixWord ++ tailWord_117795).sum := by decide
  have hdescent : baseEnd_117795 < baseStart_117795 := by decide
  rcases family_descends (prefixWord ++ tailWord_117795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117846 : List Nat := [5, 2, 2, 1, 3, 6]
def baseStart_117846 : Nat := 118140960795 + 117846 * 2 ^ 59
def prefixEnd_117846 : Nat := 4983230072969 + 3 ^ 40 * 117846 * 2
def baseEnd_117846 : Nat := 3984305594064273954439

theorem tailTrace_117846 : CollatzResearch.WordTrace tailWord_117846 prefixEnd_117846 3984305594064273954439 := by
  unfold tailWord_117846
  simp only [CollatzResearch.WordTrace]
  refine ⟨268637295691971458722337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2865464487381028893038261 268637295691971458722337)
  ·
    refine ⟨201477971768978594041753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268637295691971458722337 201477971768978594041753)
    ·
      refine ⟨151108478826733945531315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201477971768978594041753 151108478826733945531315)
      ·
        refine ⟨226662718240100918296973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151108478826733945531315 226662718240100918296973)
        ·
          refine ⟨84998519340037844361365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226662718240100918296973 84998519340037844361365)
          ·
            refine ⟨3984305594064273954439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84998519340037844361365 3984305594064273954439)
            ·
              rfl

theorem cell19_117846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 6].length) (baseStart_117846 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117846 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117846 prefixEnd_117846 := by exact prefixLift 117846
  have htrace : WordTrace (prefixWord ++ tailWord_117846) baseStart_117846 baseEnd_117846 := by
    simpa [prefixWord, tailWord_117846, baseEnd_117846] using wordTrace_append hprefix tailTrace_117846
  have hstable : (prefixWord ++ tailWord_117846).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117846).length < 2 ^ (prefixWord ++ tailWord_117846).sum := by decide
  have hdescent : baseEnd_117846 < baseStart_117846 := by decide
  rcases family_descends (prefixWord ++ tailWord_117846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117869 : List Nat := [1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_117869 : Nat := 118140960795 + 117869 * 2 ^ 59
def prefixEnd_117869 : Nat := 4983230072969 + 3 ^ 40 * 117869 * 2
def baseEnd_117869 : Nat := 35865748897721227078777

theorem tailTrace_117869 : CollatzResearch.WordTrace tailWord_117869 prefixEnd_117869 35865748897721227078777 := by
  unfold tailWord_117869
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299035609988218267644661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2866023739992145511763107 4299035609988218267644661)
  ·
    refine ⟨403034588436395462591687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4299035609988218267644661 403034588436395462591687)
    ·
      refine ⟨604551882654593193887531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 403034588436395462591687 604551882654593193887531)
      ·
        refine ⟨906827823981889790831297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604551882654593193887531 906827823981889790831297)
        ·
          refine ⟨680120867986417343123473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906827823981889790831297 680120867986417343123473)
          ·
            refine ⟨510090650989813007342605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680120867986417343123473 510090650989813007342605)
            ·
              refine ⟨191283994121179877753477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510090650989813007342605 191283994121179877753477)
              ·
                refine ⟨35865748897721227078777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191283994121179877753477 35865748897721227078777)
                ·
                  rfl

theorem cell19_117869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_117869 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117869 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117869 prefixEnd_117869 := by exact prefixLift 117869
  have htrace : WordTrace (prefixWord ++ tailWord_117869) baseStart_117869 baseEnd_117869 := by
    simpa [prefixWord, tailWord_117869, baseEnd_117869] using wordTrace_append hprefix tailTrace_117869
  have hstable : (prefixWord ++ tailWord_117869).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117869).length < 2 ^ (prefixWord ++ tailWord_117869).sum := by decide
  have hdescent : baseEnd_117869 < baseStart_117869 := by decide
  rcases family_descends (prefixWord ++ tailWord_117869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117945 : List Nat := [1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_117945 : Nat := 118140960795 + 117945 * 2 ^ 59
def prefixEnd_117945 : Nat := 4983230072969 + 3 ^ 40 * 117945 * 2
def baseEnd_117945 : Nat := 35888874544975569389681

theorem tailTrace_117945 : CollatzResearch.WordTrace tailWord_117945 prefixEnd_117945 35888874544975569389681 := by
  unfold tailWord_117945
  simp only [CollatzResearch.WordTrace]
  refine ⟨4301807557712883247411289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2867871705141922164940859 4301807557712883247411289)
  ·
    refine ⟨3226355668284662435558467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4301807557712883247411289 3226355668284662435558467)
    ·
      refine ⟨4839533502426993653337701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3226355668284662435558467 4839533502426993653337701)
      ·
        refine ⟨907412531705061310000819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4839533502426993653337701 907412531705061310000819)
        ·
          refine ⟨1361118797557591965001229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 907412531705061310000819 1361118797557591965001229)
          ·
            refine ⟨510419549084096986875461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1361118797557591965001229 510419549084096986875461)
            ·
              refine ⟨95703665453268185039149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510419549084096986875461 95703665453268185039149)
              ·
                refine ⟨35888874544975569389681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95703665453268185039149 35888874544975569389681)
                ·
                  rfl

theorem cell19_117945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_117945 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117945 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117945 prefixEnd_117945 := by exact prefixLift 117945
  have htrace : WordTrace (prefixWord ++ tailWord_117945) baseStart_117945 baseEnd_117945 := by
    simpa [prefixWord, tailWord_117945, baseEnd_117945] using wordTrace_append hprefix tailTrace_117945
  have hstable : (prefixWord ++ tailWord_117945).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117945).length < 2 ^ (prefixWord ++ tailWord_117945).sum := by decide
  have hdescent : baseEnd_117945 < baseStart_117945 := by decide
  rcases family_descends (prefixWord ++ tailWord_117945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117958 : List Nat := [6, 1, 2, 2, 1, 2, 5]
def baseStart_117958 : Nat := 118140960795 + 117958 * 2 ^ 59
def prefixEnd_117958 : Nat := 4983230072969 + 3 ^ 40 * 117958 * 2
def baseEnd_117958 : Nat := 11964276749265130366919

theorem tailTrace_117958 : CollatzResearch.WordTrace tailWord_117958 prefixEnd_117958 11964276749265130366919 := by
  unfold tailWord_117958
  simp only [CollatzResearch.WordTrace]
  refine ⟨134446303333305827113579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2868187804443857645089685 134446303333305827113579)
  ·
    refine ⟨201669454999958740670369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134446303333305827113579 201669454999958740670369)
    ·
      refine ⟨151252091249969055502777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201669454999958740670369 151252091249969055502777)
      ·
        refine ⟨113439068437476791627083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151252091249969055502777 113439068437476791627083)
        ·
          refine ⟨170158602656215187440625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113439068437476791627083 170158602656215187440625)
          ·
            refine ⟨127618951992161390580469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170158602656215187440625 127618951992161390580469)
            ·
              refine ⟨11964276749265130366919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127618951992161390580469 11964276749265130366919)
              ·
                rfl

theorem cell19_117958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 5].length) (baseStart_117958 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117958 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117958 prefixEnd_117958 := by exact prefixLift 117958
  have htrace : WordTrace (prefixWord ++ tailWord_117958) baseStart_117958 baseEnd_117958 := by
    simpa [prefixWord, tailWord_117958, baseEnd_117958] using wordTrace_append hprefix tailTrace_117958
  have hstable : (prefixWord ++ tailWord_117958).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117958).length < 2 ^ (prefixWord ++ tailWord_117958).sum := by decide
  have hdescent : baseEnd_117958 < baseStart_117958 := by decide
  rcases family_descends (prefixWord ++ tailWord_117958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117981 : List Nat := [1, 4, 3, 2, 2, 1, 2, 4]
def baseStart_117981 : Nat := 118140960795 + 117981 * 2 ^ 59
def prefixEnd_117981 : Nat := 4983230072969 + 3 ^ 40 * 117981 * 2
def baseEnd_117981 : Nat := 35899828798938152589583

theorem tailTrace_117981 : CollatzResearch.WordTrace tailWord_117981 prefixEnd_117981 35899828798938152589583 := by
  unfold tailWord_117981
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303120585582461395721797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2868747057054974263814531 4303120585582461395721797)
  ·
    refine ⟨806835109796711511697837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4303120585582461395721797 806835109796711511697837)
    ·
      refine ⟨302563166173766816886689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 806835109796711511697837 302563166173766816886689)
      ·
        refine ⟨226922374630325112665017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302563166173766816886689 226922374630325112665017)
        ·
          refine ⟨170191780972743834498763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226922374630325112665017 170191780972743834498763)
          ·
            refine ⟨255287671459115751748145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170191780972743834498763 255287671459115751748145)
            ·
              refine ⟨191465753594336813811109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255287671459115751748145 191465753594336813811109)
              ·
                refine ⟨35899828798938152589583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191465753594336813811109 35899828798938152589583)
                ·
                  rfl

theorem cell19_117981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_117981 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117981 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117981 prefixEnd_117981 := by exact prefixLift 117981
  have htrace : WordTrace (prefixWord ++ tailWord_117981) baseStart_117981 baseEnd_117981 := by
    simpa [prefixWord, tailWord_117981, baseEnd_117981] using wordTrace_append hprefix tailTrace_117981
  have hstable : (prefixWord ++ tailWord_117981).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117981).length < 2 ^ (prefixWord ++ tailWord_117981).sum := by decide
  have hdescent : baseEnd_117981 < baseStart_117981 := by decide
  rcases family_descends (prefixWord ++ tailWord_117981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_117985 : List Nat := [1, 2, 3, 1, 3, 2, 1, 6]
def baseStart_117985 : Nat := 118140960795 + 117985 * 2 ^ 59
def prefixEnd_117985 : Nat := 4983230072969 + 3 ^ 40 * 117985 * 2
def baseEnd_117985 : Nat := 35901045938267328500683

theorem tailTrace_117985 : CollatzResearch.WordTrace tailWord_117985 prefixEnd_117985 35901045938267328500683 := by
  unfold tailWord_117985
  simp only [CollatzResearch.WordTrace]
  refine ⟨4303266477567970078867409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2868844318378646719244939 4303266477567970078867409)
  ·
    refine ⟨3227449858175977559150557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4303266477567970078867409 3227449858175977559150557)
    ·
      refine ⟨1210293696815991584681459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3227449858175977559150557 1210293696815991584681459)
      ·
        refine ⟨1815440545223987377022189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1210293696815991584681459 1815440545223987377022189)
        ·
          refine ⟨680790204458995266383321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1815440545223987377022189 680790204458995266383321)
          ·
            refine ⟨510592653344246449787491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 680790204458995266383321 510592653344246449787491)
            ·
              refine ⟨765888980016369674681237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 510592653344246449787491 765888980016369674681237)
              ·
                refine ⟨35901045938267328500683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 765888980016369674681237 35901045938267328500683)
                ·
                  rfl

theorem cell19_117985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_117985 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_117985 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_117985 prefixEnd_117985 := by exact prefixLift 117985
  have htrace : WordTrace (prefixWord ++ tailWord_117985) baseStart_117985 baseEnd_117985 := by
    simpa [prefixWord, tailWord_117985, baseEnd_117985] using wordTrace_append hprefix tailTrace_117985
  have hstable : (prefixWord ++ tailWord_117985).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_117985).length < 2 ^ (prefixWord ++ tailWord_117985).sum := by decide
  have hdescent : baseEnd_117985 < baseStart_117985 := by decide
  rcases family_descends (prefixWord ++ tailWord_117985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118034 : List Nat := [3, 2, 4, 2, 2, 1, 1, 4]
def baseStart_118034 : Nat := 118140960795 + 118034 * 2 ^ 59
def prefixEnd_118034 : Nat := 4983230072969 + 3 ^ 40 * 118034 * 2
def baseEnd_118034 : Nat := 35915955895049733411661

theorem tailTrace_118034 : CollatzResearch.WordTrace tailWord_118034 prefixEnd_118034 35915955895049733411661 := by
  unfold tailWord_118034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1076263413597612861850289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2870035769593634298267437 1076263413597612861850289)
  ·
    refine ⟨807197560198209646387717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1076263413597612861850289 807197560198209646387717)
    ·
      refine ⟨151349542537164308697697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 807197560198209646387717 151349542537164308697697)
      ·
        refine ⟨113512156902873231523273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151349542537164308697697 113512156902873231523273)
        ·
          refine ⟨85134117677154923642455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113512156902873231523273 85134117677154923642455)
          ·
            refine ⟨127701176515732385463683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85134117677154923642455 127701176515732385463683)
            ·
              refine ⟨191551764773598578195525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127701176515732385463683 191551764773598578195525)
              ·
                refine ⟨35915955895049733411661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191551764773598578195525 35915955895049733411661)
                ·
                  rfl

theorem cell19_118034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_118034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118034 prefixEnd_118034 := by exact prefixLift 118034
  have htrace : WordTrace (prefixWord ++ tailWord_118034) baseStart_118034 baseEnd_118034 := by
    simpa [prefixWord, tailWord_118034, baseEnd_118034] using wordTrace_append hprefix tailTrace_118034
  have hstable : (prefixWord ++ tailWord_118034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118034).length < 2 ^ (prefixWord ++ tailWord_118034).sum := by decide
  have hdescent : baseEnd_118034 < baseStart_118034 := by decide
  rcases family_descends (prefixWord ++ tailWord_118034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118040 : List Nat := [2, 1, 2, 3, 1, 5, 1, 4]
def baseStart_118040 : Nat := 118140960795 + 118040 * 2 ^ 59
def prefixEnd_118040 : Nat := 4983230072969 + 3 ^ 40 * 118040 * 2
def baseEnd_118040 : Nat := 35917781604043497278311

theorem tailTrace_118040 : CollatzResearch.WordTrace tailWord_118040 prefixEnd_118040 35917781604043497278311 := by
  unfold tailWord_118040
  simp only [CollatzResearch.WordTrace]
  refine ⟨2152636246184357236059787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2870181661579142981413049 2152636246184357236059787)
  ·
    refine ⟨3228954369276535854089681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2152636246184357236059787 3228954369276535854089681)
    ·
      refine ⟨2421715776957401890567261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3228954369276535854089681 2421715776957401890567261)
      ·
        refine ⟨908143416359025708962723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2421715776957401890567261 908143416359025708962723)
        ·
          refine ⟨1362215124538538563444085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 908143416359025708962723 1362215124538538563444085)
          ·
            refine ⟨127707667925487990322883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1362215124538538563444085 127707667925487990322883)
            ·
              refine ⟨191561501888231985484325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127707667925487990322883 191561501888231985484325)
              ·
                refine ⟨35917781604043497278311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191561501888231985484325 35917781604043497278311)
                ·
                  rfl

theorem cell19_118040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_118040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118040 prefixEnd_118040 := by exact prefixLift 118040
  have htrace : WordTrace (prefixWord ++ tailWord_118040) baseStart_118040 baseEnd_118040 := by
    simpa [prefixWord, tailWord_118040, baseEnd_118040] using wordTrace_append hprefix tailTrace_118040
  have hstable : (prefixWord ++ tailWord_118040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118040).length < 2 ^ (prefixWord ++ tailWord_118040).sum := by decide
  have hdescent : baseEnd_118040 < baseStart_118040 := by decide
  rcases family_descends (prefixWord ++ tailWord_118040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118116 : List Nat := [2, 3, 1, 1, 3, 2, 4, 3]
def baseStart_118116 : Nat := 118140960795 + 118116 * 2 ^ 59
def prefixEnd_118116 : Nat := 4983230072969 + 3 ^ 40 * 118116 * 2
def baseEnd_118116 : Nat := 35940907251297839589215

theorem tailTrace_118116 : CollatzResearch.WordTrace tailWord_118116 prefixEnd_118116 35940907251297839589215 := by
  unfold tailWord_118116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154022220046689725943101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2872029626728919634590801 2154022220046689725943101)
  ·
    refine ⟨807758332517508647228663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2154022220046689725943101 807758332517508647228663)
    ·
      refine ⟨1211637498776262970842995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 807758332517508647228663 1211637498776262970842995)
      ·
        refine ⟨1817456248164394456264493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1211637498776262970842995 1817456248164394456264493)
        ·
          refine ⟨681546093061647921099185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1817456248164394456264493 681546093061647921099185)
          ·
            refine ⟨511159569796235940824389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681546093061647921099185 511159569796235940824389)
            ·
              refine ⟨95842419336794238904573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 511159569796235940824389 95842419336794238904573)
              ·
                refine ⟨35940907251297839589215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95842419336794238904573 35940907251297839589215)
                ·
                  rfl

theorem cell19_118116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 4, 3].length) (baseStart_118116 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118116 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118116 prefixEnd_118116 := by exact prefixLift 118116
  have htrace : WordTrace (prefixWord ++ tailWord_118116) baseStart_118116 baseEnd_118116 := by
    simpa [prefixWord, tailWord_118116, baseEnd_118116] using wordTrace_append hprefix tailTrace_118116
  have hstable : (prefixWord ++ tailWord_118116).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118116).length < 2 ^ (prefixWord ++ tailWord_118116).sum := by decide
  have hdescent : baseEnd_118116 < baseStart_118116 := by decide
  rcases family_descends (prefixWord ++ tailWord_118116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118133 : List Nat := [1, 3, 4, 1, 4, 1, 5]
def baseStart_118133 : Nat := 118140960795 + 118133 * 2 ^ 59
def prefixEnd_118133 : Nat := 4983230072969 + 3 ^ 40 * 118133 * 2
def baseEnd_118133 : Nat := 11982026697815612403797

theorem tailTrace_118133 : CollatzResearch.WordTrace tailWord_118133 prefixEnd_118133 11982026697815612403797 := by
  unfold tailWord_118133
  simp only [CollatzResearch.WordTrace]
  refine ⟨4308664481031791355255053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2872442987354527570170035 4308664481031791355255053)
  ·
    refine ⟨1615749180386921758220645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4308664481031791355255053 1615749180386921758220645)
    ·
      refine ⟨302952971322547829666371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1615749180386921758220645 302952971322547829666371)
      ·
        refine ⟨454429456983821744499557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302952971322547829666371 454429456983821744499557)
        ·
          refine ⟨85205523184466577093667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 454429456983821744499557 85205523184466577093667)
          ·
            refine ⟨127808284776699865640501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85205523184466577093667 127808284776699865640501)
            ·
              refine ⟨11982026697815612403797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127808284776699865640501 11982026697815612403797)
              ·
                rfl

theorem cell19_118133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 5].length) (baseStart_118133 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118133 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118133 prefixEnd_118133 := by exact prefixLift 118133
  have htrace : WordTrace (prefixWord ++ tailWord_118133) baseStart_118133 baseEnd_118133 := by
    simpa [prefixWord, tailWord_118133, baseEnd_118133] using wordTrace_append hprefix tailTrace_118133
  have hstable : (prefixWord ++ tailWord_118133).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118133).length < 2 ^ (prefixWord ++ tailWord_118133).sum := by decide
  have hdescent : baseEnd_118133 < baseStart_118133 := by decide
  rcases family_descends (prefixWord ++ tailWord_118133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118156 : List Nat := [2, 2, 1, 2, 1, 3, 4, 4]
def baseStart_118156 : Nat := 118140960795 + 118156 * 2 ^ 59
def prefixEnd_118156 : Nat := 4983230072969 + 3 ^ 40 * 118156 * 2
def baseEnd_118156 : Nat := 35953078644589598700217

theorem tailTrace_118156 : CollatzResearch.WordTrace tailWord_118156 prefixEnd_118156 35953078644589598700217 := by
  unfold tailWord_118156
  simp only [CollatzResearch.WordTrace]
  refine ⟨2154751679974233141671161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2873002239965644188894881 2154751679974233141671161)
  ·
    refine ⟨1616063759980674856253371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2154751679974233141671161 1616063759980674856253371)
    ·
      refine ⟨2424095639971012284380057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1616063759980674856253371 2424095639971012284380057)
      ·
        refine ⟨1818071729978259213285043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2424095639971012284380057 1818071729978259213285043)
        ·
          refine ⟨2727107594967388819927565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1818071729978259213285043 2727107594967388819927565)
          ·
            refine ⟨1022665348112770807472837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2727107594967388819927565 1022665348112770807472837)
            ·
              refine ⟨191749752771144526401157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1022665348112770807472837 191749752771144526401157)
              ·
                refine ⟨35953078644589598700217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191749752771144526401157 35953078644589598700217)
                ·
                  rfl

theorem cell19_118156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_118156 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118156 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118156 prefixEnd_118156 := by exact prefixLift 118156
  have htrace : WordTrace (prefixWord ++ tailWord_118156) baseStart_118156 baseEnd_118156 := by
    simpa [prefixWord, tailWord_118156, baseEnd_118156] using wordTrace_append hprefix tailTrace_118156
  have hstable : (prefixWord ++ tailWord_118156).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118156).length < 2 ^ (prefixWord ++ tailWord_118156).sum := by decide
  have hdescent : baseEnd_118156 < baseStart_118156 := by decide
  rcases family_descends (prefixWord ++ tailWord_118156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118175 : List Nat := [1, 1, 2, 5, 1, 2, 2, 5]
def baseStart_118175 : Nat := 118140960795 + 118175 * 2 ^ 59
def prefixEnd_118175 : Nat := 4983230072969 + 3 ^ 40 * 118175 * 2
def baseEnd_118175 : Nat := 35958860056403184277943

theorem tailTrace_118175 : CollatzResearch.WordTrace tailWord_118175 prefixEnd_118175 35958860056403184277943 := by
  unfold tailWord_118175
  simp only [CollatzResearch.WordTrace]
  refine ⟨4310196346879632528283979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2873464231253088352189319 4310196346879632528283979)
  ·
    refine ⟨6465294520319448792425969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4310196346879632528283979 6465294520319448792425969)
    ·
      refine ⟨4848970890239586594319477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6465294520319448792425969 4848970890239586594319477)
      ·
        refine ⟨454591020959961243217451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4848970890239586594319477 454591020959961243217451)
        ·
          refine ⟨681886531439941864826177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 454591020959961243217451 681886531439941864826177)
          ·
            refine ⟨511414898579956398619633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 681886531439941864826177 511414898579956398619633)
            ·
              refine ⟨383561173934967298964725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 511414898579956398619633 383561173934967298964725)
              ·
                refine ⟨35958860056403184277943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 383561173934967298964725 35958860056403184277943)
                ·
                  rfl

theorem cell19_118175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_118175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118175 prefixEnd_118175 := by exact prefixLift 118175
  have htrace : WordTrace (prefixWord ++ tailWord_118175) baseStart_118175 baseEnd_118175 := by
    simpa [prefixWord, tailWord_118175, baseEnd_118175] using wordTrace_append hprefix tailTrace_118175
  have hstable : (prefixWord ++ tailWord_118175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118175).length < 2 ^ (prefixWord ++ tailWord_118175).sum := by decide
  have hdescent : baseEnd_118175 < baseStart_118175 := by decide
  rcases family_descends (prefixWord ++ tailWord_118175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118228 : List Nat := [2, 4, 1, 2, 3, 1, 3, 3]
def baseStart_118228 : Nat := 118140960795 + 118228 * 2 ^ 59
def prefixEnd_118228 : Nat := 4983230072969 + 3 ^ 40 * 118228 * 2
def baseEnd_118228 : Nat := 35974987152514765100021

theorem tailTrace_118228 : CollatzResearch.WordTrace tailWord_118228 prefixEnd_118228 35974987152514765100021 := by
  unfold tailWord_118228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2156064707843811289981669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2874752943791748386642225 2156064707843811289981669)
  ·
    refine ⟨404262132720714616871563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2156064707843811289981669 404262132720714616871563)
    ·
      refine ⟨606393199081071925307345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 404262132720714616871563 606393199081071925307345)
      ·
        refine ⟨454794899310803943980509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 606393199081071925307345 454794899310803943980509)
        ·
          refine ⟨170548087241551478992691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454794899310803943980509 170548087241551478992691)
          ·
            refine ⟨255822130862327218489037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170548087241551478992691 255822130862327218489037)
            ·
              refine ⟨95933299073372706933389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255822130862327218489037 95933299073372706933389)
              ·
                refine ⟨35974987152514765100021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95933299073372706933389 35974987152514765100021)
                ·
                  rfl

theorem cell19_118228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 3].length) (baseStart_118228 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118228 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118228 prefixEnd_118228 := by exact prefixLift 118228
  have htrace : WordTrace (prefixWord ++ tailWord_118228) baseStart_118228 baseEnd_118228 := by
    simpa [prefixWord, tailWord_118228, baseEnd_118228] using wordTrace_append hprefix tailTrace_118228
  have hstable : (prefixWord ++ tailWord_118228).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118228).length < 2 ^ (prefixWord ++ tailWord_118228).sum := by decide
  have hdescent : baseEnd_118228 < baseStart_118228 := by decide
  rcases family_descends (prefixWord ++ tailWord_118228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118327 : List Nat := [1, 1, 3, 1, 2, 5, 2, 4]
def baseStart_118327 : Nat := 118140960795 + 118327 * 2 ^ 59
def prefixEnd_118327 : Nat := 4983230072969 + 3 ^ 40 * 118327 * 2
def baseEnd_118327 : Nat := 36005111350911868899751

theorem tailTrace_118327 : CollatzResearch.WordTrace tailWord_118327 prefixEnd_118327 36005111350911868899751 := by
  unfold tailWord_118327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4315740242328962487817235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2877160161552641658544823 4315740242328962487817235)
  ·
    refine ⟨6473610363493443731725853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4315740242328962487817235 6473610363493443731725853)
    ·
      refine ⟨2427603886310041399397195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6473610363493443731725853 2427603886310041399397195)
      ·
        refine ⟨3641405829465062099095793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2427603886310041399397195 3641405829465062099095793)
        ·
          refine ⟨2731054372098796574321845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3641405829465062099095793 2731054372098796574321845)
          ·
            refine ⟨256036347384262178842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2731054372098796574321845 256036347384262178842673)
            ·
              refine ⟨192027260538196634132005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 256036347384262178842673 192027260538196634132005)
              ·
                refine ⟨36005111350911868899751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192027260538196634132005 36005111350911868899751)
                ·
                  rfl

theorem cell19_118327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_118327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118327 prefixEnd_118327 := by exact prefixLift 118327
  have htrace : WordTrace (prefixWord ++ tailWord_118327) baseStart_118327 baseEnd_118327 := by
    simpa [prefixWord, tailWord_118327, baseEnd_118327] using wordTrace_append hprefix tailTrace_118327
  have hstable : (prefixWord ++ tailWord_118327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118327).length < 2 ^ (prefixWord ++ tailWord_118327).sum := by decide
  have hdescent : baseEnd_118327 < baseStart_118327 := by decide
  rcases family_descends (prefixWord ++ tailWord_118327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118384 : List Nat := [2, 1, 1, 1, 6, 1, 3, 4]
def baseStart_118384 : Nat := 118140960795 + 118384 * 2 ^ 59
def prefixEnd_118384 : Nat := 4983230072969 + 3 ^ 40 * 118384 * 2
def baseEnd_118384 : Nat := 36022455586352625632929

theorem tailTrace_118384 : CollatzResearch.WordTrace tailWord_118384 prefixEnd_118384 36022455586352625632929 := by
  unfold tailWord_118384
  simp only [CollatzResearch.WordTrace]
  refine ⟨2158909601561230611321103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2878546135414974148428137 2158909601561230611321103)
  ·
    refine ⟨3238364402341845916981655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2158909601561230611321103 3238364402341845916981655)
    ·
      refine ⟨4857546603512768875472483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3238364402341845916981655 4857546603512768875472483)
      ·
        refine ⟨7286319905269153313208725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4857546603512768875472483 7286319905269153313208725)
        ·
          refine ⟨341546245559491561556659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7286319905269153313208725 341546245559491561556659)
          ·
            refine ⟨512319368339237342334989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341546245559491561556659 512319368339237342334989)
            ·
              refine ⟨192119763127214003375621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 512319368339237342334989 192119763127214003375621)
              ·
                refine ⟨36022455586352625632929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192119763127214003375621 36022455586352625632929)
                ·
                  rfl

theorem cell19_118384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_118384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118384 prefixEnd_118384 := by exact prefixLift 118384
  have htrace : WordTrace (prefixWord ++ tailWord_118384) baseStart_118384 baseEnd_118384 := by
    simpa [prefixWord, tailWord_118384, baseEnd_118384] using wordTrace_append hprefix tailTrace_118384
  have hstable : (prefixWord ++ tailWord_118384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118384).length < 2 ^ (prefixWord ++ tailWord_118384).sum := by decide
  have hdescent : baseEnd_118384 < baseStart_118384 := by decide
  rcases family_descends (prefixWord ++ tailWord_118384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118401 : List Nat := [1, 2, 4, 2, 1, 3, 3, 3]
def baseStart_118401 : Nat := 118140960795 + 118401 * 2 ^ 59
def prefixEnd_118401 : Nat := 4983230072969 + 3 ^ 40 * 118401 * 2
def baseEnd_118401 : Nat := 36027628428501623255105

theorem tailTrace_118401 : CollatzResearch.WordTrace tailWord_118401 prefixEnd_118401 36027628428501623255105 := by
  unfold tailWord_118401
  simp only [CollatzResearch.WordTrace]
  refine ⟨4318439244060873126011057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2878959496040582084007371 4318439244060873126011057)
  ·
    refine ⟨3238829433045654844508293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4318439244060873126011057 3238829433045654844508293)
    ·
      refine ⟨607280518696060283345305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3238829433045654844508293 607280518696060283345305)
      ·
        refine ⟨455460389022045212508979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 607280518696060283345305 455460389022045212508979)
        ·
          refine ⟨683190583533067818763469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455460389022045212508979 683190583533067818763469)
          ·
            refine ⟨256196468824900432036301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683190583533067818763469 256196468824900432036301)
            ·
              refine ⟨96073675809337662013613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 256196468824900432036301 96073675809337662013613)
              ·
                refine ⟨36027628428501623255105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96073675809337662013613 36027628428501623255105)
                ·
                  rfl

theorem cell19_118401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 3].length) (baseStart_118401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118401 prefixEnd_118401 := by exact prefixLift 118401
  have htrace : WordTrace (prefixWord ++ tailWord_118401) baseStart_118401 baseEnd_118401 := by
    simpa [prefixWord, tailWord_118401, baseEnd_118401] using wordTrace_append hprefix tailTrace_118401
  have hstable : (prefixWord ++ tailWord_118401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118401).length < 2 ^ (prefixWord ++ tailWord_118401).sum := by decide
  have hdescent : baseEnd_118401 < baseStart_118401 := by decide
  rcases family_descends (prefixWord ++ tailWord_118401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118420 : List Nat := [2, 4, 2, 2, 2, 1, 6]
def baseStart_118420 : Nat := 118140960795 + 118420 * 2 ^ 59
def prefixEnd_118420 : Nat := 4983230072969 + 3 ^ 40 * 118420 * 2
def baseEnd_118420 : Nat := 12011136613438402944277

theorem tailTrace_118420 : CollatzResearch.WordTrace tailWord_118420 prefixEnd_118420 12011136613438402944277 := by
  unfold tailWord_118420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2159566115496019685476357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2879421487328026247301809 2159566115496019685476357)
  ·
    refine ⟨404918646655503691026817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2159566115496019685476357 404918646655503691026817)
    ·
      refine ⟨303688984991627768270113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 404918646655503691026817 303688984991627768270113)
      ·
        refine ⟨227766738743720826202585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 303688984991627768270113 227766738743720826202585)
        ·
          refine ⟨170825054057790619651939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227766738743720826202585 170825054057790619651939)
          ·
            refine ⟨256237581086685929477909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170825054057790619651939 256237581086685929477909)
            ·
              refine ⟨12011136613438402944277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256237581086685929477909 12011136613438402944277)
              ·
                rfl

theorem cell19_118420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 6].length) (baseStart_118420 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118420 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118420 prefixEnd_118420 := by exact prefixLift 118420
  have htrace : WordTrace (prefixWord ++ tailWord_118420) baseStart_118420 baseEnd_118420 := by
    simpa [prefixWord, tailWord_118420, baseEnd_118420] using wordTrace_append hprefix tailTrace_118420
  have hstable : (prefixWord ++ tailWord_118420).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118420).length < 2 ^ (prefixWord ++ tailWord_118420).sum := by decide
  have hdescent : baseEnd_118420 < baseStart_118420 := by decide
  rcases family_descends (prefixWord ++ tailWord_118420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118454 : List Nat := [5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_118454 : Nat := 118140960795 + 118454 * 2 ^ 59
def prefixEnd_118454 : Nat := 4983230072969 + 3 ^ 40 * 118454 * 2
def baseEnd_118454 : Nat := 36043755524613204077183

theorem tailTrace_118454 : CollatzResearch.WordTrace tailWord_118454 prefixEnd_118454 36043755524613204077183 := by
  unfold tailWord_118454
  simp only [CollatzResearch.WordTrace]
  refine ⟨270023269554303948605651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2880248208579242118460277 270023269554303948605651)
  ·
    refine ⟨405034904331455922908477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270023269554303948605651 405034904331455922908477)
    ·
      refine ⟨151888089124295971090679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 405034904331455922908477 151888089124295971090679)
      ·
        refine ⟨227832133686443956636019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151888089124295971090679 227832133686443956636019)
        ·
          refine ⟨341748200529665934954029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227832133686443956636019 341748200529665934954029)
          ·
            refine ⟨128155575198624725607761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 341748200529665934954029 128155575198624725607761)
            ·
              refine ⟨96116681398968544205821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128155575198624725607761 96116681398968544205821)
              ·
                refine ⟨36043755524613204077183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96116681398968544205821 36043755524613204077183)
                ·
                  rfl

theorem cell19_118454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_118454 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118454 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118454 prefixEnd_118454 := by exact prefixLift 118454
  have htrace : WordTrace (prefixWord ++ tailWord_118454) baseStart_118454 baseEnd_118454 := by
    simpa [prefixWord, tailWord_118454, baseEnd_118454] using wordTrace_append hprefix tailTrace_118454
  have hstable : (prefixWord ++ tailWord_118454).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118454).length < 2 ^ (prefixWord ++ tailWord_118454).sum := by decide
  have hdescent : baseEnd_118454 < baseStart_118454 := by decide
  rcases family_descends (prefixWord ++ tailWord_118454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118458 : List Nat := [3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_118458 : Nat := 118140960795 + 118458 * 2 ^ 59
def prefixEnd_118458 : Nat := 4983230072969 + 3 ^ 40 * 118458 * 2
def baseEnd_118458 : Nat := 36044972663942379988283

theorem tailTrace_118458 : CollatzResearch.WordTrace tailWord_118458 prefixEnd_118458 36044972663942379988283 := by
  unfold tailWord_118458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080129551213592965209007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2880345469902914573890685 1080129551213592965209007)
  ·
    refine ⟨1620194326820389447813511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080129551213592965209007 1620194326820389447813511)
    ·
      refine ⟨2430291490230584171720267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1620194326820389447813511 2430291490230584171720267)
      ·
        refine ⟨3645437235345876257580401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430291490230584171720267 3645437235345876257580401)
        ·
          refine ⟨2734077926509407193185301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3645437235345876257580401 2734077926509407193185301)
          ·
            refine ⟨128159902805128462180561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2734077926509407193185301 128159902805128462180561)
            ·
              refine ⟨96119927103846346635421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128159902805128462180561 96119927103846346635421)
              ·
                refine ⟨36044972663942379988283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96119927103846346635421 36044972663942379988283)
                ·
                  rfl

theorem cell19_118458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_118458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118458 prefixEnd_118458 := by exact prefixLift 118458
  have htrace : WordTrace (prefixWord ++ tailWord_118458) baseStart_118458 baseEnd_118458 := by
    simpa [prefixWord, tailWord_118458, baseEnd_118458] using wordTrace_append hprefix tailTrace_118458
  have hstable : (prefixWord ++ tailWord_118458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118458).length < 2 ^ (prefixWord ++ tailWord_118458).sum := by decide
  have hdescent : baseEnd_118458 < baseStart_118458 := by decide
  rcases family_descends (prefixWord ++ tailWord_118458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118460 : List Nat := [2, 2, 2, 3, 1, 3, 1, 5]
def baseStart_118460 : Nat := 118140960795 + 118460 * 2 ^ 59
def prefixEnd_118460 : Nat := 4983230072969 + 3 ^ 40 * 118460 * 2
def baseEnd_118460 : Nat := 36045581233606967943833

theorem tailTrace_118460 : CollatzResearch.WordTrace tailWord_118460 prefixEnd_118460 36045581233606967943833 := by
  unfold tailWord_118460
  simp only [CollatzResearch.WordTrace]
  refine ⟨2160295575423563101204417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2880394100564750801605889 2160295575423563101204417)
  ·
    refine ⟨1620221681567672325903313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2160295575423563101204417 1620221681567672325903313)
    ·
      refine ⟨1215166261175754244427485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1620221681567672325903313 1215166261175754244427485)
      ·
        refine ⟨455687347940907841660307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1215166261175754244427485 455687347940907841660307)
        ·
          refine ⟨683531021911361762490461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 455687347940907841660307 683531021911361762490461)
          ·
            refine ⟨256324133216760660933923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 683531021911361762490461 256324133216760660933923)
            ·
              refine ⟨384486199825140991400885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256324133216760660933923 384486199825140991400885)
              ·
                refine ⟨36045581233606967943833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384486199825140991400885 36045581233606967943833)
                ·
                  rfl

theorem cell19_118460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_118460 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118460 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118460 prefixEnd_118460 := by exact prefixLift 118460
  have htrace : WordTrace (prefixWord ++ tailWord_118460) baseStart_118460 baseEnd_118460 := by
    simpa [prefixWord, tailWord_118460, baseEnd_118460] using wordTrace_append hprefix tailTrace_118460
  have hstable : (prefixWord ++ tailWord_118460).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118460).length < 2 ^ (prefixWord ++ tailWord_118460).sum := by decide
  have hdescent : baseEnd_118460 < baseStart_118460 := by decide
  rcases family_descends (prefixWord ++ tailWord_118460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118477 : List Nat := [1, 6, 2, 1, 1, 1, 7]
def baseStart_118477 : Nat := 118140960795 + 118477 * 2 ^ 59
def prefixEnd_118477 : Nat := 4983230072969 + 3 ^ 40 * 118477 * 2
def baseEnd_118477 : Nat := 12016918025251988522003

theorem tailTrace_118477 : CollatzResearch.WordTrace tailWord_118477 prefixEnd_118477 12016918025251988522003 := by
  unfold tailWord_118477
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321211191785538105777685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2880807461190358737185123 4321211191785538105777685)
  ·
    refine ⟨202556774614947098708329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4321211191785538105777685 202556774614947098708329)
    ·
      refine ⟨151917580961210324031247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 202556774614947098708329 151917580961210324031247)
      ·
        refine ⟨227876371441815486046871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151917580961210324031247 227876371441815486046871)
        ·
          refine ⟨341814557162723229070307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227876371441815486046871 341814557162723229070307)
          ·
            refine ⟨512721835744084843605461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 341814557162723229070307 512721835744084843605461)
            ·
              refine ⟨12016918025251988522003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 512721835744084843605461 12016918025251988522003)
              ·
                rfl

theorem cell19_118477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_118477 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118477 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118477 prefixEnd_118477 := by exact prefixLift 118477
  have htrace : WordTrace (prefixWord ++ tailWord_118477) baseStart_118477 baseEnd_118477 := by
    simpa [prefixWord, tailWord_118477, baseEnd_118477] using wordTrace_append hprefix tailTrace_118477
  have hstable : (prefixWord ++ tailWord_118477).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118477).length < 2 ^ (prefixWord ++ tailWord_118477).sum := by decide
  have hdescent : baseEnd_118477 < baseStart_118477 := by decide
  rcases family_descends (prefixWord ++ tailWord_118477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118481 : List Nat := [1, 2, 2, 1, 2, 4, 7]
def baseStart_118481 : Nat := 118140960795 + 118481 * 2 ^ 59
def prefixEnd_118481 : Nat := 4983230072969 + 3 ^ 40 * 118481 * 2
def baseEnd_118481 : Nat := 12017323738361713825703

theorem tailTrace_118481 : CollatzResearch.WordTrace tailWord_118481 prefixEnd_118481 12017323738361713825703 := by
  unfold tailWord_118481
  simp only [CollatzResearch.WordTrace]
  refine ⟨4321357083771046788923297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2880904722514031192615531 4321357083771046788923297)
  ·
    refine ⟨3241017812828285091692473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4321357083771046788923297 3241017812828285091692473)
    ·
      refine ⟨2430763359621213818769355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3241017812828285091692473 2430763359621213818769355)
      ·
        refine ⟨3646145039431820728154033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2430763359621213818769355 3646145039431820728154033)
        ·
          refine ⟨2734608779573865546115525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3646145039431820728154033 2734608779573865546115525)
          ·
            refine ⟨512739146170099789896661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2734608779573865546115525 512739146170099789896661)
            ·
              refine ⟨12017323738361713825703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 512739146170099789896661 12017323738361713825703)
              ·
                rfl

theorem cell19_118481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_118481 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118481 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118481 prefixEnd_118481 := by exact prefixLift 118481
  have htrace : WordTrace (prefixWord ++ tailWord_118481) baseStart_118481 baseEnd_118481 := by
    simpa [prefixWord, tailWord_118481, baseEnd_118481] using wordTrace_append hprefix tailTrace_118481
  have hstable : (prefixWord ++ tailWord_118481).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118481).length < 2 ^ (prefixWord ++ tailWord_118481).sum := by decide
  have hdescent : baseEnd_118481 < baseStart_118481 := by decide
  rcases family_descends (prefixWord ++ tailWord_118481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118519 : List Nat := [1, 1, 3, 1, 1, 1, 6, 5]
def baseStart_118519 : Nat := 118140960795 + 118519 * 2 ^ 59
def prefixEnd_118519 : Nat := 4983230072969 + 3 ^ 40 * 118519 * 2
def baseEnd_118519 : Nat := 36063534038712312632561

theorem tailTrace_118519 : CollatzResearch.WordTrace tailWord_118519 prefixEnd_118519 36063534038712312632561 := by
  unfold tailWord_118519
  simp only [CollatzResearch.WordTrace]
  refine ⟨4322743057633379278806611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2881828705088919519204407 4322743057633379278806611)
  ·
    refine ⟨6484114586450068918209917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4322743057633379278806611 6484114586450068918209917)
    ·
      refine ⟨2431542969918775844328719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6484114586450068918209917 2431542969918775844328719)
      ·
        refine ⟨3647314454878163766493079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2431542969918775844328719 3647314454878163766493079)
        ·
          refine ⟨5470971682317245649739619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3647314454878163766493079 5470971682317245649739619)
          ·
            refine ⟨8206457523475868474609429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5470971682317245649739619 8206457523475868474609429)
            ·
              refine ⟨384677696412931334747317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8206457523475868474609429 384677696412931334747317)
              ·
                refine ⟨36063534038712312632561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 384677696412931334747317 36063534038712312632561)
                ·
                  rfl

theorem cell19_118519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_118519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118519 prefixEnd_118519 := by exact prefixLift 118519
  have htrace : WordTrace (prefixWord ++ tailWord_118519) baseStart_118519 baseEnd_118519 := by
    simpa [prefixWord, tailWord_118519, baseEnd_118519] using wordTrace_append hprefix tailTrace_118519
  have hstable : (prefixWord ++ tailWord_118519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118519).length < 2 ^ (prefixWord ++ tailWord_118519).sum := by decide
  have hdescent : baseEnd_118519 < baseStart_118519 := by decide
  rcases family_descends (prefixWord ++ tailWord_118519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118538 : List Nat := [3, 1, 2, 2, 1, 10]
def baseStart_118538 : Nat := 118140960795 + 118538 * 2 ^ 59
def prefixEnd_118538 : Nat := 4983230072969 + 3 ^ 40 * 118538 * 2
def baseEnd_118538 : Nat := 4007701716725099801143

theorem tailTrace_118538 : CollatzResearch.WordTrace tailWord_118538 prefixEnd_118538 4007701716725099801143 := by
  unfold tailWord_118538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1080859011141136380937067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2882290696376363682498845 1080859011141136380937067)
  ·
    refine ⟨1621288516711704571405601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1080859011141136380937067 1621288516711704571405601)
    ·
      refine ⟨1215966387533778428554201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1621288516711704571405601 1215966387533778428554201)
      ·
        refine ⟨911974790650333821415651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1215966387533778428554201 911974790650333821415651)
        ·
          refine ⟨1367962185975500732123477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 911974790650333821415651 1367962185975500732123477)
          ·
            refine ⟨4007701716725099801143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1367962185975500732123477 4007701716725099801143)
            ·
              rfl

theorem cell19_118538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 10].length) (baseStart_118538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118538 prefixEnd_118538 := by exact prefixLift 118538
  have htrace : WordTrace (prefixWord ++ tailWord_118538) baseStart_118538 baseEnd_118538 := by
    simpa [prefixWord, tailWord_118538, baseEnd_118538] using wordTrace_append hprefix tailTrace_118538
  have hstable : (prefixWord ++ tailWord_118538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118538).length < 2 ^ (prefixWord ++ tailWord_118538).sum := by decide
  have hdescent : baseEnd_118538 < baseStart_118538 := by decide
  rcases family_descends (prefixWord ++ tailWord_118538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118595 : List Nat := [1, 1, 1, 3, 1, 6, 6]
def baseStart_118595 : Nat := 118140960795 + 118595 * 2 ^ 59
def prefixEnd_118595 : Nat := 4983230072969 + 3 ^ 40 * 118595 * 2
def baseEnd_118595 : Nat := 12028886561988884981155

theorem tailTrace_118595 : CollatzResearch.WordTrace tailWord_118595 prefixEnd_118595 12028886561988884981155 := by
  unfold tailWord_118595
  simp only [CollatzResearch.WordTrace]
  refine ⟨4325515005358044258573239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2883676670238696172382159 4325515005358044258573239)
  ·
    refine ⟨6488272508037066387859859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4325515005358044258573239 6488272508037066387859859)
    ·
      refine ⟨9732408762055599581789789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6488272508037066387859859 9732408762055599581789789)
      ·
        refine ⟨3649653285770849843171171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9732408762055599581789789 3649653285770849843171171)
        ·
          refine ⟨5474479928656274764756757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3649653285770849843171171 5474479928656274764756757)
          ·
            refine ⟨256616246655762879597973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5474479928656274764756757 256616246655762879597973)
            ·
              refine ⟨12028886561988884981155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 256616246655762879597973 12028886561988884981155)
              ·
                rfl

theorem cell19_118595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 6].length) (baseStart_118595 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118595 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118595 prefixEnd_118595 := by exact prefixLift 118595
  have htrace : WordTrace (prefixWord ++ tailWord_118595) baseStart_118595 baseEnd_118595 := by
    simpa [prefixWord, tailWord_118595, baseEnd_118595] using wordTrace_append hprefix tailTrace_118595
  have hstable : (prefixWord ++ tailWord_118595).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118595).length < 2 ^ (prefixWord ++ tailWord_118595).sum := by decide
  have hdescent : baseEnd_118595 < baseStart_118595 := by decide
  rcases family_descends (prefixWord ++ tailWord_118595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118627 : List Nat := [1, 1, 1, 5, 5, 1, 2, 3]
def baseStart_118627 : Nat := 118140960795 + 118627 * 2 ^ 59
def prefixEnd_118627 : Nat := 4983230072969 + 3 ^ 40 * 118627 * 2
def baseEnd_118627 : Nat := 36096396800600062232267

theorem tailTrace_118627 : CollatzResearch.WordTrace tailWord_118627 prefixEnd_118627 36096396800600062232267 := by
  unfold tailWord_118627
  simp only [CollatzResearch.WordTrace]
  refine ⟨4326682141242113723738135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2884454760828075815825423 4326682141242113723738135)
  ·
    refine ⟨6490023211863170585607203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4326682141242113723738135 6490023211863170585607203)
    ·
      refine ⟨9735034817794755878410805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6490023211863170585607203 9735034817794755878410805)
      ·
        refine ⟨912659514168258363601013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9735034817794755878410805 912659514168258363601013)
        ·
          refine ⟨85561829453274221587595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 912659514168258363601013 85561829453274221587595)
          ·
            refine ⟨128342744179911332381393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85561829453274221587595 128342744179911332381393)
            ·
              refine ⟨96257058134933499286045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128342744179911332381393 96257058134933499286045)
              ·
                refine ⟨36096396800600062232267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96257058134933499286045 36096396800600062232267)
                ·
                  rfl

theorem cell19_118627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 2, 3].length) (baseStart_118627 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118627 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118627 prefixEnd_118627 := by exact prefixLift 118627
  have htrace : WordTrace (prefixWord ++ tailWord_118627) baseStart_118627 baseEnd_118627 := by
    simpa [prefixWord, tailWord_118627, baseEnd_118627] using wordTrace_append hprefix tailTrace_118627
  have hstable : (prefixWord ++ tailWord_118627).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118627).length < 2 ^ (prefixWord ++ tailWord_118627).sum := by decide
  have hdescent : baseEnd_118627 < baseStart_118627 := by decide
  rcases family_descends (prefixWord ++ tailWord_118627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118646 : List Nat := [5, 1, 1, 3, 3, 1, 5]
def baseStart_118646 : Nat := 118140960795 + 118646 * 2 ^ 59
def prefixEnd_118646 : Nat := 4983230072969 + 3 ^ 40 * 118646 * 2
def baseEnd_118646 : Nat := 12034059404137882603331

theorem tailTrace_118646 : CollatzResearch.WordTrace tailWord_118646 prefixEnd_118646 12034059404137882603331 := by
  unfold tailWord_118646
  simp only [CollatzResearch.WordTrace]
  refine ⟨270460945510829998042487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2884916752115519979119861 270460945510829998042487)
  ·
    refine ⟨405691418266244997063731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270460945510829998042487 405691418266244997063731)
    ·
      refine ⟨608537127399367495595597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 405691418266244997063731 608537127399367495595597)
      ·
        refine ⟨228201422774762810848349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 608537127399367495595597 228201422774762810848349)
        ·
          refine ⟨85575533540536054068131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228201422774762810848349 85575533540536054068131)
          ·
            refine ⟨128363300310804081102197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85575533540536054068131 128363300310804081102197)
            ·
              refine ⟨12034059404137882603331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128363300310804081102197 12034059404137882603331)
              ·
                rfl

theorem cell19_118646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 5].length) (baseStart_118646 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118646 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118646 prefixEnd_118646 := by exact prefixLift 118646
  have htrace : WordTrace (prefixWord ++ tailWord_118646) baseStart_118646 baseEnd_118646 := by
    simpa [prefixWord, tailWord_118646, baseEnd_118646] using wordTrace_append hprefix tailTrace_118646
  have hstable : (prefixWord ++ tailWord_118646).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118646).length < 2 ^ (prefixWord ++ tailWord_118646).sum := by decide
  have hdescent : baseEnd_118646 < baseStart_118646 := by decide
  rcases family_descends (prefixWord ++ tailWord_118646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118709 : List Nat := [1, 3, 3, 2, 1, 9]
def baseStart_118709 : Nat := 118140960795 + 118709 * 2 ^ 59
def prefixEnd_118709 : Nat := 4983230072969 + 3 ^ 40 * 118709 * 2
def baseEnd_118709 : Nat := 4013483128538685378869

theorem tailTrace_118709 : CollatzResearch.WordTrace tailWord_118709 prefixEnd_118709 4013483128538685378869 := by
  unfold tailWord_118709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4329672926945041728223181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2886448617963361152148787 4329672926945041728223181)
  ·
    refine ⟨1623627347604390648083693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4329672926945041728223181 1623627347604390648083693)
    ·
      refine ⟨608860255351646493031385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1623627347604390648083693 608860255351646493031385)
      ·
        refine ⟨456645191513734869773539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 608860255351646493031385 456645191513734869773539)
        ·
          refine ⟨684967787270602304660309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456645191513734869773539 684967787270602304660309)
          ·
            refine ⟨4013483128538685378869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 684967787270602304660309 4013483128538685378869)
            ·
              rfl

theorem cell19_118709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_118709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118709 prefixEnd_118709 := by exact prefixLift 118709
  have htrace : WordTrace (prefixWord ++ tailWord_118709) baseStart_118709 baseEnd_118709 := by
    simpa [prefixWord, tailWord_118709, baseEnd_118709] using wordTrace_append hprefix tailTrace_118709
  have hstable : (prefixWord ++ tailWord_118709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118709).length < 2 ^ (prefixWord ++ tailWord_118709).sum := by decide
  have hdescent : baseEnd_118709 < baseStart_118709 := by decide
  rcases family_descends (prefixWord ++ tailWord_118709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118785 : List Nat := [1, 2, 4, 1, 2, 1, 2, 6]
def baseStart_118785 : Nat := 118140960795 + 118785 * 2 ^ 59
def prefixEnd_118785 : Nat := 4983230072969 + 3 ^ 40 * 118785 * 2
def baseEnd_118785 : Nat := 36144473804102510720725

theorem tailTrace_118785 : CollatzResearch.WordTrace tailWord_118785 prefixEnd_118785 36144473804102510720725 := by
  unfold tailWord_118785
  simp only [CollatzResearch.WordTrace]
  refine ⟨4332444874669706707989809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2888296583113137805326539 4332444874669706707989809)
  ·
    refine ⟨3249333656002280030992357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4332444874669706707989809 3249333656002280030992357)
    ·
      refine ⟨609250060500427505811067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3249333656002280030992357 609250060500427505811067)
      ·
        refine ⟨913875090750641258716601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609250060500427505811067 913875090750641258716601)
        ·
          refine ⟨685406318062980944037451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913875090750641258716601 685406318062980944037451)
          ·
            refine ⟨1028109477094471416056177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685406318062980944037451 1028109477094471416056177)
            ·
              refine ⟨771082107820853562042133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028109477094471416056177 771082107820853562042133)
              ·
                refine ⟨36144473804102510720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 771082107820853562042133 36144473804102510720725)
                ·
                  rfl

theorem cell19_118785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_118785 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118785 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118785 prefixEnd_118785 := by exact prefixLift 118785
  have htrace : WordTrace (prefixWord ++ tailWord_118785) baseStart_118785 baseEnd_118785 := by
    simpa [prefixWord, tailWord_118785, baseEnd_118785] using wordTrace_append hprefix tailTrace_118785
  have hstable : (prefixWord ++ tailWord_118785).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118785).length < 2 ^ (prefixWord ++ tailWord_118785).sum := by decide
  have hdescent : baseEnd_118785 < baseStart_118785 := by decide
  rcases family_descends (prefixWord ++ tailWord_118785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118840 : List Nat := [2, 1, 2, 1, 6, 1, 2, 4]
def baseStart_118840 : Nat := 118140960795 + 118840 * 2 ^ 59
def prefixEnd_118840 : Nat := 4983230072969 + 3 ^ 40 * 118840 * 2
def baseEnd_118840 : Nat := 36161209469878679498353

theorem tailTrace_118840 : CollatzResearch.WordTrace tailWord_118840 prefixEnd_118840 36161209469878679498353 := by
  unfold tailWord_118840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2167225444735225550620987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2889633926313634067494649 2167225444735225550620987)
  ·
    refine ⟨3250838167102838325931481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2167225444735225550620987 3250838167102838325931481)
    ·
      refine ⟨2438128625327128744448611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3250838167102838325931481 2438128625327128744448611)
      ·
        refine ⟨3657192937990693116672917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2438128625327128744448611 3657192937990693116672917)
        ·
          refine ⟨171430918968313739844043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3657192937990693116672917 171430918968313739844043)
          ·
            refine ⟨257146378452470609766065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171430918968313739844043 257146378452470609766065)
            ·
              refine ⟨192859783839352957324549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257146378452470609766065 192859783839352957324549)
              ·
                refine ⟨36161209469878679498353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192859783839352957324549 36161209469878679498353)
                ·
                  rfl

theorem cell19_118840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_118840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118840 prefixEnd_118840 := by exact prefixLift 118840
  have htrace : WordTrace (prefixWord ++ tailWord_118840) baseStart_118840 baseEnd_118840 := by
    simpa [prefixWord, tailWord_118840, baseEnd_118840] using wordTrace_append hprefix tailTrace_118840
  have hstable : (prefixWord ++ tailWord_118840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118840).length < 2 ^ (prefixWord ++ tailWord_118840).sum := by decide
  have hdescent : baseEnd_118840 < baseStart_118840 := by decide
  rcases family_descends (prefixWord ++ tailWord_118840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118916 : List Nat := [2, 3, 2, 1, 2, 1, 5, 3]
def baseStart_118916 : Nat := 118140960795 + 118916 * 2 ^ 59
def prefixEnd_118916 : Nat := 4983230072969 + 3 ^ 40 * 118916 * 2
def baseEnd_118916 : Nat := 36184335117133021809257

theorem tailTrace_118916 : CollatzResearch.WordTrace tailWord_118916 prefixEnd_118916 36184335117133021809257 := by
  unfold tailWord_118916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2168611418597558040504301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2891481891463410720672401 2168611418597558040504301)
  ·
    refine ⟨813229281974084265189113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2168611418597558040504301 813229281974084265189113)
    ·
      refine ⟨609921961480563198891835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813229281974084265189113 609921961480563198891835)
      ·
        refine ⟨914882942220844798337753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609921961480563198891835 914882942220844798337753)
        ·
          refine ⟨686162206665633598753315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 914882942220844798337753 686162206665633598753315)
          ·
            refine ⟨1029243309998450398129973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 686162206665633598753315 1029243309998450398129973)
            ·
              refine ⟨96491560312354724824685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1029243309998450398129973 96491560312354724824685)
              ·
                refine ⟨36184335117133021809257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96491560312354724824685 36184335117133021809257)
                ·
                  rfl

theorem cell19_118916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_118916 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118916 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118916 prefixEnd_118916 := by exact prefixLift 118916
  have htrace : WordTrace (prefixWord ++ tailWord_118916) baseStart_118916 baseEnd_118916 := by
    simpa [prefixWord, tailWord_118916, baseEnd_118916] using wordTrace_append hprefix tailTrace_118916
  have hstable : (prefixWord ++ tailWord_118916).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118916).length < 2 ^ (prefixWord ++ tailWord_118916).sum := by decide
  have hdescent : baseEnd_118916 < baseStart_118916 := by decide
  rcases family_descends (prefixWord ++ tailWord_118916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_118994 : List Nat := [3, 2, 2, 2, 1, 2, 7]
def baseStart_118994 : Nat := 118140960795 + 118994 * 2 ^ 59
def prefixEnd_118994 : Nat := 4983230072969 + 3 ^ 40 * 118994 * 2
def baseEnd_118994 : Nat := 12069356444683984025237

theorem tailTrace_118994 : CollatzResearch.WordTrace tailWord_118994 prefixEnd_118994 12069356444683984025237 := by
  unfold tailWord_118994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085016932728133850587009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2893378487275023601565357 1085016932728133850587009)
  ·
    refine ⟨813762699546100387940257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1085016932728133850587009 813762699546100387940257)
    ·
      refine ⟨610322024659575290955193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 813762699546100387940257 610322024659575290955193)
      ·
        refine ⟨457741518494681468216395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 610322024659575290955193 457741518494681468216395)
        ·
          refine ⟨686612277742022202324593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457741518494681468216395 686612277742022202324593)
          ·
            refine ⟨514959208306516651743445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 686612277742022202324593 514959208306516651743445)
            ·
              refine ⟨12069356444683984025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 514959208306516651743445 12069356444683984025237)
              ·
                rfl

theorem cell19_118994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_118994 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_118994 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_118994 prefixEnd_118994 := by exact prefixLift 118994
  have htrace : WordTrace (prefixWord ++ tailWord_118994) baseStart_118994 baseEnd_118994 := by
    simpa [prefixWord, tailWord_118994, baseEnd_118994] using wordTrace_append hprefix tailTrace_118994
  have hstable : (prefixWord ++ tailWord_118994).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_118994).length < 2 ^ (prefixWord ++ tailWord_118994).sum := by decide
  have hdescent : baseEnd_118994 < baseStart_118994 := by decide
  rcases family_descends (prefixWord ++ tailWord_118994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119013 : List Nat := [1, 3, 1, 4, 2, 1, 1, 6]
def baseStart_119013 : Nat := 118140960795 + 119013 * 2 ^ 59
def prefixEnd_119013 : Nat := 4983230072969 + 3 ^ 40 * 119013 * 2
def baseEnd_119013 : Nat := 36213850745865537653437

theorem tailTrace_119013 : CollatzResearch.WordTrace tailWord_119013 prefixEnd_119013 36213850745865537653437 := by
  unfold tailWord_119013
  simp only [CollatzResearch.WordTrace]
  refine ⟨4340760717843701647289693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2893840478562467764859795 4340760717843701647289693)
  ·
    refine ⟨1627785269191388117733635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4340760717843701647289693 1627785269191388117733635)
    ·
      refine ⟨2441677903787082176600453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1627785269191388117733635 2441677903787082176600453)
      ·
        refine ⟨457814606960077908112585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2441677903787082176600453 457814606960077908112585)
        ·
          refine ⟨343360955220058431084439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457814606960077908112585 343360955220058431084439)
          ·
            refine ⟨515041432830087646626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343360955220058431084439 515041432830087646626659)
            ·
              refine ⟨772562149245131469939989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 515041432830087646626659 772562149245131469939989)
              ·
                refine ⟨36213850745865537653437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 772562149245131469939989 36213850745865537653437)
                ·
                  rfl

theorem cell19_119013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_119013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119013 prefixEnd_119013 := by exact prefixLift 119013
  have htrace : WordTrace (prefixWord ++ tailWord_119013) baseStart_119013 baseEnd_119013 := by
    simpa [prefixWord, tailWord_119013, baseEnd_119013] using wordTrace_append hprefix tailTrace_119013
  have hstable : (prefixWord ++ tailWord_119013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119013).length < 2 ^ (prefixWord ++ tailWord_119013).sum := by decide
  have hdescent : baseEnd_119013 < baseStart_119013 := by decide
  rcases family_descends (prefixWord ++ tailWord_119013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119066 : List Nat := [3, 1, 1, 3, 5, 1, 1, 4]
def baseStart_119066 : Nat := 118140960795 + 119066 * 2 ^ 59
def prefixEnd_119066 : Nat := 4983230072969 + 3 ^ 40 * 119066 * 2
def baseEnd_119066 : Nat := 36229977841977118475515

theorem tailTrace_119066 : CollatzResearch.WordTrace tailWord_119066 prefixEnd_119066 36229977841977118475515 := by
  unfold tailWord_119066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1085673446662922924742263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2895129191101127799312701 1085673446662922924742263)
  ·
    refine ⟨1628510169994384387113395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1085673446662922924742263 1628510169994384387113395)
    ·
      refine ⟨2442765254991576580670093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1628510169994384387113395 2442765254991576580670093)
      ·
        refine ⟨916036970621841217751285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2442765254991576580670093 916036970621841217751285)
        ·
          refine ⟨85878465995797614164183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 916036970621841217751285 85878465995797614164183)
          ·
            refine ⟨128817698993696421246275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85878465995797614164183 128817698993696421246275)
            ·
              refine ⟨193226548490544631869413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128817698993696421246275 193226548490544631869413)
              ·
                refine ⟨36229977841977118475515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193226548490544631869413 36229977841977118475515)
                ·
                  rfl

theorem cell19_119066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_119066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119066 prefixEnd_119066 := by exact prefixLift 119066
  have htrace : WordTrace (prefixWord ++ tailWord_119066) baseStart_119066 baseEnd_119066 := by
    simpa [prefixWord, tailWord_119066, baseEnd_119066] using wordTrace_append hprefix tailTrace_119066
  have hstable : (prefixWord ++ tailWord_119066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119066).length < 2 ^ (prefixWord ++ tailWord_119066).sum := by decide
  have hdescent : baseEnd_119066 < baseStart_119066 := by decide
  rcases family_descends (prefixWord ++ tailWord_119066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119129 : List Nat := [1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_119129 : Nat := 118140960795 + 119129 * 2 ^ 59
def prefixEnd_119129 : Nat := 4983230072969 + 3 ^ 40 * 119129 * 2
def baseEnd_119129 : Nat := 36249147786411639075343

theorem tailTrace_119129 : CollatzResearch.WordTrace tailWord_119129 prefixEnd_119129 36249147786411639075343 := by
  unfold tailWord_119129
  simp only [CollatzResearch.WordTrace]
  refine ⟨4344991585423453458512441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2896661056948968972341627 4344991585423453458512441)
  ·
    refine ⟨3258743689067590093884331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4344991585423453458512441 3258743689067590093884331)
    ·
      refine ⟨4888115533601385140826497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3258743689067590093884331 4888115533601385140826497)
      ·
        refine ⟨3666086650201038855619873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4888115533601385140826497 3666086650201038855619873)
        ·
          refine ⟨2749564987650779141714905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3666086650201038855619873 2749564987650779141714905)
          ·
            refine ⟨2062173740738084356286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2749564987650779141714905 2062173740738084356286179)
            ·
              refine ⟨3093260611107126534429269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2062173740738084356286179 3093260611107126534429269)
              ·
                refine ⟨36249147786411639075343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3093260611107126534429269 36249147786411639075343)
                ·
                  rfl

theorem cell19_119129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_119129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119129 prefixEnd_119129 := by exact prefixLift 119129
  have htrace : WordTrace (prefixWord ++ tailWord_119129) baseStart_119129 baseEnd_119129 := by
    simpa [prefixWord, tailWord_119129, baseEnd_119129] using wordTrace_append hprefix tailTrace_119129
  have hstable : (prefixWord ++ tailWord_119129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119129).length < 2 ^ (prefixWord ++ tailWord_119129).sum := by decide
  have hdescent : baseEnd_119129 < baseStart_119129 := by decide
  rcases family_descends (prefixWord ++ tailWord_119129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119134 : List Nat := [4, 4, 2, 1, 2, 1, 2, 3]
def baseStart_119134 : Nat := 118140960795 + 119134 * 2 ^ 59
def prefixEnd_119134 : Nat := 4983230072969 + 3 ^ 40 * 119134 * 2
def baseEnd_119134 : Nat := 36250669210573108964219

theorem tailTrace_119134 : CollatzResearch.WordTrace tailWord_119134 prefixEnd_119134 36250669210573108964219 := by
  unfold tailWord_119134
  simp only [CollatzResearch.WordTrace]
  refine ⟨543146743800667414055557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2896782633603559541629637 543146743800667414055557)
  ·
    refine ⟨101840014462625140135417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 543146743800667414055557 101840014462625140135417)
    ·
      refine ⟨76380010846968855101563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101840014462625140135417 76380010846968855101563)
      ·
        refine ⟨114570016270453282652345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76380010846968855101563 114570016270453282652345)
        ·
          refine ⟨85927512202839961989259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114570016270453282652345 85927512202839961989259)
          ·
            refine ⟨128891268304259942983889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85927512202839961989259 128891268304259942983889)
            ·
              refine ⟨96668451228194957237917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128891268304259942983889 96668451228194957237917)
              ·
                refine ⟨36250669210573108964219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96668451228194957237917 36250669210573108964219)
                ·
                  rfl

theorem cell19_119134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_119134 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119134 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119134 prefixEnd_119134 := by exact prefixLift 119134
  have htrace : WordTrace (prefixWord ++ tailWord_119134) baseStart_119134 baseEnd_119134 := by
    simpa [prefixWord, tailWord_119134, baseEnd_119134] using wordTrace_append hprefix tailTrace_119134
  have hstable : (prefixWord ++ tailWord_119134).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119134).length < 2 ^ (prefixWord ++ tailWord_119134).sum := by decide
  have hdescent : baseEnd_119134 < baseStart_119134 := by decide
  rcases family_descends (prefixWord ++ tailWord_119134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119144 : List Nat := [2, 1, 4, 2, 2, 1, 4, 3]
def baseStart_119144 : Nat := 118140960795 + 119144 * 2 ^ 59
def prefixEnd_119144 : Nat := 4983230072969 + 3 ^ 40 * 119144 * 2
def baseEnd_119144 : Nat := 36253712058896048741969

theorem tailTrace_119144 : CollatzResearch.WordTrace tailWord_119144 prefixEnd_119144 36253712058896048741969 := by
  unfold tailWord_119144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2172769340184555510154243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2897025786912740680205657 2172769340184555510154243)
  ·
    refine ⟨3259154010276833265231365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2172769340184555510154243 3259154010276833265231365)
    ·
      refine ⟨611091376926906237230881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3259154010276833265231365 611091376926906237230881)
      ·
        refine ⟨458318532695179677923161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 611091376926906237230881 458318532695179677923161)
        ·
          refine ⟨343738899521384758442371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 458318532695179677923161 343738899521384758442371)
          ·
            refine ⟨515608349282077137663557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 343738899521384758442371 515608349282077137663557)
            ·
              refine ⟨96676565490389463311917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 515608349282077137663557 96676565490389463311917)
              ·
                refine ⟨36253712058896048741969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96676565490389463311917 36253712058896048741969)
                ·
                  rfl

theorem cell19_119144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_119144 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119144 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119144 prefixEnd_119144 := by exact prefixLift 119144
  have htrace : WordTrace (prefixWord ++ tailWord_119144) baseStart_119144 baseEnd_119144 := by
    simpa [prefixWord, tailWord_119144, baseEnd_119144] using wordTrace_append hprefix tailTrace_119144
  have hstable : (prefixWord ++ tailWord_119144).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119144).length < 2 ^ (prefixWord ++ tailWord_119144).sum := by decide
  have hdescent : baseEnd_119144 < baseStart_119144 := by decide
  rcases family_descends (prefixWord ++ tailWord_119144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119165 : List Nat := [1, 4, 1, 1, 2, 5, 5]
def baseStart_119165 : Nat := 118140960795 + 119165 * 2 ^ 59
def prefixEnd_119165 : Nat := 4983230072969 + 3 ^ 40 * 119165 * 2
def baseEnd_119165 : Nat := 12086700680124740758415

theorem tailTrace_119165 : CollatzResearch.WordTrace tailWord_119165 prefixEnd_119165 12086700680124740758415 := by
  unfold tailWord_119165
  simp only [CollatzResearch.WordTrace]
  refine ⟨4346304613293031606822949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2897536408862021071215299 4346304613293031606822949)
  ·
    refine ⟨814932114992443426279303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4346304613293031606822949 814932114992443426279303)
    ·
      refine ⟨1222398172488665139418955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 814932114992443426279303 1222398172488665139418955)
      ·
        refine ⟨1833597258732997709128433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1222398172488665139418955 1833597258732997709128433)
        ·
          refine ⟨1375197944049748281846325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1833597258732997709128433 1375197944049748281846325)
          ·
            refine ⟨128924807254663901423093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1375197944049748281846325 128924807254663901423093)
            ·
              refine ⟨12086700680124740758415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128924807254663901423093 12086700680124740758415)
              ·
                rfl

theorem cell19_119165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_119165 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119165 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119165 prefixEnd_119165 := by exact prefixLift 119165
  have htrace : WordTrace (prefixWord ++ tailWord_119165) baseStart_119165 baseEnd_119165 := by
    simpa [prefixWord, tailWord_119165, baseEnd_119165] using wordTrace_append hprefix tailTrace_119165
  have hstable : (prefixWord ++ tailWord_119165).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119165).length < 2 ^ (prefixWord ++ tailWord_119165).sum := by decide
  have hdescent : baseEnd_119165 < baseStart_119165 := by decide
  rcases family_descends (prefixWord ++ tailWord_119165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119182 : List Nat := [4, 1, 1, 4, 1, 2, 2, 4]
def baseStart_119182 : Nat := 118140960795 + 119182 * 2 ^ 59
def prefixEnd_119182 : Nat := 4983230072969 + 3 ^ 40 * 119182 * 2
def baseEnd_119182 : Nat := 36265274882523219897421

theorem tailTrace_119182 : CollatzResearch.WordTrace tailWord_119182 prefixEnd_119182 36265274882523219897421 := by
  unfold tailWord_119182
  simp only [CollatzResearch.WordTrace]
  refine ⟨543365581778930438773975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2897949769487629006794533 543365581778930438773975)
  ·
    refine ⟨815048372668395658160963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 543365581778930438773975 815048372668395658160963)
    ·
      refine ⟨1222572559002593487241445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 815048372668395658160963 1222572559002593487241445)
      ·
        refine ⟨229232354812986278857771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1222572559002593487241445 229232354812986278857771)
        ·
          refine ⟨343848532219479418286657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229232354812986278857771 343848532219479418286657)
          ·
            refine ⟨257886399164609563714993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 343848532219479418286657 257886399164609563714993)
            ·
              refine ⟨193414799373457172786245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257886399164609563714993 193414799373457172786245)
              ·
                refine ⟨36265274882523219897421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193414799373457172786245 36265274882523219897421)
                ·
                  rfl

theorem cell19_119182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_119182 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119182 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119182 prefixEnd_119182 := by exact prefixLift 119182
  have htrace : WordTrace (prefixWord ++ tailWord_119182) baseStart_119182 baseEnd_119182 := by
    simpa [prefixWord, tailWord_119182, baseEnd_119182] using wordTrace_append hprefix tailTrace_119182
  have hstable : (prefixWord ++ tailWord_119182).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119182).length < 2 ^ (prefixWord ++ tailWord_119182).sum := by decide
  have hdescent : baseEnd_119182 < baseStart_119182 := by decide
  rcases family_descends (prefixWord ++ tailWord_119182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119205 : List Nat := [1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_119205 : Nat := 118140960795 + 119205 * 2 ^ 59
def prefixEnd_119205 : Nat := 4983230072969 + 3 ^ 40 * 119205 * 2
def baseEnd_119205 : Nat := 36272273433665981386247

theorem tailTrace_119205 : CollatzResearch.WordTrace tailWord_119205 prefixEnd_119205 36272273433665981386247 := by
  unfold tailWord_119205
  simp only [CollatzResearch.WordTrace]
  refine ⟨4347763533148118438279069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2898509022098745625519379 4347763533148118438279069)
  ·
    refine ⟨1630411324930544414354651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4347763533148118438279069 1630411324930544414354651)
    ·
      refine ⟨2445616987395816621531977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1630411324930544414354651 2445616987395816621531977)
      ·
        refine ⟨1834212740546862466148983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2445616987395816621531977 1834212740546862466148983)
        ·
          refine ⟨2751319110820293699223475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1834212740546862466148983 2751319110820293699223475)
          ·
            refine ⟨4126978666230440548835213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2751319110820293699223475 4126978666230440548835213)
            ·
              refine ⟨1547616999836415205813205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4126978666230440548835213 1547616999836415205813205)
              ·
                refine ⟨36272273433665981386247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1547616999836415205813205 36272273433665981386247)
                ·
                  rfl

theorem cell19_119205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_119205 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119205 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119205 prefixEnd_119205 := by exact prefixLift 119205
  have htrace : WordTrace (prefixWord ++ tailWord_119205) baseStart_119205 baseEnd_119205 := by
    simpa [prefixWord, tailWord_119205, baseEnd_119205] using wordTrace_append hprefix tailTrace_119205
  have hstable : (prefixWord ++ tailWord_119205).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119205).length < 2 ^ (prefixWord ++ tailWord_119205).sum := by decide
  have hdescent : baseEnd_119205 < baseStart_119205 := by decide
  rcases family_descends (prefixWord ++ tailWord_119205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119220 : List Nat := [2, 5, 2, 2, 8]
def baseStart_119220 : Nat := 118140960795 + 119220 * 2 ^ 59
def prefixEnd_119220 : Nat := 4983230072969 + 3 ^ 40 * 119220 * 2
def baseEnd_119220 : Nat := 1343586581709273742699

theorem tailTrace_119220 : CollatzResearch.WordTrace tailWord_119220 prefixEnd_119220 1343586581709273742699 := by
  unfold tailWord_119220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2174155314046888000037557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2898873752062517333383409 2174155314046888000037557)
  ·
    refine ⟨203827060691895750003521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2174155314046888000037557 203827060691895750003521)
    ·
      refine ⟨152870295518921812502641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203827060691895750003521 152870295518921812502641)
      ·
        refine ⟨114652721639191359376981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152870295518921812502641 114652721639191359376981)
        ·
          refine ⟨1343586581709273742699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 114652721639191359376981 1343586581709273742699)
          ·
            rfl

theorem cell19_119220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 8].length) (baseStart_119220 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119220 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119220 prefixEnd_119220 := by exact prefixLift 119220
  have htrace : WordTrace (prefixWord ++ tailWord_119220) baseStart_119220 baseEnd_119220 := by
    simpa [prefixWord, tailWord_119220, baseEnd_119220] using wordTrace_append hprefix tailTrace_119220
  have hstable : (prefixWord ++ tailWord_119220).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119220).length < 2 ^ (prefixWord ++ tailWord_119220).sum := by decide
  have hdescent : baseEnd_119220 < baseStart_119220 := by decide
  rcases family_descends (prefixWord ++ tailWord_119220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119233 : List Nat := [1, 2, 7, 1, 2, 1, 1, 4]
def baseStart_119233 : Nat := 118140960795 + 119233 * 2 ^ 59
def prefixEnd_119233 : Nat := 4983230072969 + 3 ^ 40 * 119233 * 2
def baseEnd_119233 : Nat := 36280793408970212763949

theorem tailTrace_119233 : CollatzResearch.WordTrace tailWord_119233 prefixEnd_119233 36280793408970212763949 := by
  unfold tailWord_119233
  simp only [CollatzResearch.WordTrace]
  refine ⟨4348784777046679220298353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2899189851364452813532235 4348784777046679220298353)
  ·
    refine ⟨3261588582785009415223765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4348784777046679220298353 3261588582785009415223765)
    ·
      refine ⟨76443482409023658169307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 3261588582785009415223765 76443482409023658169307)
      ·
        refine ⟨114665223613535487253961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76443482409023658169307 114665223613535487253961)
        ·
          refine ⟨85998917710151615440471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114665223613535487253961 85998917710151615440471)
          ·
            refine ⟨128998376565227423160707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85998917710151615440471 128998376565227423160707)
            ·
              refine ⟨193497564847841134741061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128998376565227423160707 193497564847841134741061)
              ·
                refine ⟨36280793408970212763949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193497564847841134741061 36280793408970212763949)
                ·
                  rfl

theorem cell19_119233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 4].length) (baseStart_119233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119233 prefixEnd_119233 := by exact prefixLift 119233
  have htrace : WordTrace (prefixWord ++ tailWord_119233) baseStart_119233 baseEnd_119233 := by
    simpa [prefixWord, tailWord_119233, baseEnd_119233] using wordTrace_append hprefix tailTrace_119233
  have hstable : (prefixWord ++ tailWord_119233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119233).length < 2 ^ (prefixWord ++ tailWord_119233).sum := by decide
  have hdescent : baseEnd_119233 < baseStart_119233 := by decide
  rcases family_descends (prefixWord ++ tailWord_119233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119281 : List Nat := [1, 2, 2, 2, 3, 1, 8]
def baseStart_119281 : Nat := 118140960795 + 119281 * 2 ^ 59
def prefixEnd_119281 : Nat := 4983230072969 + 3 ^ 40 * 119281 * 2
def baseEnd_119281 : Nat := 12098466360306774565717

theorem tailTrace_119281 : CollatzResearch.WordTrace tailWord_119281 prefixEnd_119281 12098466360306774565717 := by
  unfold tailWord_119281
  simp only [CollatzResearch.WordTrace]
  refine ⟨4350535480872783418045697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2900356987248522278697131 4350535480872783418045697)
  ·
    refine ⟨3262901610654587563534273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4350535480872783418045697 3262901610654587563534273)
    ·
      refine ⟨2447176207990940672650705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3262901610654587563534273 2447176207990940672650705)
      ·
        refine ⟨1835382155993205504488029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2447176207990940672650705 1835382155993205504488029)
        ·
          refine ⟨688268308497452064183011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1835382155993205504488029 688268308497452064183011)
          ·
            refine ⟨1032402462746178096274517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 688268308497452064183011 1032402462746178096274517)
            ·
              refine ⟨12098466360306774565717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1032402462746178096274517 12098466360306774565717)
              ·
                rfl

theorem cell19_119281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 8].length) (baseStart_119281 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119281 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119281 prefixEnd_119281 := by exact prefixLift 119281
  have htrace : WordTrace (prefixWord ++ tailWord_119281) baseStart_119281 baseEnd_119281 := by
    simpa [prefixWord, tailWord_119281, baseEnd_119281] using wordTrace_append hprefix tailTrace_119281
  have hstable : (prefixWord ++ tailWord_119281).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119281).length < 2 ^ (prefixWord ++ tailWord_119281).sum := by decide
  have hdescent : baseEnd_119281 < baseStart_119281 := by decide
  rcases family_descends (prefixWord ++ tailWord_119281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119332 : List Nat := [2, 3, 1, 5, 2, 1, 5]
def baseStart_119332 : Nat := 118140960795 + 119332 * 2 ^ 59
def prefixEnd_119332 : Nat := 4983230072969 + 3 ^ 40 * 119332 * 2
def baseEnd_119332 : Nat := 12103639202455772187893

theorem tailTrace_119332 : CollatzResearch.WordTrace tailWord_119332 prefixEnd_119332 12103639202455772187893 := by
  unfold tailWord_119332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176197801844009564076125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2901597069125346085434833 2176197801844009564076125)
  ·
    refine ⟨816074175691503586528547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2176197801844009564076125 816074175691503586528547)
    ·
      refine ⟨1224111263537255379792821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816074175691503586528547 1224111263537255379792821)
      ·
        refine ⟨114760430956617691855577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1224111263537255379792821 114760430956617691855577)
        ·
          refine ⟨86070323217463268891683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114760430956617691855577 86070323217463268891683)
          ·
            refine ⟨129105484826194903337525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86070323217463268891683 129105484826194903337525)
            ·
              refine ⟨12103639202455772187893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129105484826194903337525 12103639202455772187893)
              ·
                rfl

theorem cell19_119332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 5].length) (baseStart_119332 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119332 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119332 prefixEnd_119332 := by exact prefixLift 119332
  have htrace : WordTrace (prefixWord ++ tailWord_119332) baseStart_119332 baseEnd_119332 := by
    simpa [prefixWord, tailWord_119332, baseEnd_119332] using wordTrace_append hprefix tailTrace_119332
  have hstable : (prefixWord ++ tailWord_119332).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119332).length < 2 ^ (prefixWord ++ tailWord_119332).sum := by decide
  have hdescent : baseEnd_119332 < baseStart_119332 := by decide
  rcases family_descends (prefixWord ++ tailWord_119332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119336 : List Nat := [2, 1, 5, 2, 1, 1, 7]
def baseStart_119336 : Nat := 118140960795 + 119336 * 2 ^ 59
def prefixEnd_119336 : Nat := 4983230072969 + 3 ^ 40 * 119336 * 2
def baseEnd_119336 : Nat := 12104044915565497491593

theorem tailTrace_119336 : CollatzResearch.WordTrace tailWord_119336 prefixEnd_119336 12104044915565497491593 := by
  unfold tailWord_119336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2176270747836763905648931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2901694330449018540865241 2176270747836763905648931)
  ·
    refine ⟨3264406121755145858473397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2176270747836763905648931 3264406121755145858473397)
    ·
      refine ⟨306038073914544924231881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3264406121755145858473397 306038073914544924231881)
      ·
        refine ⟨229528555435908693173911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 306038073914544924231881 229528555435908693173911)
        ·
          refine ⟨344292833153863039760867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 229528555435908693173911 344292833153863039760867)
          ·
            refine ⟨516439249730794559641301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 344292833153863039760867 516439249730794559641301)
            ·
              refine ⟨12104044915565497491593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 516439249730794559641301 12104044915565497491593)
              ·
                rfl

theorem cell19_119336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 7].length) (baseStart_119336 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119336 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119336 prefixEnd_119336 := by exact prefixLift 119336
  have htrace : WordTrace (prefixWord ++ tailWord_119336) baseStart_119336 baseEnd_119336 := by
    simpa [prefixWord, tailWord_119336, baseEnd_119336] using wordTrace_append hprefix tailTrace_119336
  have hstable : (prefixWord ++ tailWord_119336).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119336).length < 2 ^ (prefixWord ++ tailWord_119336).sum := by decide
  have hdescent : baseEnd_119336 < baseStart_119336 := by decide
  rcases family_descends (prefixWord ++ tailWord_119336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119410 : List Nat := [3, 2, 1, 2, 4, 2, 1, 4]
def baseStart_119410 : Nat := 118140960795 + 119410 * 2 ^ 59
def prefixEnd_119410 : Nat := 4983230072969 + 3 ^ 40 * 119410 * 2
def baseEnd_119410 : Nat := 36334651824286246830133

theorem tailTrace_119410 : CollatzResearch.WordTrace tailWord_119410 prefixEnd_119410 36334651824286246830133 := by
  unfold tailWord_119410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1088810124351359612372921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2903493664936958966327789 1088810124351359612372921)
  ·
    refine ⟨816607593263519709279691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1088810124351359612372921 816607593263519709279691)
    ·
      refine ⟨1224911389895279563919537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 816607593263519709279691 1224911389895279563919537)
      ·
        refine ⟨918683542421459672939653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1224911389895279563919537 918683542421459672939653)
        ·
          refine ⟨172253164204023688676185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 918683542421459672939653 172253164204023688676185)
          ·
            refine ⟨129189873153017766507139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172253164204023688676185 129189873153017766507139)
            ·
              refine ⟨193784809729526649760709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129189873153017766507139 193784809729526649760709)
              ·
                refine ⟨36334651824286246830133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 193784809729526649760709 36334651824286246830133)
                ·
                  rfl

theorem cell19_119410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_119410 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119410 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119410 prefixEnd_119410 := by exact prefixLift 119410
  have htrace : WordTrace (prefixWord ++ tailWord_119410) baseStart_119410 baseEnd_119410 := by
    simpa [prefixWord, tailWord_119410, baseEnd_119410] using wordTrace_append hprefix tailTrace_119410
  have hstable : (prefixWord ++ tailWord_119410).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119410).length < 2 ^ (prefixWord ++ tailWord_119410).sum := by decide
  have hdescent : baseEnd_119410 < baseStart_119410 := by decide
  rcases family_descends (prefixWord ++ tailWord_119410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119431 : List Nat := [1, 1, 4, 2, 1, 2, 5, 3]
def baseStart_119431 : Nat := 118140960795 + 119431 * 2 ^ 59
def prefixEnd_119431 : Nat := 4983230072969 + 3 ^ 40 * 119431 * 2
def baseEnd_119431 : Nat := 36341041805764420363409

theorem tailTrace_119431 : CollatzResearch.WordTrace tailWord_119431 prefixEnd_119431 36341041805764420363409 := by
  unfold tailWord_119431
  simp only [CollatzResearch.WordTrace]
  refine ⟨4356006430329359036006147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2904004286886239357337431 4356006430329359036006147)
  ·
    refine ⟨6534009645494038554009221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4356006430329359036006147 6534009645494038554009221)
    ·
      refine ⟨1225126808530132228876729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6534009645494038554009221 1225126808530132228876729)
      ·
        refine ⟨918845106397599171657547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1225126808530132228876729 918845106397599171657547)
        ·
          refine ⟨1378267659596398757486321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 918845106397599171657547 1378267659596398757486321)
          ·
            refine ⟨1033700744697299068114741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1378267659596398757486321 1033700744697299068114741)
            ·
              refine ⟨96909444815371787635757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1033700744697299068114741 96909444815371787635757)
              ·
                refine ⟨36341041805764420363409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96909444815371787635757 36341041805764420363409)
                ·
                  rfl

theorem cell19_119431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5, 3].length) (baseStart_119431 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119431 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119431 prefixEnd_119431 := by exact prefixLift 119431
  have htrace : WordTrace (prefixWord ++ tailWord_119431) baseStart_119431 baseEnd_119431 := by
    simpa [prefixWord, tailWord_119431, baseEnd_119431] using wordTrace_append hprefix tailTrace_119431
  have hstable : (prefixWord ++ tailWord_119431).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119431).length < 2 ^ (prefixWord ++ tailWord_119431).sum := by decide
  have hdescent : baseEnd_119431 < baseStart_119431 := by decide
  rcases family_descends (prefixWord ++ tailWord_119431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119488 : List Nat := [2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_119488 : Nat := 118140960795 + 119488 * 2 ^ 59
def prefixEnd_119488 : Nat := 4983230072969 + 3 ^ 40 * 119488 * 2
def baseEnd_119488 : Nat := 36358386041205177096587

theorem tailTrace_119488 : CollatzResearch.WordTrace tailWord_119488 prefixEnd_119488 36358386041205177096587 := by
  unfold tailWord_119488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2179042695561428885415559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2905390260748571847220745 2179042695561428885415559)
  ·
    refine ⟨3268564043342143328123339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2179042695561428885415559 3268564043342143328123339)
    ·
      refine ⟨4902846065013214992185009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3268564043342143328123339 4902846065013214992185009)
      ·
        refine ⟨3677134548759911244138757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4902846065013214992185009 3677134548759911244138757)
        ·
          refine ⟨689462727892483358276017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3677134548759911244138757 689462727892483358276017)
          ·
            refine ⟨517097045919362518707013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 689462727892483358276017 517097045919362518707013)
            ·
              refine ⟨96955696109880472257565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 517097045919362518707013 96955696109880472257565)
              ·
                refine ⟨36358386041205177096587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96955696109880472257565 36358386041205177096587)
                ·
                  rfl

theorem cell19_119488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_119488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119488 prefixEnd_119488 := by exact prefixLift 119488
  have htrace : WordTrace (prefixWord ++ tailWord_119488) baseStart_119488 baseEnd_119488 := by
    simpa [prefixWord, tailWord_119488, baseEnd_119488] using wordTrace_append hprefix tailTrace_119488
  have hstable : (prefixWord ++ tailWord_119488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119488).length < 2 ^ (prefixWord ++ tailWord_119488).sum := by decide
  have hdescent : baseEnd_119488 < baseStart_119488 := by decide
  rcases family_descends (prefixWord ++ tailWord_119488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119583 : List Nat := [1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_119583 : Nat := 118140960795 + 119583 * 2 ^ 59
def prefixEnd_119583 : Nat := 4983230072969 + 3 ^ 40 * 119583 * 2
def baseEnd_119583 : Nat := 36387293100273104985217

theorem tailTrace_119583 : CollatzResearch.WordTrace tailWord_119583 prefixEnd_119583 36387293100273104985217 := by
  unfold tailWord_119583
  simp only [CollatzResearch.WordTrace]
  refine ⟨4361550325778688995539403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2907700217185792663692935 4361550325778688995539403)
  ·
    refine ⟨6542325488668033493309105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4361550325778688995539403 6542325488668033493309105)
    ·
      refine ⟨4906744116501025119981829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6542325488668033493309105 4906744116501025119981829)
      ·
        refine ⟨920014521843942209996593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4906744116501025119981829 920014521843942209996593)
        ·
          refine ⟨690010891382956657497445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 920014521843942209996593 690010891382956657497445)
          ·
            refine ⟨129377042134304373280771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 690010891382956657497445 129377042134304373280771)
            ·
              refine ⟨194065563201456559921157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129377042134304373280771 194065563201456559921157)
              ·
                refine ⟨36387293100273104985217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194065563201456559921157 36387293100273104985217)
                ·
                  rfl

theorem cell19_119583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_119583 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119583 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119583 prefixEnd_119583 := by exact prefixLift 119583
  have htrace : WordTrace (prefixWord ++ tailWord_119583) baseStart_119583 baseEnd_119583 := by
    simpa [prefixWord, tailWord_119583, baseEnd_119583] using wordTrace_append hprefix tailTrace_119583
  have hstable : (prefixWord ++ tailWord_119583).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119583).length < 2 ^ (prefixWord ++ tailWord_119583).sum := by decide
  have hdescent : baseEnd_119583 < baseStart_119583 := by decide
  rcases family_descends (prefixWord ++ tailWord_119583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119602 : List Nat := [3, 2, 1, 1, 3, 1, 5, 3]
def baseStart_119602 : Nat := 118140960795 + 119602 * 2 ^ 59
def prefixEnd_119602 : Nat := 4983230072969 + 3 ^ 40 * 119602 * 2
def baseEnd_119602 : Nat := 36393074512086690562943

theorem tailTrace_119602 : CollatzResearch.WordTrace tailWord_119602 prefixEnd_119602 36393074512086690562943 := by
  unfold tailWord_119602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1090560828177463810120265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2908162208473236826987373 1090560828177463810120265)
  ·
    refine ⟨817920621133097857590199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1090560828177463810120265 817920621133097857590199)
    ·
      refine ⟨1226880931699646786385299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 817920621133097857590199 1226880931699646786385299)
      ·
        refine ⟨1840321397549470179577949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1226880931699646786385299 1840321397549470179577949)
        ·
          refine ⟨690120524081051317341731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1840321397549470179577949 690120524081051317341731)
          ·
            refine ⟨1035180786121576976012597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 690120524081051317341731 1035180786121576976012597)
            ·
              refine ⟨97048198698897841501181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1035180786121576976012597 97048198698897841501181)
              ·
                refine ⟨36393074512086690562943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97048198698897841501181 36393074512086690562943)
                ·
                  rfl

theorem cell19_119602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 3].length) (baseStart_119602 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119602 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119602 prefixEnd_119602 := by exact prefixLift 119602
  have htrace : WordTrace (prefixWord ++ tailWord_119602) baseStart_119602 baseEnd_119602 := by
    simpa [prefixWord, tailWord_119602, baseEnd_119602] using wordTrace_append hprefix tailTrace_119602
  have hstable : (prefixWord ++ tailWord_119602).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119602).length < 2 ^ (prefixWord ++ tailWord_119602).sum := by decide
  have hdescent : baseEnd_119602 < baseStart_119602 := by decide
  rcases family_descends (prefixWord ++ tailWord_119602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119752 : List Nat := [2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_119752 : Nat := 118140960795 + 119752 * 2 ^ 59
def prefixEnd_119752 : Nat := 4983230072969 + 3 ^ 40 * 119752 * 2
def baseEnd_119752 : Nat := 36438717236930787229201

theorem tailTrace_119752 : CollatzResearch.WordTrace tailWord_119752 prefixEnd_119752 36438717236930787229201 := by
  unfold tailWord_119752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2183857131083215429220755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2911809508110953905627673 2183857131083215429220755)
  ·
    refine ⟨3275785696624823143831133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2183857131083215429220755 3275785696624823143831133)
    ·
      refine ⟨1228419636234308678936675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3275785696624823143831133 1228419636234308678936675)
      ·
        refine ⟨1842629454351463018405013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1228419636234308678936675 1842629454351463018405013)
        ·
          refine ⟨86373255672724828987735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1842629454351463018405013 86373255672724828987735)
          ·
            refine ⟨129559883509087243481603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86373255672724828987735 129559883509087243481603)
            ·
              refine ⟨194339825263630865222405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129559883509087243481603 194339825263630865222405)
              ·
                refine ⟨36438717236930787229201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194339825263630865222405 36438717236930787229201)
                ·
                  rfl

theorem cell19_119752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_119752 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119752 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119752 prefixEnd_119752 := by exact prefixLift 119752
  have htrace : WordTrace (prefixWord ++ tailWord_119752) baseStart_119752 baseEnd_119752 := by
    simpa [prefixWord, tailWord_119752, baseEnd_119752] using wordTrace_append hprefix tailTrace_119752
  have hstable : (prefixWord ++ tailWord_119752).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119752).length < 2 ^ (prefixWord ++ tailWord_119752).sum := by decide
  have hdescent : baseEnd_119752 < baseStart_119752 := by decide
  rcases family_descends (prefixWord ++ tailWord_119752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119826 : List Nat := [3, 2, 5, 1, 1, 1, 1, 5]
def baseStart_119826 : Nat := 118140960795 + 119826 * 2 ^ 59
def prefixEnd_119826 : Nat := 4983230072969 + 3 ^ 40 * 119826 * 2
def baseEnd_119826 : Nat := 36461234314520541584555

theorem tailTrace_119826 : CollatzResearch.WordTrace tailWord_119826 prefixEnd_119826 36461234314520541584555 := by
  unfold tailWord_119826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1092603315974585374158833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2913608842598894331090221 1092603315974585374158833)
  ·
    refine ⟨819452486980939030619125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1092603315974585374158833 819452486980939030619125)
    ·
      refine ⟨76823670654463034120543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 819452486980939030619125 76823670654463034120543)
      ·
        refine ⟨115235505981694551180815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76823670654463034120543 115235505981694551180815)
        ·
          refine ⟨172853258972541826771223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115235505981694551180815 172853258972541826771223)
          ·
            refine ⟨259279888458812740156835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 172853258972541826771223 259279888458812740156835)
            ·
              refine ⟨388919832688219110235253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259279888458812740156835 388919832688219110235253)
              ·
                refine ⟨36461234314520541584555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388919832688219110235253 36461234314520541584555)
                ·
                  rfl

theorem cell19_119826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 5].length) (baseStart_119826 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119826 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119826 prefixEnd_119826 := by exact prefixLift 119826
  have htrace : WordTrace (prefixWord ++ tailWord_119826) baseStart_119826 baseEnd_119826 := by
    simpa [prefixWord, tailWord_119826, baseEnd_119826] using wordTrace_append hprefix tailTrace_119826
  have hstable : (prefixWord ++ tailWord_119826).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119826).length < 2 ^ (prefixWord ++ tailWord_119826).sum := by decide
  have hdescent : baseEnd_119826 < baseStart_119826 := by decide
  rcases family_descends (prefixWord ++ tailWord_119826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119832 : List Nat := [2, 1, 2, 3, 2, 3, 1, 5]
def baseStart_119832 : Nat := 118140960795 + 119832 * 2 ^ 59
def prefixEnd_119832 : Nat := 4983230072969 + 3 ^ 40 * 119832 * 2
def baseEnd_119832 : Nat := 36463060023514305451205

theorem tailTrace_119832 : CollatzResearch.WordTrace tailWord_119832 prefixEnd_119832 36463060023514305451205 := by
  unfold tailWord_119832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2185316050938302260676875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2913754734584403014235833 2185316050938302260676875)
  ·
    refine ⟨3277974076407453391015313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2185316050938302260676875 3277974076407453391015313)
    ·
      refine ⟨2458480557305590043261485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3277974076407453391015313 2458480557305590043261485)
      ·
        refine ⟨921930208989596266223057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2458480557305590043261485 921930208989596266223057)
        ·
          refine ⟨691447656742197199667293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 921930208989596266223057 691447656742197199667293)
          ·
            refine ⟨259292871278323949875235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 691447656742197199667293 259292871278323949875235)
            ·
              refine ⟨388939306917485924812853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259292871278323949875235 388939306917485924812853)
              ·
                refine ⟨36463060023514305451205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 388939306917485924812853 36463060023514305451205)
                ·
                  rfl

theorem cell19_119832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_119832 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119832 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119832 prefixEnd_119832 := by exact prefixLift 119832
  have htrace : WordTrace (prefixWord ++ tailWord_119832) baseStart_119832 baseEnd_119832 := by
    simpa [prefixWord, tailWord_119832, baseEnd_119832] using wordTrace_append hprefix tailTrace_119832
  have hstable : (prefixWord ++ tailWord_119832).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119832).length < 2 ^ (prefixWord ++ tailWord_119832).sum := by decide
  have hdescent : baseEnd_119832 < baseStart_119832 := by decide
  rcases family_descends (prefixWord ++ tailWord_119832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_119948 : List Nat := [2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_119948 : Nat := 118140960795 + 119948 * 2 ^ 59
def prefixEnd_119948 : Nat := 4983230072969 + 3 ^ 40 * 119948 * 2
def baseEnd_119948 : Nat := 36498357064060406873111

theorem tailTrace_119948 : CollatzResearch.WordTrace tailWord_119948 prefixEnd_119948 36498357064060406873111 := by
  unfold tailWord_119948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2187431484728178166288249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2916575312970904221717665 2187431484728178166288249)
  ·
    refine ⟨1640573613546133624716187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2187431484728178166288249 1640573613546133624716187)
    ·
      refine ⟨2460860420319200437074281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1640573613546133624716187 2460860420319200437074281)
      ·
        refine ⟨1845645315239400327805711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2460860420319200437074281 1845645315239400327805711)
        ·
          refine ⟨2768467972859100491708567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1845645315239400327805711 2768467972859100491708567)
          ·
            refine ⟨4152701959288650737562851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2768467972859100491708567 4152701959288650737562851)
            ·
              refine ⟨6229052938932976106344277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4152701959288650737562851 6229052938932976106344277)
              ·
                refine ⟨36498357064060406873111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6229052938932976106344277 36498357064060406873111)
                ·
                  rfl

theorem cell19_119948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_119948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_119948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_119948 prefixEnd_119948 := by exact prefixLift 119948
  have htrace : WordTrace (prefixWord ++ tailWord_119948) baseStart_119948 baseEnd_119948 := by
    simpa [prefixWord, tailWord_119948, baseEnd_119948] using wordTrace_append hprefix tailTrace_119948
  have hstable : (prefixWord ++ tailWord_119948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_119948).length < 2 ^ (prefixWord ++ tailWord_119948).sum := by decide
  have hdescent : baseEnd_119948 < baseStart_119948 := by decide
  rcases family_descends (prefixWord ++ tailWord_119948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120001 : List Nat := [1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_120001 : Nat := 118140960795 + 120001 * 2 ^ 59
def prefixEnd_120001 : Nat := 4983230072969 + 3 ^ 40 * 120001 * 2
def baseEnd_120001 : Nat := 36514484160171987695189

theorem tailTrace_120001 : CollatzResearch.WordTrace tailWord_120001 prefixEnd_120001 36514484160171987695189 := by
  unfold tailWord_120001
  simp only [CollatzResearch.WordTrace]
  refine ⟨4376796038264346384255857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2917864025509564256170571 4376796038264346384255857)
  ·
    refine ⟨3282597028698259788191893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4376796038264346384255857 3282597028698259788191893)
    ·
      refine ⟨153871735720230927571495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3282597028698259788191893 153871735720230927571495)
      ·
        refine ⟨230807603580346391357243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153871735720230927571495 230807603580346391357243)
        ·
          refine ⟨346211405370519587035865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230807603580346391357243 346211405370519587035865)
          ·
            refine ⟨259658554027889690276899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 346211405370519587035865 259658554027889690276899)
            ·
              refine ⟨389487831041834535415349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 259658554027889690276899 389487831041834535415349)
              ·
                refine ⟨36514484160171987695189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 389487831041834535415349 36514484160171987695189)
                ·
                  rfl

theorem cell19_120001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_120001 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120001 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120001 prefixEnd_120001 := by exact prefixLift 120001
  have htrace : WordTrace (prefixWord ++ tailWord_120001) baseStart_120001 baseEnd_120001 := by
    simpa [prefixWord, tailWord_120001, baseEnd_120001] using wordTrace_append hprefix tailTrace_120001
  have hstable : (prefixWord ++ tailWord_120001).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120001).length < 2 ^ (prefixWord ++ tailWord_120001).sum := by decide
  have hdescent : baseEnd_120001 < baseStart_120001 := by decide
  rcases family_descends (prefixWord ++ tailWord_120001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120039 : List Nat := [1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_120039 : Nat := 118140960795 + 120039 * 2 ^ 59
def prefixEnd_120039 : Nat := 4983230072969 + 3 ^ 40 * 120039 * 2
def baseEnd_120039 : Nat := 36526046983799158850641

theorem tailTrace_120039 : CollatzResearch.WordTrace tailWord_120039 prefixEnd_120039 36526046983799158850641 := by
  unfold tailWord_120039
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378182012126678874139171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918788008084452582759447 4378182012126678874139171)
  ·
    refine ⟨6567273018190018311208757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378182012126678874139171 6567273018190018311208757)
    ·
      refine ⟨615681845455314216675821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6567273018190018311208757 615681845455314216675821)
      ·
        refine ⟨230880692045742831253433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 615681845455314216675821 230880692045742831253433)
        ·
          refine ⟨173160519034307123440075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230880692045742831253433 173160519034307123440075)
          ·
            refine ⟨259740778551460685160113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173160519034307123440075 259740778551460685160113)
            ·
              refine ⟨194805583913595513870085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 259740778551460685160113 194805583913595513870085)
              ·
                refine ⟨36526046983799158850641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194805583913595513870085 36526046983799158850641)
                ·
                  rfl

theorem cell19_120039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_120039 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120039 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120039 prefixEnd_120039 := by exact prefixLift 120039
  have htrace : WordTrace (prefixWord ++ tailWord_120039) baseStart_120039 baseEnd_120039 := by
    simpa [prefixWord, tailWord_120039, baseEnd_120039] using wordTrace_append hprefix tailTrace_120039
  have hstable : (prefixWord ++ tailWord_120039).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120039).length < 2 ^ (prefixWord ++ tailWord_120039).sum := by decide
  have hdescent : baseEnd_120039 < baseStart_120039 := by decide
  rcases family_descends (prefixWord ++ tailWord_120039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120043 : List Nat := [1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_120043 : Nat := 118140960795 + 120043 * 2 ^ 59
def prefixEnd_120043 : Nat := 4983230072969 + 3 ^ 40 * 120043 * 2
def baseEnd_120043 : Nat := 36527264123128334761741

theorem tailTrace_120043 : CollatzResearch.WordTrace tailWord_120043 prefixEnd_120043 36527264123128334761741 := by
  unfold tailWord_120043
  simp only [CollatzResearch.WordTrace]
  refine ⟨4378327904112187557284783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2918885269408125038189855 4378327904112187557284783)
  ·
    refine ⟨6567491856168281335927175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4378327904112187557284783 6567491856168281335927175)
    ·
      refine ⟨9851237784252422003890763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6567491856168281335927175 9851237784252422003890763)
      ·
        refine ⟨14776856676378633005836145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9851237784252422003890763 14776856676378633005836145)
        ·
          refine ⟨11082642507283974754377109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14776856676378633005836145 11082642507283974754377109)
          ·
            refine ⟨519498867528936316611427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11082642507283974754377109 519498867528936316611427)
            ·
              refine ⟨779248301293404474917141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 519498867528936316611427 779248301293404474917141)
              ·
                refine ⟨36527264123128334761741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 779248301293404474917141 36527264123128334761741)
                ·
                  rfl

theorem cell19_120043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_120043 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120043 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120043 prefixEnd_120043 := by exact prefixLift 120043
  have htrace : WordTrace (prefixWord ++ tailWord_120043) baseStart_120043 baseEnd_120043 := by
    simpa [prefixWord, tailWord_120043, baseEnd_120043] using wordTrace_append hprefix tailTrace_120043
  have hstable : (prefixWord ++ tailWord_120043).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120043).length < 2 ^ (prefixWord ++ tailWord_120043).sum := by decide
  have hdescent : baseEnd_120043 < baseStart_120043 := by decide
  rcases family_descends (prefixWord ++ tailWord_120043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120096 : List Nat := [2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_120096 : Nat := 118140960795 + 120096 * 2 ^ 59
def prefixEnd_120096 : Nat := 4983230072969 + 3 ^ 40 * 120096 * 2
def baseEnd_120096 : Nat := 36543391219239915583819

theorem tailTrace_120096 : CollatzResearch.WordTrace tailWord_120096 prefixEnd_120096 36543391219239915583819 := by
  unfold tailWord_120096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2190130486460088804482071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2920173981946785072642761 2190130486460088804482071)
  ·
    refine ⟨3285195729690133206723107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2190130486460088804482071 3285195729690133206723107)
    ·
      refine ⟨4927793594535199810084661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3285195729690133206723107 4927793594535199810084661)
      ·
        refine ⟨461980649487674982195437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4927793594535199810084661 461980649487674982195437)
        ·
          refine ⟨173242743557878118323289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 461980649487674982195437 173242743557878118323289)
          ·
            refine ⟨129932057668408588742467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173242743557878118323289 129932057668408588742467)
            ·
              refine ⟨194898086502612883113701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129932057668408588742467 194898086502612883113701)
              ·
                refine ⟨36543391219239915583819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 194898086502612883113701 36543391219239915583819)
                ·
                  rfl

theorem cell19_120096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_120096 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120096 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120096 prefixEnd_120096 := by exact prefixLift 120096
  have htrace : WordTrace (prefixWord ++ tailWord_120096) baseStart_120096 baseEnd_120096 := by
    simpa [prefixWord, tailWord_120096, baseEnd_120096] using wordTrace_append hprefix tailTrace_120096
  have hstable : (prefixWord ++ tailWord_120096).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120096).length < 2 ^ (prefixWord ++ tailWord_120096).sum := by decide
  have hdescent : baseEnd_120096 < baseStart_120096 := by decide
  rcases family_descends (prefixWord ++ tailWord_120096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120170 : List Nat := [3, 1, 3, 3, 2, 2, 2, 3]
def baseStart_120170 : Nat := 118140960795 + 120170 * 2 ^ 59
def prefixEnd_120170 : Nat := 4983230072969 + 3 ^ 40 * 120170 * 2
def baseEnd_120170 : Nat := 36565908296829669939173

theorem tailTrace_120170 : CollatzResearch.WordTrace tailWord_120170 prefixEnd_120170 36565908296829669939173 := by
  unfold tailWord_120170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1095739993663022061789491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2921973316434725498105309 1095739993663022061789491)
  ·
    refine ⟨1643609990494533092684237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1095739993663022061789491 1643609990494533092684237)
    ·
      refine ⟨616353746435449909756589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1643609990494533092684237 616353746435449909756589)
      ·
        refine ⟨231132654913293716158721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 616353746435449909756589 231132654913293716158721)
        ·
          refine ⟨173349491184970287119041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231132654913293716158721 173349491184970287119041)
          ·
            refine ⟨130012118388727715339281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173349491184970287119041 130012118388727715339281)
            ·
              refine ⟨97509088791545786504461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130012118388727715339281 97509088791545786504461)
              ·
                refine ⟨36565908296829669939173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97509088791545786504461 36565908296829669939173)
                ·
                  rfl

theorem cell19_120170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_120170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120170 prefixEnd_120170 := by exact prefixLift 120170
  have htrace : WordTrace (prefixWord ++ tailWord_120170) baseStart_120170 baseEnd_120170 := by
    simpa [prefixWord, tailWord_120170, baseEnd_120170] using wordTrace_append hprefix tailTrace_120170
  have hstable : (prefixWord ++ tailWord_120170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120170).length < 2 ^ (prefixWord ++ tailWord_120170).sum := by decide
  have hdescent : baseEnd_120170 < baseStart_120170 := by decide
  rcases family_descends (prefixWord ++ tailWord_120170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120172 : List Nat := [2, 2, 1, 1, 5, 3, 2, 3]
def baseStart_120172 : Nat := 118140960795 + 120172 * 2 ^ 59
def prefixEnd_120172 : Nat := 4983230072969 + 3 ^ 40 * 120172 * 2
def baseEnd_120172 : Nat := 36566516866494257894723

theorem tailTrace_120172 : CollatzResearch.WordTrace tailWord_120172 prefixEnd_120172 36566516866494257894723 := by
  unfold tailWord_120172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191516460322421294365385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2922021947096561725820513 2191516460322421294365385)
  ·
    refine ⟨1643637345241815970774039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2191516460322421294365385 1643637345241815970774039)
    ·
      refine ⟨2465456017862723956161059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1643637345241815970774039 2465456017862723956161059)
      ·
        refine ⟨3698184026794085934241589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2465456017862723956161059 3698184026794085934241589)
        ·
          refine ⟨346704752511945556335149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3698184026794085934241589 346704752511945556335149)
          ·
            refine ⟨130014282191979583625681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346704752511945556335149 130014282191979583625681)
            ·
              refine ⟨97510711643984687719261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130014282191979583625681 97510711643984687719261)
              ·
                refine ⟨36566516866494257894723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97510711643984687719261 36566516866494257894723)
                ·
                  rfl

theorem cell19_120172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 3].length) (baseStart_120172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120172 prefixEnd_120172 := by exact prefixLift 120172
  have htrace : WordTrace (prefixWord ++ tailWord_120172) baseStart_120172 baseEnd_120172 := by
    simpa [prefixWord, tailWord_120172, baseEnd_120172] using wordTrace_append hprefix tailTrace_120172
  have hstable : (prefixWord ++ tailWord_120172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120172).length < 2 ^ (prefixWord ++ tailWord_120172).sum := by decide
  have hdescent : baseEnd_120172 < baseStart_120172 := by decide
  rcases family_descends (prefixWord ++ tailWord_120172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120176 : List Nat := [2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_120176 : Nat := 118140960795 + 120176 * 2 ^ 59
def prefixEnd_120176 : Nat := 4983230072969 + 3 ^ 40 * 120176 * 2
def baseEnd_120176 : Nat := 36567734005823433805823

theorem tailTrace_120176 : CollatzResearch.WordTrace tailWord_120176 prefixEnd_120176 36567734005823433805823 := by
  unfold tailWord_120176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2191589406315175635938191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2922119208420234181250921 2191589406315175635938191)
  ·
    refine ⟨3287384109472763453907287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2191589406315175635938191 3287384109472763453907287)
    ·
      refine ⟨4931076164209145180860931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3287384109472763453907287 4931076164209145180860931)
      ·
        refine ⟨7396614246313717771291397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4931076164209145180860931 7396614246313717771291397)
        ·
          refine ⟨1386865171183822082117137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7396614246313717771291397 1386865171183822082117137)
          ·
            refine ⟨1040148878387866561587853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1386865171183822082117137 1040148878387866561587853)
            ·
              refine ⟨390055829395449960595445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1040148878387866561587853 390055829395449960595445)
              ·
                refine ⟨36567734005823433805823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 390055829395449960595445 36567734005823433805823)
                ·
                  rfl

theorem cell19_120176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_120176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120176 prefixEnd_120176 := by exact prefixLift 120176
  have htrace : WordTrace (prefixWord ++ tailWord_120176) baseStart_120176 baseEnd_120176 := by
    simpa [prefixWord, tailWord_120176, baseEnd_120176] using wordTrace_append hprefix tailTrace_120176
  have hstable : (prefixWord ++ tailWord_120176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120176).length < 2 ^ (prefixWord ++ tailWord_120176).sum := by decide
  have hdescent : baseEnd_120176 < baseStart_120176 := by decide
  rcases family_descends (prefixWord ++ tailWord_120176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120195 : List Nat := [1, 1, 1, 3, 5, 1, 7]
def baseStart_120195 : Nat := 118140960795 + 120195 * 2 ^ 59
def prefixEnd_120195 : Nat := 4983230072969 + 3 ^ 40 * 120195 * 2
def baseEnd_120195 : Nat := 12191171805879006461183

theorem tailTrace_120195 : CollatzResearch.WordTrace tailWord_120195 prefixEnd_120195 12191171805879006461183 := by
  unfold tailWord_120195
  simp only [CollatzResearch.WordTrace]
  refine ⟨4383871799561517516818039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2922581199707678344545359 4383871799561517516818039)
  ·
    refine ⟨6575807699342276275227059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4383871799561517516818039 6575807699342276275227059)
    ·
      refine ⟨9863711549013414412840589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6575807699342276275227059 9863711549013414412840589)
      ·
        refine ⟨3698891830880030404815221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9863711549013414412840589 3698891830880030404815221)
        ·
          refine ⟨346771109145002850451427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3698891830880030404815221 346771109145002850451427)
          ·
            refine ⟨520156663717504275677141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346771109145002850451427 520156663717504275677141)
            ·
              refine ⟨12191171805879006461183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 520156663717504275677141 12191171805879006461183)
              ·
                rfl

theorem cell19_120195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_120195 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120195 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120195 prefixEnd_120195 := by exact prefixLift 120195
  have htrace : WordTrace (prefixWord ++ tailWord_120195) baseStart_120195 baseEnd_120195 := by
    simpa [prefixWord, tailWord_120195, baseEnd_120195] using wordTrace_append hprefix tailTrace_120195
  have hstable : (prefixWord ++ tailWord_120195).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120195).length < 2 ^ (prefixWord ++ tailWord_120195).sum := by decide
  have hdescent : baseEnd_120195 < baseStart_120195 := by decide
  rcases family_descends (prefixWord ++ tailWord_120195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120212 : List Nat := [2, 4, 2, 1, 2, 1, 1, 6]
def baseStart_120212 : Nat := 118140960795 + 120212 * 2 ^ 59
def prefixEnd_120212 : Nat := 4983230072969 + 3 ^ 40 * 120212 * 2
def baseEnd_120212 : Nat := 36578688259786017005725

theorem tailTrace_120212 : CollatzResearch.WordTrace tailWord_120212 prefixEnd_120212 36578688259786017005725 := by
  unfold tailWord_120212
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192245920249964710093445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2922994560333286280124593 2192245920249964710093445)
  ·
    refine ⟨411046110046868383142521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2192245920249964710093445 411046110046868383142521)
    ·
      refine ⟨308284582535151287356891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 411046110046868383142521 308284582535151287356891)
      ·
        refine ⟨462426873802726931035337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308284582535151287356891 462426873802726931035337)
        ·
          refine ⟨346820155352045198276503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 462426873802726931035337 346820155352045198276503)
          ·
            refine ⟨520230233028067797414755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 346820155352045198276503 520230233028067797414755)
            ·
              refine ⟨780345349542101696122133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 520230233028067797414755 780345349542101696122133)
              ·
                refine ⟨36578688259786017005725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 780345349542101696122133 36578688259786017005725)
                ·
                  rfl

theorem cell19_120212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_120212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120212 prefixEnd_120212 := by exact prefixLift 120212
  have htrace : WordTrace (prefixWord ++ tailWord_120212) baseStart_120212 baseEnd_120212 := by
    simpa [prefixWord, tailWord_120212, baseEnd_120212] using wordTrace_append hprefix tailTrace_120212
  have hstable : (prefixWord ++ tailWord_120212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120212).length < 2 ^ (prefixWord ++ tailWord_120212).sum := by decide
  have hdescent : baseEnd_120212 < baseStart_120212 := by decide
  rcases family_descends (prefixWord ++ tailWord_120212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120252 : List Nat := [2, 2, 2, 4, 9]
def baseStart_120252 : Nat := 118140960795 + 120252 * 2 ^ 59
def prefixEnd_120252 : Nat := 4983230072969 + 3 ^ 40 * 120252 * 2
def baseEnd_120252 : Nat := 1355217024188065782101

theorem tailTrace_120252 : CollatzResearch.WordTrace tailWord_120252 prefixEnd_120252 1355217024188065782101 := by
  unfold tailWord_120252
  simp only [CollatzResearch.WordTrace]
  refine ⟨2192975380177508125821505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2923967173570010834428673 2192975380177508125821505)
  ·
    refine ⟨1644731535133131094366129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2192975380177508125821505 1644731535133131094366129)
    ·
      refine ⟨1233548651349848320774597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1644731535133131094366129 1233548651349848320774597)
      ·
        refine ⟨231290372128096560145237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1233548651349848320774597 231290372128096560145237)
        ·
          refine ⟨1355217024188065782101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 231290372128096560145237 1355217024188065782101)
          ·
            rfl

theorem cell19_120252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 9].length) (baseStart_120252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120252 prefixEnd_120252 := by exact prefixLift 120252
  have htrace : WordTrace (prefixWord ++ tailWord_120252) baseStart_120252 baseEnd_120252 := by
    simpa [prefixWord, tailWord_120252, baseEnd_120252] using wordTrace_append hprefix tailTrace_120252
  have hstable : (prefixWord ++ tailWord_120252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120252).length < 2 ^ (prefixWord ++ tailWord_120252).sum := by decide
  have hdescent : baseEnd_120252 < baseStart_120252 := by decide
  rcases family_descends (prefixWord ++ tailWord_120252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120271 : List Nat := [1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_120271 : Nat := 118140960795 + 120271 * 2 ^ 59
def prefixEnd_120271 : Nat := 4983230072969 + 3 ^ 40 * 120271 * 2
def baseEnd_120271 : Nat := 36596641064891361694453

theorem tailTrace_120271 : CollatzResearch.WordTrace tailWord_120271 prefixEnd_120271 36596641064891361694453 := by
  unfold tailWord_120271
  simp only [CollatzResearch.WordTrace]
  refine ⟨4386643747286182496584667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2924429164857454997723111 4386643747286182496584667)
  ·
    refine ⟨6579965620929273744877001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4386643747286182496584667 6579965620929273744877001)
    ·
      refine ⟨4934974215696955308657751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6579965620929273744877001 4934974215696955308657751)
      ·
        refine ⟨7402461323545432962986627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934974215696955308657751 7402461323545432962986627)
        ·
          refine ⟨11103691985318149444479941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402461323545432962986627 11103691985318149444479941)
          ·
            refine ⟨2081942247247153020839989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11103691985318149444479941 2081942247247153020839989)
            ·
              refine ⟨195182085679420595703749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2081942247247153020839989 195182085679420595703749)
              ·
                refine ⟨36596641064891361694453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195182085679420595703749 36596641064891361694453)
                ·
                  rfl

theorem cell19_120271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_120271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120271 prefixEnd_120271 := by exact prefixLift 120271
  have htrace : WordTrace (prefixWord ++ tailWord_120271) baseStart_120271 baseEnd_120271 := by
    simpa [prefixWord, tailWord_120271, baseEnd_120271] using wordTrace_append hprefix tailTrace_120271
  have hstable : (prefixWord ++ tailWord_120271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120271).length < 2 ^ (prefixWord ++ tailWord_120271).sum := by decide
  have hdescent : baseEnd_120271 < baseStart_120271 := by decide
  rcases family_descends (prefixWord ++ tailWord_120271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120404 : List Nat := [2, 4, 1, 1, 1, 2, 1, 7]
def baseStart_120404 : Nat := 118140960795 + 120404 * 2 ^ 59
def prefixEnd_120404 : Nat := 4983230072969 + 3 ^ 40 * 120404 * 2
def baseEnd_120404 : Nat := 36637110947586460738535

theorem tailTrace_120404 : CollatzResearch.WordTrace tailWord_120404 prefixEnd_120404 36637110947586460738535 := by
  unfold tailWord_120404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2195747327902173105588133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2927663103869564140784177 2195747327902173105588133)
  ·
    refine ⟨411702623981657457297775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2195747327902173105588133 411702623981657457297775)
    ·
      refine ⟨617553935972486185946663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411702623981657457297775 617553935972486185946663)
      ·
        refine ⟨926330903958729278919995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 617553935972486185946663 926330903958729278919995)
        ·
          refine ⟨1389496355938093918379993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 926330903958729278919995 1389496355938093918379993)
          ·
            refine ⟨1042122266953570438784995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1389496355938093918379993 1042122266953570438784995)
            ·
              refine ⟨1563183400430355658177493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1042122266953570438784995 1563183400430355658177493)
              ·
                refine ⟨36637110947586460738535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1563183400430355658177493 36637110947586460738535)
                ·
                  rfl

theorem cell19_120404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_120404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120404 prefixEnd_120404 := by exact prefixLift 120404
  have htrace : WordTrace (prefixWord ++ tailWord_120404) baseStart_120404 baseEnd_120404 := by
    simpa [prefixWord, tailWord_120404, baseEnd_120404] using wordTrace_append hprefix tailTrace_120404
  have hstable : (prefixWord ++ tailWord_120404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120404).length < 2 ^ (prefixWord ++ tailWord_120404).sum := by decide
  have hdescent : baseEnd_120404 < baseStart_120404 := by decide
  rcases family_descends (prefixWord ++ tailWord_120404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120438 : List Nat := [5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_120438 : Nat := 118140960795 + 120438 * 2 ^ 59
def prefixEnd_120438 : Nat := 4983230072969 + 3 ^ 40 * 120438 * 2
def baseEnd_120438 : Nat := 36647456631884455982887

theorem tailTrace_120438 : CollatzResearch.WordTrace tailWord_120438 prefixEnd_120438 36647456631884455982887 := by
  unfold tailWord_120438
  simp only [CollatzResearch.WordTrace]
  refine ⟨274545921105073126119623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2928489825120780011942645 274545921105073126119623)
  ·
    refine ⟨411818881657609689179435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 274545921105073126119623 411818881657609689179435)
    ·
      refine ⟨617728322486414533769153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 411818881657609689179435 617728322486414533769153)
      ·
        refine ⟨463296241864810900326865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 617728322486414533769153 463296241864810900326865)
        ·
          refine ⟨347472181398608175245149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 463296241864810900326865 347472181398608175245149)
          ·
            refine ⟨130302068024478065716931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347472181398608175245149 130302068024478065716931)
            ·
              refine ⟨195453102036717098575397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130302068024478065716931 195453102036717098575397)
              ·
                refine ⟨36647456631884455982887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195453102036717098575397 36647456631884455982887)
                ·
                  rfl

theorem cell19_120438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_120438 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120438 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120438 prefixEnd_120438 := by exact prefixLift 120438
  have htrace : WordTrace (prefixWord ++ tailWord_120438) baseStart_120438 baseEnd_120438 := by
    simpa [prefixWord, tailWord_120438, baseEnd_120438] using wordTrace_append hprefix tailTrace_120438
  have hstable : (prefixWord ++ tailWord_120438).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120438).length < 2 ^ (prefixWord ++ tailWord_120438).sum := by decide
  have hdescent : baseEnd_120438 < baseStart_120438 := by decide
  rcases family_descends (prefixWord ++ tailWord_120438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120478 : List Nat := [4, 3, 1, 1, 1, 3, 6]
def baseStart_120478 : Nat := 118140960795 + 120478 * 2 ^ 59
def prefixEnd_120478 : Nat := 4983230072969 + 3 ^ 40 * 120478 * 2
def baseEnd_120478 : Nat := 12219876008392071697963

theorem tailTrace_120478 : CollatzResearch.WordTrace tailWord_120478 prefixEnd_120478 12219876008392071697963 := by
  unfold tailWord_120478
  simp only [CollatzResearch.WordTrace]
  refine ⟨549274207192032106171261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2929462438357504566246725 549274207192032106171261)
  ·
    refine ⟨205977827697012039814223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 549274207192032106171261 205977827697012039814223)
    ·
      refine ⟨308966741545518059721335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205977827697012039814223 308966741545518059721335)
      ·
        refine ⟨463450112318277089582003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308966741545518059721335 463450112318277089582003)
        ·
          refine ⟨695175168477415634373005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463450112318277089582003 695175168477415634373005)
          ·
            refine ⟨260690688179030862889877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 695175168477415634373005 260690688179030862889877)
            ·
              refine ⟨12219876008392071697963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260690688179030862889877 12219876008392071697963)
              ·
                rfl

theorem cell19_120478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 6].length) (baseStart_120478 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120478 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120478 prefixEnd_120478 := by exact prefixLift 120478
  have htrace : WordTrace (prefixWord ++ tailWord_120478) baseStart_120478 baseEnd_120478 := by
    simpa [prefixWord, tailWord_120478, baseEnd_120478] using wordTrace_append hprefix tailTrace_120478
  have hstable : (prefixWord ++ tailWord_120478).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120478).length < 2 ^ (prefixWord ++ tailWord_120478).sum := by decide
  have hdescent : baseEnd_120478 < baseStart_120478 := by decide
  rcases family_descends (prefixWord ++ tailWord_120478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120480 : List Nat := [2, 1, 1, 4, 3, 2, 6]
def baseStart_120480 : Nat := 118140960795 + 120480 * 2 ^ 59
def prefixEnd_120480 : Nat := 4983230072969 + 3 ^ 40 * 120480 * 2
def baseEnd_120480 : Nat := 12220078864946934349813

theorem tailTrace_120480 : CollatzResearch.WordTrace tailWord_120480 prefixEnd_120480 12220078864946934349813 := by
  unfold tailWord_120480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2197133301764505595471447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2929511069019340793961929 2197133301764505595471447)
  ·
    refine ⟨3295699952646758393207171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2197133301764505595471447 3295699952646758393207171)
    ·
      refine ⟨4943549928970137589810757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3295699952646758393207171 4943549928970137589810757)
      ·
        refine ⟨926915611681900798089517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4943549928970137589810757 926915611681900798089517)
        ·
          refine ⟨347593354380712799283569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 926915611681900798089517 347593354380712799283569)
          ·
            refine ⟨260695015785534599462677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347593354380712799283569 260695015785534599462677)
            ·
              refine ⟨12220078864946934349813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260695015785534599462677 12220078864946934349813)
              ·
                rfl

theorem cell19_120480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 6].length) (baseStart_120480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120480 prefixEnd_120480 := by exact prefixLift 120480
  have htrace : WordTrace (prefixWord ++ tailWord_120480) baseStart_120480 baseEnd_120480 := by
    simpa [prefixWord, tailWord_120480, baseEnd_120480] using wordTrace_append hprefix tailTrace_120480
  have hstable : (prefixWord ++ tailWord_120480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120480).length < 2 ^ (prefixWord ++ tailWord_120480).sum := by decide
  have hdescent : baseEnd_120480 < baseStart_120480 := by decide
  rcases family_descends (prefixWord ++ tailWord_120480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120537 : List Nat := [1, 2, 1, 2, 3, 5, 5]
def baseStart_120537 : Nat := 118140960795 + 120537 * 2 ^ 59
def prefixEnd_120537 : Nat := 4983230072969 + 3 ^ 40 * 120537 * 2
def baseEnd_120537 : Nat := 12225860276760519927539

theorem tailTrace_120537 : CollatzResearch.WordTrace tailWord_120537 prefixEnd_120537 12225860276760519927539 := by
  unfold tailWord_120537
  simp only [CollatzResearch.WordTrace]
  refine ⟨4396345564322509925767865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2930897042881673283845243 4396345564322509925767865)
  ·
    refine ⟨3297259173241882444325899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4396345564322509925767865 3297259173241882444325899)
    ·
      refine ⟨4945888759862823666488849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3297259173241882444325899 4945888759862823666488849)
      ·
        refine ⟨3709416569897117749866637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4945888759862823666488849 3709416569897117749866637)
        ·
          refine ⟨1391031213711419156199989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3709416569897117749866637 1391031213711419156199989)
          ·
            refine ⟨130409176285445545893749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1391031213711419156199989 130409176285445545893749)
            ·
              refine ⟨12225860276760519927539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130409176285445545893749 12225860276760519927539)
              ·
                rfl

theorem cell19_120537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_120537 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120537 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120537 prefixEnd_120537 := by exact prefixLift 120537
  have htrace : WordTrace (prefixWord ++ tailWord_120537) baseStart_120537 baseEnd_120537 := by
    simpa [prefixWord, tailWord_120537, baseEnd_120537] using wordTrace_append hprefix tailTrace_120537
  have hstable : (prefixWord ++ tailWord_120537).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120537).length < 2 ^ (prefixWord ++ tailWord_120537).sum := by decide
  have hdescent : baseEnd_120537 < baseStart_120537 := by decide
  rcases family_descends (prefixWord ++ tailWord_120537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120613 : List Nat := [1, 3, 1, 2, 3, 2, 3, 4]
def baseStart_120613 : Nat := 118140960795 + 120613 * 2 ^ 59
def prefixEnd_120613 : Nat := 4983230072969 + 3 ^ 40 * 120613 * 2
def baseEnd_120613 : Nat := 36700706477535902093521

theorem tailTrace_120613 : CollatzResearch.WordTrace tailWord_120613 prefixEnd_120613 36700706477535902093521 := by
  unfold tailWord_120613
  simp only [CollatzResearch.WordTrace]
  refine ⟨4399117512047174905534493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2932745008031449937022995 4399117512047174905534493)
  ·
    refine ⟨1649669067017690589575435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4399117512047174905534493 1649669067017690589575435)
    ·
      refine ⟨2474503600526535884363153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1649669067017690589575435 2474503600526535884363153)
      ·
        refine ⟨1855877700394901913272365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2474503600526535884363153 1855877700394901913272365)
        ·
          refine ⟨695954137648088217477137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1855877700394901913272365 695954137648088217477137)
          ·
            refine ⟨521965603236066163107853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 695954137648088217477137 521965603236066163107853)
            ·
              refine ⟨195737101213524811165445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 521965603236066163107853 195737101213524811165445)
              ·
                refine ⟨36700706477535902093521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195737101213524811165445 36700706477535902093521)
                ·
                  rfl

theorem cell19_120613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 4].length) (baseStart_120613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120613 prefixEnd_120613 := by exact prefixLift 120613
  have htrace : WordTrace (prefixWord ++ tailWord_120613) baseStart_120613 baseEnd_120613 := by
    simpa [prefixWord, tailWord_120613, baseEnd_120613] using wordTrace_append hprefix tailTrace_120613
  have hstable : (prefixWord ++ tailWord_120613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120613).length < 2 ^ (prefixWord ++ tailWord_120613).sum := by decide
  have hdescent : baseEnd_120613 < baseStart_120613 := by decide
  rcases family_descends (prefixWord ++ tailWord_120613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120628 : List Nat := [2, 5, 1, 1, 2, 2, 3, 3]
def baseStart_120628 : Nat := 118140960795 + 120628 * 2 ^ 59
def prefixEnd_120628 : Nat := 4983230072969 + 3 ^ 40 * 120628 * 2
def baseEnd_120628 : Nat := 36705270750020311760147

theorem tailTrace_120628 : CollatzResearch.WordTrace tailWord_120628 prefixEnd_120628 36705270750020311760147 := by
  unfold tailWord_120628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2199832303496416233665269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2933109737995221644887025 2199832303496416233665269)
  ·
    refine ⟨206234278452789021906119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2199832303496416233665269 206234278452789021906119)
    ·
      refine ⟨309351417679183532859179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206234278452789021906119 309351417679183532859179)
      ·
        refine ⟨464027126518775299288769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309351417679183532859179 464027126518775299288769)
        ·
          refine ⟨348020344889081474466577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 464027126518775299288769 348020344889081474466577)
          ·
            refine ⟨261015258666811105849933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348020344889081474466577 261015258666811105849933)
            ·
              refine ⟨97880722000054164693725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 261015258666811105849933 97880722000054164693725)
              ·
                refine ⟨36705270750020311760147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97880722000054164693725 36705270750020311760147)
                ·
                  rfl

theorem cell19_120628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 3].length) (baseStart_120628 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120628 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120628 prefixEnd_120628 := by exact prefixLift 120628
  have htrace : WordTrace (prefixWord ++ tailWord_120628) baseStart_120628 baseEnd_120628 := by
    simpa [prefixWord, tailWord_120628, baseEnd_120628] using wordTrace_append hprefix tailTrace_120628
  have hstable : (prefixWord ++ tailWord_120628).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120628).length < 2 ^ (prefixWord ++ tailWord_120628).sum := by decide
  have hdescent : baseEnd_120628 < baseStart_120628 := by decide
  rcases family_descends (prefixWord ++ tailWord_120628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120727 : List Nat := [1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_120727 : Nat := 118140960795 + 120727 * 2 ^ 59
def prefixEnd_120727 : Nat := 4983230072969 + 3 ^ 40 * 120727 * 2
def baseEnd_120727 : Nat := 36735394948417415559877

theorem tailTrace_120727 : CollatzResearch.WordTrace tailWord_120727 prefixEnd_120727 36735394948417415559877 := by
  unfold tailWord_120727
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403275433634172375184435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2935516955756114916789623 4403275433634172375184435)
  ·
    refine ⟨6604913150451258562776653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4403275433634172375184435 6604913150451258562776653)
    ·
      refine ⟨2476842431419221961041245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6604913150451258562776653 2476842431419221961041245)
      ·
        refine ⟨928815911782208235390467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2476842431419221961041245 928815911782208235390467)
        ·
          refine ⟨1393223867673312353085701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 928815911782208235390467 1393223867673312353085701)
          ·
            refine ⟨261229475188746066203569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1393223867673312353085701 261229475188746066203569)
            ·
              refine ⟨195922106391559549652677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261229475188746066203569 195922106391559549652677)
              ·
                refine ⟨36735394948417415559877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195922106391559549652677 36735394948417415559877)
                ·
                  rfl

theorem cell19_120727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_120727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120727 prefixEnd_120727 := by exact prefixLift 120727
  have htrace : WordTrace (prefixWord ++ tailWord_120727) baseStart_120727 baseEnd_120727 := by
    simpa [prefixWord, tailWord_120727, baseEnd_120727] using wordTrace_append hprefix tailTrace_120727
  have hstable : (prefixWord ++ tailWord_120727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120727).length < 2 ^ (prefixWord ++ tailWord_120727).sum := by decide
  have hdescent : baseEnd_120727 < baseStart_120727 := by decide
  rcases family_descends (prefixWord ++ tailWord_120727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120729 : List Nat := [1, 2, 1, 2, 1, 3, 3, 6]
def baseStart_120729 : Nat := 118140960795 + 120729 * 2 ^ 59
def prefixEnd_120729 : Nat := 4983230072969 + 3 ^ 40 * 120729 * 2
def baseEnd_120729 : Nat := 36736003518082003515427

theorem tailTrace_120729 : CollatzResearch.WordTrace tailWord_120729 prefixEnd_120729 36736003518082003515427 := by
  unfold tailWord_120729
  simp only [CollatzResearch.WordTrace]
  refine ⟨4403348379626926716757241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2935565586417951144504827 4403348379626926716757241)
  ·
    refine ⟨3302511284720195037567931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4403348379626926716757241 3302511284720195037567931)
    ·
      refine ⟨4953766927080292556351897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3302511284720195037567931 4953766927080292556351897)
      ·
        refine ⟨3715325195310219417263923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4953766927080292556351897 3715325195310219417263923)
        ·
          refine ⟨5572987792965329125895885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3715325195310219417263923 5572987792965329125895885)
          ·
            refine ⟨2089870422361998422210957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5572987792965329125895885 2089870422361998422210957)
            ·
              refine ⟨783701408385749408329109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2089870422361998422210957 783701408385749408329109)
              ·
                refine ⟨36736003518082003515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 783701408385749408329109 36736003518082003515427)
                ·
                  rfl

theorem cell19_120729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_120729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120729 prefixEnd_120729 := by exact prefixLift 120729
  have htrace : WordTrace (prefixWord ++ tailWord_120729) baseStart_120729 baseEnd_120729 := by
    simpa [prefixWord, tailWord_120729, baseEnd_120729] using wordTrace_append hprefix tailTrace_120729
  have hstable : (prefixWord ++ tailWord_120729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120729).length < 2 ^ (prefixWord ++ tailWord_120729).sum := by decide
  have hdescent : baseEnd_120729 < baseStart_120729 := by decide
  rcases family_descends (prefixWord ++ tailWord_120729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120843 : List Nat := [1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_120843 : Nat := 118140960795 + 120843 * 2 ^ 59
def prefixEnd_120843 : Nat := 4983230072969 + 3 ^ 40 * 120843 * 2
def baseEnd_120843 : Nat := 36770691988963516981783

theorem tailTrace_120843 : CollatzResearch.WordTrace tailWord_120843 prefixEnd_120843 36770691988963516981783 := by
  unfold tailWord_120843
  simp only [CollatzResearch.WordTrace]
  refine ⟨4407506301213924186407183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2938337534142616124271455 4407506301213924186407183)
  ·
    refine ⟨6611259451820886279610775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4407506301213924186407183 6611259451820886279610775)
    ·
      refine ⟨9916889177731329419416163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6611259451820886279610775 9916889177731329419416163)
      ·
        refine ⟨14875333766596994129124245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9916889177731329419416163 14875333766596994129124245)
        ·
          refine ⟨697281270309234099802699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14875333766596994129124245 697281270309234099802699)
          ·
            refine ⟨1045921905463851149704049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 697281270309234099802699 1045921905463851149704049)
            ·
              refine ⟨784441429097888362278037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1045921905463851149704049 784441429097888362278037)
              ·
                refine ⟨36770691988963516981783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 784441429097888362278037 36770691988963516981783)
                ·
                  rfl

theorem cell19_120843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_120843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120843 prefixEnd_120843 := by exact prefixLift 120843
  have htrace : WordTrace (prefixWord ++ tailWord_120843) baseStart_120843 baseEnd_120843 := by
    simpa [prefixWord, tailWord_120843, baseEnd_120843] using wordTrace_append hprefix tailTrace_120843
  have hstable : (prefixWord ++ tailWord_120843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120843).length < 2 ^ (prefixWord ++ tailWord_120843).sum := by decide
  have hdescent : baseEnd_120843 < baseStart_120843 := by decide
  rcases family_descends (prefixWord ++ tailWord_120843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120852 : List Nat := [2, 4, 3, 2, 2, 1, 2, 3]
def baseStart_120852 : Nat := 118140960795 + 120852 * 2 ^ 59
def prefixEnd_120852 : Nat := 4983230072969 + 3 ^ 40 * 120852 * 2
def baseEnd_120852 : Nat := 36773430552454162781759

theorem tailTrace_120852 : CollatzResearch.WordTrace tailWord_120852 prefixEnd_120852 36773430552454162781759 := by
  unfold tailWord_120852
  simp only [CollatzResearch.WordTrace]
  refine ⟨2203917279090659361742405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2938556372120879148989873 2203917279090659361742405)
  ·
    refine ⟨413234489829498630326701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2203917279090659361742405 413234489829498630326701)
    ·
      refine ⟨154962933686061986372513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 413234489829498630326701 154962933686061986372513)
      ·
        refine ⟨116222200264546489779385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154962933686061986372513 116222200264546489779385)
        ·
          refine ⟨87166650198409867334539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116222200264546489779385 87166650198409867334539)
          ·
            refine ⟨130749975297614801001809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87166650198409867334539 130749975297614801001809)
            ·
              refine ⟨98062481473211100751357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130749975297614801001809 98062481473211100751357)
              ·
                refine ⟨36773430552454162781759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98062481473211100751357 36773430552454162781759)
                ·
                  rfl

theorem cell19_120852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 3].length) (baseStart_120852 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120852 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120852 prefixEnd_120852 := by exact prefixLift 120852
  have htrace : WordTrace (prefixWord ++ tailWord_120852) baseStart_120852 baseEnd_120852 := by
    simpa [prefixWord, tailWord_120852, baseEnd_120852] using wordTrace_append hprefix tailTrace_120852
  have hstable : (prefixWord ++ tailWord_120852).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120852).length < 2 ^ (prefixWord ++ tailWord_120852).sum := by decide
  have hdescent : baseEnd_120852 < baseStart_120852 := by decide
  rcases family_descends (prefixWord ++ tailWord_120852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120858 : List Nat := [3, 1, 1, 3, 1, 5, 2, 3]
def baseStart_120858 : Nat := 118140960795 + 120858 * 2 ^ 59
def prefixEnd_120858 : Nat := 4983230072969 + 3 ^ 40 * 120858 * 2
def baseEnd_120858 : Nat := 36775256261447926648409

theorem tailTrace_120858 : CollatzResearch.WordTrace tailWord_120858 prefixEnd_120858 36775256261447926648409 := by
  unfold tailWord_120858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102013349039895437050807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2938702264106387832135485 1102013349039895437050807)
  ·
    refine ⟨1653020023559843155576211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102013349039895437050807 1653020023559843155576211)
    ·
      refine ⟨2479530035339764733364317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1653020023559843155576211 2479530035339764733364317)
      ·
        refine ⟨929823763252411775011619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2479530035339764733364317 929823763252411775011619)
        ·
          refine ⟨1394735644878617662517429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 929823763252411775011619 1394735644878617662517429)
          ·
            refine ⟨130756466707370405861009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1394735644878617662517429 130756466707370405861009)
            ·
              refine ⟨98067350030527804395757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130756466707370405861009 98067350030527804395757)
              ·
                refine ⟨36775256261447926648409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98067350030527804395757 36775256261447926648409)
                ·
                  rfl

theorem cell19_120858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_120858 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120858 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120858 prefixEnd_120858 := by exact prefixLift 120858
  have htrace : WordTrace (prefixWord ++ tailWord_120858) baseStart_120858 baseEnd_120858 := by
    simpa [prefixWord, tailWord_120858, baseEnd_120858] using wordTrace_append hprefix tailTrace_120858
  have hstable : (prefixWord ++ tailWord_120858).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120858).length < 2 ^ (prefixWord ++ tailWord_120858).sum := by decide
  have hdescent : baseEnd_120858 < baseStart_120858 := by decide
  rcases family_descends (prefixWord ++ tailWord_120858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120860 : List Nat := [2, 2, 3, 1, 3, 2, 1, 5]
def baseStart_120860 : Nat := 118140960795 + 120860 * 2 ^ 59
def prefixEnd_120860 : Nat := 4983230072969 + 3 ^ 40 * 120860 * 2
def baseEnd_120860 : Nat := 36775864831112514603959

theorem tailTrace_120860 : CollatzResearch.WordTrace tailWord_120860 prefixEnd_120860 36775864831112514603959 := by
  unfold tailWord_120860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2204063171076168044888017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2938750894768224059850689 2204063171076168044888017)
  ·
    refine ⟨1653047378307126033666013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2204063171076168044888017 1653047378307126033666013)
    ·
      refine ⟨619892766865172262624755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1653047378307126033666013 619892766865172262624755)
      ·
        refine ⟨929839150297758393937133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 619892766865172262624755 929839150297758393937133)
        ·
          refine ⟨348689681361659397726425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 929839150297758393937133 348689681361659397726425)
          ·
            refine ⟨261517261021244548294819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 348689681361659397726425 261517261021244548294819)
            ·
              refine ⟨392275891531866822442229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 261517261021244548294819 392275891531866822442229)
              ·
                refine ⟨36775864831112514603959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392275891531866822442229 36775864831112514603959)
                ·
                  rfl

theorem cell19_120860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_120860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120860 prefixEnd_120860 := by exact prefixLift 120860
  have htrace : WordTrace (prefixWord ++ tailWord_120860) baseStart_120860 baseEnd_120860 := by
    simpa [prefixWord, tailWord_120860, baseEnd_120860] using wordTrace_append hprefix tailTrace_120860
  have hstable : (prefixWord ++ tailWord_120860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120860).length < 2 ^ (prefixWord ++ tailWord_120860).sum := by decide
  have hdescent : baseEnd_120860 < baseStart_120860 := by decide
  rcases family_descends (prefixWord ++ tailWord_120860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120881 : List Nat := [1, 2, 2, 3, 1, 3, 7]
def baseStart_120881 : Nat := 118140960795 + 120881 * 2 ^ 59
def prefixEnd_120881 : Nat := 4983230072969 + 3 ^ 40 * 120881 * 2
def baseEnd_120881 : Nat := 12260751604196896045745

theorem tailTrace_120881 : CollatzResearch.WordTrace tailWord_120881 prefixEnd_120881 12260751604196896045745 := by
  unfold tailWord_120881
  simp only [CollatzResearch.WordTrace]
  refine ⟨4408892275076256676290497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2939261516717504450860331 4408892275076256676290497)
  ·
    refine ⟨3306669206307192507217873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4408892275076256676290497 3306669206307192507217873)
    ·
      refine ⟨2480001904730394380413405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3306669206307192507217873 2480001904730394380413405)
      ·
        refine ⟨930000714273897892655027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2480001904730394380413405 930000714273897892655027)
        ·
          refine ⟨1395001071410846838982541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 930000714273897892655027 1395001071410846838982541)
          ·
            refine ⟨523125401779067564618453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1395001071410846838982541 523125401779067564618453)
            ·
              refine ⟨12260751604196896045745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 523125401779067564618453 12260751604196896045745)
              ·
                rfl

theorem cell19_120881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 7].length) (baseStart_120881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120881 prefixEnd_120881 := by exact prefixLift 120881
  have htrace : WordTrace (prefixWord ++ tailWord_120881) baseStart_120881 baseEnd_120881 := by
    simpa [prefixWord, tailWord_120881, baseEnd_120881] using wordTrace_append hprefix tailTrace_120881
  have hstable : (prefixWord ++ tailWord_120881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120881).length < 2 ^ (prefixWord ++ tailWord_120881).sum := by decide
  have hdescent : baseEnd_120881 < baseStart_120881 := by decide
  rcases family_descends (prefixWord ++ tailWord_120881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120919 : List Nat := [1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_120919 : Nat := 118140960795 + 120919 * 2 ^ 59
def prefixEnd_120919 : Nat := 4983230072969 + 3 ^ 40 * 120919 * 2
def baseEnd_120919 : Nat := 36793817636217859292687

theorem tailTrace_120919 : CollatzResearch.WordTrace tailWord_120919 prefixEnd_120919 36793817636217859292687 := by
  unfold tailWord_120919
  simp only [CollatzResearch.WordTrace]
  refine ⟨4410278248938589166173811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2940185499292392777449207 4410278248938589166173811)
  ·
    refine ⟨6615417373407883749260717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4410278248938589166173811 6615417373407883749260717)
    ·
      refine ⟨2480781515027956405972769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6615417373407883749260717 2480781515027956405972769)
      ·
        refine ⟨1860586136270967304479577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2480781515027956405972769 1860586136270967304479577)
        ·
          refine ⟨1395439602203225478359683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1860586136270967304479577 1395439602203225478359683)
          ·
            refine ⟨2093159403304838217539525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1395439602203225478359683 2093159403304838217539525)
            ·
              refine ⟨392467388119657165788661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2093159403304838217539525 392467388119657165788661)
              ·
                refine ⟨36793817636217859292687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 392467388119657165788661 36793817636217859292687)
                ·
                  rfl

theorem cell19_120919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_120919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120919 prefixEnd_120919 := by exact prefixLift 120919
  have htrace : WordTrace (prefixWord ++ tailWord_120919) baseStart_120919 baseEnd_120919 := by
    simpa [prefixWord, tailWord_120919, baseEnd_120919] using wordTrace_append hprefix tailTrace_120919
  have hstable : (prefixWord ++ tailWord_120919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120919).length < 2 ^ (prefixWord ++ tailWord_120919).sum := by decide
  have hdescent : baseEnd_120919 < baseStart_120919 := by decide
  rcases family_descends (prefixWord ++ tailWord_120919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_120938 : List Nat := [3, 1, 3, 2, 10]
def baseStart_120938 : Nat := 118140960795 + 120938 * 2 ^ 59
def prefixEnd_120938 : Nat := 4983230072969 + 3 ^ 40 * 120938 * 2
def baseEnd_120938 : Nat := 1362948112890053513719

theorem tailTrace_120938 : CollatzResearch.WordTrace tailWord_120938 prefixEnd_120938 1362948112890053513719 := by
  unfold tailWord_120938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1102742808967438852778867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2940647490579836940743645 1102742808967438852778867)
  ·
    refine ⟨1654114213451158279168301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1102742808967438852778867 1654114213451158279168301)
    ·
      refine ⟨620292830044184354688113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1654114213451158279168301 620292830044184354688113)
      ·
        refine ⟨465219622533138266016085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 620292830044184354688113 465219622533138266016085)
        ·
          refine ⟨1362948112890053513719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 465219622533138266016085 1362948112890053513719)
          ·
            rfl

theorem cell19_120938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 10].length) (baseStart_120938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_120938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_120938 prefixEnd_120938 := by exact prefixLift 120938
  have htrace : WordTrace (prefixWord ++ tailWord_120938) baseStart_120938 baseEnd_120938 := by
    simpa [prefixWord, tailWord_120938, baseEnd_120938] using wordTrace_append hprefix tailTrace_120938
  have hstable : (prefixWord ++ tailWord_120938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_120938).length < 2 ^ (prefixWord ++ tailWord_120938).sum := by decide
  have hdescent : baseEnd_120938 < baseStart_120938 := by decide
  rcases family_descends (prefixWord ++ tailWord_120938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121025 : List Nat := [1, 2, 6, 1, 3, 1, 2, 3]
def baseStart_121025 : Nat := 118140960795 + 121025 * 2 ^ 59
def prefixEnd_121025 : Nat := 4983230072969 + 3 ^ 40 * 121025 * 2
def baseEnd_121025 : Nat := 36826071828441020936843

theorem tailTrace_121025 : CollatzResearch.WordTrace tailWord_121025 prefixEnd_121025 36826071828441020936843 := by
  unfold tailWord_121025
  simp only [CollatzResearch.WordTrace]
  refine ⟨4414144386554569269532529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2942762924369712846355019 4414144386554569269532529)
  ·
    refine ⟨3310608289915926952149397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4414144386554569269532529 3310608289915926952149397)
    ·
      refine ⟨155184763589809075882003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3310608289915926952149397 155184763589809075882003)
      ·
        refine ⟨232777145384713613823005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 155184763589809075882003 232777145384713613823005)
        ·
          refine ⟨87291429519267605183627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232777145384713613823005 87291429519267605183627)
          ·
            refine ⟨130937144278901407775441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87291429519267605183627 130937144278901407775441)
            ·
              refine ⟨98202858209176055831581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130937144278901407775441 98202858209176055831581)
              ·
                refine ⟨36826071828441020936843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98202858209176055831581 36826071828441020936843)
                ·
                  rfl

theorem cell19_121025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 3].length) (baseStart_121025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121025 prefixEnd_121025 := by exact prefixLift 121025
  have htrace : WordTrace (prefixWord ++ tailWord_121025) baseStart_121025 baseEnd_121025 := by
    simpa [prefixWord, tailWord_121025, baseEnd_121025] using wordTrace_append hprefix tailTrace_121025
  have hstable : (prefixWord ++ tailWord_121025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121025).length < 2 ^ (prefixWord ++ tailWord_121025).sum := by decide
  have hdescent : baseEnd_121025 < baseStart_121025 := by decide
  rcases family_descends (prefixWord ++ tailWord_121025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121071 : List Nat := [1, 1, 2, 1, 6, 1, 1, 6]
def baseStart_121071 : Nat := 118140960795 + 121071 * 2 ^ 59
def prefixEnd_121071 : Nat := 4983230072969 + 3 ^ 40 * 121071 * 2
def baseEnd_121071 : Nat := 36840068930726543914495

theorem tailTrace_121071 : CollatzResearch.WordTrace tailWord_121071 prefixEnd_121071 36840068930726543914495 := by
  unfold tailWord_121071
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415822144387919125707067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2943881429591946083804711 4415822144387919125707067)
  ·
    refine ⟨6623733216581878688560601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415822144387919125707067 6623733216581878688560601)
    ·
      refine ⟨4967799912436409016420451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6623733216581878688560601 4967799912436409016420451)
      ·
        refine ⟨7451699868654613524630677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967799912436409016420451 7451699868654613524630677)
        ·
          refine ⟨349298431343185008967063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7451699868654613524630677 349298431343185008967063)
          ·
            refine ⟨523947647014777513450595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 349298431343185008967063 523947647014777513450595)
            ·
              refine ⟨785921470522166270175893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 523947647014777513450595 785921470522166270175893)
              ·
                refine ⟨36840068930726543914495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 785921470522166270175893 36840068930726543914495)
                ·
                  rfl

theorem cell19_121071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_121071 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121071 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121071 prefixEnd_121071 := by exact prefixLift 121071
  have htrace : WordTrace (prefixWord ++ tailWord_121071) baseStart_121071 baseEnd_121071 := by
    simpa [prefixWord, tailWord_121071, baseEnd_121071] using wordTrace_append hprefix tailTrace_121071
  have hstable : (prefixWord ++ tailWord_121071).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121071).length < 2 ^ (prefixWord ++ tailWord_121071).sum := by decide
  have hdescent : baseEnd_121071 < baseStart_121071 := by decide
  rcases family_descends (prefixWord ++ tailWord_121071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121202 : List Nat := [3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_121202 : Nat := 118140960795 + 121202 * 2 ^ 59
def prefixEnd_121202 : Nat := 4983230072969 + 3 ^ 40 * 121202 * 2
def baseEnd_121202 : Nat := 36879930243757055003027

theorem tailTrace_121202 : CollatzResearch.WordTrace tailWord_121202 prefixEnd_121202 36879930243757055003027 := by
  unfold tailWord_121202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105150026728332124681465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2947066737942218999150573 1105150026728332124681465)
  ·
    refine ⟨828862520046249093511099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1105150026728332124681465 828862520046249093511099)
    ·
      refine ⟨1243293780069373640266649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 828862520046249093511099 1243293780069373640266649)
      ·
        refine ⟨932470335052030230199987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1243293780069373640266649 932470335052030230199987)
        ·
          refine ⟨1398705502578045345299981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 932470335052030230199987 1398705502578045345299981)
          ·
            refine ⟨524514563466767004487493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1398705502578045345299981 524514563466767004487493)
            ·
              refine ⟨98346480650018813341405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 524514563466767004487493 98346480650018813341405)
              ·
                refine ⟨36879930243757055003027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98346480650018813341405 36879930243757055003027)
                ·
                  rfl

theorem cell19_121202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_121202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121202 prefixEnd_121202 := by exact prefixLift 121202
  have htrace : WordTrace (prefixWord ++ tailWord_121202) baseStart_121202 baseEnd_121202 := by
    simpa [prefixWord, tailWord_121202, baseEnd_121202] using wordTrace_append hprefix tailTrace_121202
  have hstable : (prefixWord ++ tailWord_121202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121202).length < 2 ^ (prefixWord ++ tailWord_121202).sum := by decide
  have hdescent : baseEnd_121202 < baseStart_121202 := by decide
  rcases family_descends (prefixWord ++ tailWord_121202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121240 : List Nat := [2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_121240 : Nat := 118140960795 + 121240 * 2 ^ 59
def prefixEnd_121240 : Nat := 4983230072969 + 3 ^ 40 * 121240 * 2
def baseEnd_121240 : Nat := 36891493067384226158479

theorem tailTrace_121240 : CollatzResearch.WordTrace tailWord_121240 prefixEnd_121240 36891493067384226158479 := by
  unfold tailWord_121240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2210993040387830494304587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2947990720517107325739449 2210993040387830494304587)
  ·
    refine ⟨3316489560581745741456881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2210993040387830494304587 3316489560581745741456881)
    ·
      refine ⟨2487367170436309306092661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3316489560581745741456881 2487367170436309306092661)
      ·
        refine ⟨233190672228403997446187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2487367170436309306092661 233190672228403997446187)
        ·
          refine ⟨349786008342605996169281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 233190672228403997446187 349786008342605996169281)
          ·
            refine ⟨262339506256954497126961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 349786008342605996169281 262339506256954497126961)
            ·
              refine ⟨196754629692715872845221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262339506256954497126961 196754629692715872845221)
              ·
                refine ⟨36891493067384226158479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 196754629692715872845221 36891493067384226158479)
                ·
                  rfl

theorem cell19_121240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_121240 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121240 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121240 prefixEnd_121240 := by exact prefixLift 121240
  have htrace : WordTrace (prefixWord ++ tailWord_121240) baseStart_121240 baseEnd_121240 := by
    simpa [prefixWord, tailWord_121240, baseEnd_121240] using wordTrace_append hprefix tailTrace_121240
  have hstable : (prefixWord ++ tailWord_121240).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121240).length < 2 ^ (prefixWord ++ tailWord_121240).sum := by decide
  have hdescent : baseEnd_121240 < baseStart_121240 := by decide
  rcases family_descends (prefixWord ++ tailWord_121240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121242 : List Nat := [3, 1, 1, 4, 1, 2, 1, 6]
def baseStart_121242 : Nat := 118140960795 + 121242 * 2 ^ 59
def prefixEnd_121242 : Nat := 4983230072969 + 3 ^ 40 * 121242 * 2
def baseEnd_121242 : Nat := 36892101637048814114029

theorem tailTrace_121242 : CollatzResearch.WordTrace tailWord_121242 prefixEnd_121242 36892101637048814114029 := by
  unfold tailWord_121242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1105514756692103832545495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2948039351178943553454653 1105514756692103832545495)
  ·
    refine ⟨1658272135038155748818243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1105514756692103832545495 1658272135038155748818243)
    ·
      refine ⟨2487408202557233623227365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1658272135038155748818243 2487408202557233623227365)
      ·
        refine ⟨466389037979481304355131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2487408202557233623227365 466389037979481304355131)
        ·
          refine ⟨699583556969221956532697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466389037979481304355131 699583556969221956532697)
          ·
            refine ⟨524687667726916467399523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 699583556969221956532697 524687667726916467399523)
            ·
              refine ⟨787031501590374701099285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 524687667726916467399523 787031501590374701099285)
              ·
                refine ⟨36892101637048814114029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 787031501590374701099285 36892101637048814114029)
                ·
                  rfl

theorem cell19_121242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_121242 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121242 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121242 prefixEnd_121242 := by exact prefixLift 121242
  have htrace : WordTrace (prefixWord ++ tailWord_121242) baseStart_121242 baseEnd_121242 := by
    simpa [prefixWord, tailWord_121242, baseEnd_121242] using wordTrace_append hprefix tailTrace_121242
  have hstable : (prefixWord ++ tailWord_121242).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121242).length < 2 ^ (prefixWord ++ tailWord_121242).sum := by decide
  have hdescent : baseEnd_121242 < baseStart_121242 := by decide
  rcases family_descends (prefixWord ++ tailWord_121242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121373 : List Nat := [1, 4, 2, 2, 1, 2, 4, 3]
def baseStart_121373 : Nat := 118140960795 + 121373 * 2 ^ 59
def prefixEnd_121373 : Nat := 4983230072969 + 3 ^ 40 * 121373 * 2
def baseEnd_121373 : Nat := 36931962950079325202561

theorem tailTrace_121373 : CollatzResearch.WordTrace tailWord_121373 prefixEnd_121373 36931962950079325202561 := by
  unfold tailWord_121373
  simp only [CollatzResearch.WordTrace]
  refine ⟨4426836989293824703200773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2951224659529216468800515 4426836989293824703200773)
  ·
    refine ⟨830031935492592131850145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4426836989293824703200773 830031935492592131850145)
    ·
      refine ⟨622523951619444098887609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 830031935492592131850145 622523951619444098887609)
      ·
        refine ⟨466892963714583074165707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 622523951619444098887609 466892963714583074165707)
        ·
          refine ⟨700339445571874611248561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 466892963714583074165707 700339445571874611248561)
          ·
            refine ⟨525254584178905958436421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 700339445571874611248561 525254584178905958436421)
            ·
              refine ⟨98485234533544867206829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 525254584178905958436421 98485234533544867206829)
              ·
                refine ⟨36931962950079325202561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98485234533544867206829 36931962950079325202561)
                ·
                  rfl

theorem cell19_121373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 3].length) (baseStart_121373 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121373 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121373 prefixEnd_121373 := by exact prefixLift 121373
  have htrace : WordTrace (prefixWord ++ tailWord_121373) baseStart_121373 baseEnd_121373 := by
    simpa [prefixWord, tailWord_121373, baseEnd_121373] using wordTrace_append hprefix tailTrace_121373
  have hstable : (prefixWord ++ tailWord_121373).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121373).length < 2 ^ (prefixWord ++ tailWord_121373).sum := by decide
  have hdescent : baseEnd_121373 < baseStart_121373 := by decide
  rcases family_descends (prefixWord ++ tailWord_121373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121390 : List Nat := [4, 1, 3, 1, 4, 1, 5]
def baseStart_121390 : Nat := 118140960795 + 121390 * 2 ^ 59
def prefixEnd_121390 : Nat := 4983230072969 + 3 ^ 40 * 121390 * 2
def baseEnd_121390 : Nat := 12312378597409440941579

theorem tailTrace_121390 : CollatzResearch.WordTrace tailWord_121390 prefixEnd_121390 12312378597409440941579 := by
  unfold tailWord_121390
  simp only [CollatzResearch.WordTrace]
  refine ⟨553432128779029575821203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2951638020154824404379749 553432128779029575821203)
  ·
    refine ⟨830148193168544363731805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 553432128779029575821203 830148193168544363731805)
    ·
      refine ⟨311305572438204136399427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 830148193168544363731805 311305572438204136399427)
      ·
        refine ⟨466958358657306204599141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 311305572438204136399427 466958358657306204599141)
        ·
          refine ⟨87554692248244913362339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 466958358657306204599141 87554692248244913362339)
          ·
            refine ⟨131332038372367370043509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87554692248244913362339 131332038372367370043509)
            ·
              refine ⟨12312378597409440941579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 131332038372367370043509 12312378597409440941579)
              ·
                rfl

theorem cell19_121390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 5].length) (baseStart_121390 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121390 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121390 prefixEnd_121390 := by exact prefixLift 121390
  have htrace : WordTrace (prefixWord ++ tailWord_121390) baseStart_121390 baseEnd_121390 := by
    simpa [prefixWord, tailWord_121390, baseEnd_121390] using wordTrace_append hprefix tailTrace_121390
  have hstable : (prefixWord ++ tailWord_121390).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121390).length < 2 ^ (prefixWord ++ tailWord_121390).sum := by decide
  have hdescent : baseEnd_121390 < baseStart_121390 := by decide
  rcases family_descends (prefixWord ++ tailWord_121390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121413 : List Nat := [1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_121413 : Nat := 118140960795 + 121413 * 2 ^ 59
def prefixEnd_121413 : Nat := 4983230072969 + 3 ^ 40 * 121413 * 2
def baseEnd_121413 : Nat := 36944134343371084313563

theorem tailTrace_121413 : CollatzResearch.WordTrace tailWord_121413 prefixEnd_121413 36944134343371084313563 := by
  unfold tailWord_121413
  simp only [CollatzResearch.WordTrace]
  refine ⟨4428295909148911534656893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2952197272765941023104595 4428295909148911534656893)
  ·
    refine ⟨1660610965930841825496335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4428295909148911534656893 1660610965930841825496335)
    ·
      refine ⟨2490916448896262738244503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1660610965930841825496335 2490916448896262738244503)
      ·
        refine ⟨3736374673344394107366755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2490916448896262738244503 3736374673344394107366755)
        ·
          refine ⟨5604562010016591161050133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3736374673344394107366755 5604562010016591161050133)
          ·
            refine ⟨262713844219527710674225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5604562010016591161050133 262713844219527710674225)
            ·
              refine ⟨197035383164645783005669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 262713844219527710674225 197035383164645783005669)
              ·
                refine ⟨36944134343371084313563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 197035383164645783005669 36944134343371084313563)
                ·
                  rfl

theorem cell19_121413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_121413 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121413 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121413 prefixEnd_121413 := by exact prefixLift 121413
  have htrace : WordTrace (prefixWord ++ tailWord_121413) baseStart_121413 baseEnd_121413 := by
    simpa [prefixWord, tailWord_121413, baseEnd_121413] using wordTrace_append hprefix tailTrace_121413
  have hstable : (prefixWord ++ tailWord_121413).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121413).length < 2 ^ (prefixWord ++ tailWord_121413).sum := by decide
  have hdescent : baseEnd_121413 < baseStart_121413 := by decide
  rcases family_descends (prefixWord ++ tailWord_121413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121529 : List Nat := [1, 2, 1, 4, 1, 1, 1, 8]
def baseStart_121529 : Nat := 118140960795 + 121529 * 2 ^ 59
def prefixEnd_121529 : Nat := 4983230072969 + 3 ^ 40 * 121529 * 2
def baseEnd_121529 : Nat := 36979431383917185735469

theorem tailTrace_121529 : CollatzResearch.WordTrace tailWord_121529 prefixEnd_121529 36979431383917185735469 := by
  unfold tailWord_121529
  simp only [CollatzResearch.WordTrace]
  refine ⟨4432526776728663345879641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2955017851152442230586427 4432526776728663345879641)
  ·
    refine ⟨3324395082546497509409731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4432526776728663345879641 3324395082546497509409731)
    ·
      refine ⟨4986592623819746264114597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3324395082546497509409731 4986592623819746264114597)
      ·
        refine ⟨934986116966202424521487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4986592623819746264114597 934986116966202424521487)
        ·
          refine ⟨1402479175449303636782231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 934986116966202424521487 1402479175449303636782231)
          ·
            refine ⟨2103718763173955455173347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1402479175449303636782231 2103718763173955455173347)
            ·
              refine ⟨3155578144760933182760021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2103718763173955455173347 3155578144760933182760021)
              ·
                refine ⟨36979431383917185735469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3155578144760933182760021 36979431383917185735469)
                ·
                  rfl

theorem cell19_121529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_121529 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121529 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121529 prefixEnd_121529 := by exact prefixLift 121529
  have htrace : WordTrace (prefixWord ++ tailWord_121529) baseStart_121529 baseEnd_121529 := by
    simpa [prefixWord, tailWord_121529, baseEnd_121529] using wordTrace_append hprefix tailTrace_121529
  have hstable : (prefixWord ++ tailWord_121529).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121529).length < 2 ^ (prefixWord ++ tailWord_121529).sum := by decide
  have hdescent : baseEnd_121529 < baseStart_121529 := by decide
  rcases family_descends (prefixWord ++ tailWord_121529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121544 : List Nat := [2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_121544 : Nat := 118140960795 + 121544 * 2 ^ 59
def prefixEnd_121544 : Nat := 4983230072969 + 3 ^ 40 * 121544 * 2
def baseEnd_121544 : Nat := 36983995656401595402095

theorem tailTrace_121544 : CollatzResearch.WordTrace tailWord_121544 prefixEnd_121544 36983995656401595402095 := by
  unfold tailWord_121544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2216536935837160453837843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2955382581116213938450457 2216536935837160453837843)
  ·
    refine ⟨3324805403755740680756765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2216536935837160453837843 3324805403755740680756765)
    ·
      refine ⟨1246802026408402755283787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3324805403755740680756765 1246802026408402755283787)
      ·
        refine ⟨1870203039612604132925681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246802026408402755283787 1870203039612604132925681)
        ·
          refine ⟨1402652279709453099694261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1870203039612604132925681 1402652279709453099694261)
          ·
            refine ⟨131498651222761228096337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1402652279709453099694261 131498651222761228096337)
            ·
              refine ⟨98623988417070921072253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 131498651222761228096337 98623988417070921072253)
              ·
                refine ⟨36983995656401595402095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 98623988417070921072253 36983995656401595402095)
                ·
                  rfl

theorem cell19_121544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_121544 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121544 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121544 prefixEnd_121544 := by exact prefixLift 121544
  have htrace : WordTrace (prefixWord ++ tailWord_121544) baseStart_121544 baseEnd_121544 := by
    simpa [prefixWord, tailWord_121544, baseEnd_121544] using wordTrace_append hprefix tailTrace_121544
  have hstable : (prefixWord ++ tailWord_121544).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121544).length < 2 ^ (prefixWord ++ tailWord_121544).sum := by decide
  have hdescent : baseEnd_121544 < baseStart_121544 := by decide
  rcases family_descends (prefixWord ++ tailWord_121544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_121546 : List Nat := [3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_121546 : Nat := 118140960795 + 121546 * 2 ^ 59
def prefixEnd_121546 : Nat := 4983230072969 + 3 ^ 40 * 121546 * 2
def baseEnd_121546 : Nat := 36984604226066183357645

theorem tailTrace_121546 : CollatzResearch.WordTrace tailWord_121546 prefixEnd_121546 36984604226066183357645 := by
  unfold tailWord_121546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1108286704416768812312123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2955431211778050166165661 1108286704416768812312123)
  ·
    refine ⟨1662430056625153218468185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1108286704416768812312123 1662430056625153218468185)
    ·
      refine ⟨1246822542468864913851139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1662430056625153218468185 1246822542468864913851139)
      ·
        refine ⟨1870233813703297370776709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1246822542468864913851139 1870233813703297370776709)
        ·
          refine ⟨350668840069368257020633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1870233813703297370776709 350668840069368257020633)
          ·
            refine ⟨263001630052026192765475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 350668840069368257020633 263001630052026192765475)
            ·
              refine ⟨394502445078039289148213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 263001630052026192765475 394502445078039289148213)
              ·
                refine ⟨36984604226066183357645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 394502445078039289148213 36984604226066183357645)
                ·
                  rfl

theorem cell19_121546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_121546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_121546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_121546 prefixEnd_121546 := by exact prefixLift 121546
  have htrace : WordTrace (prefixWord ++ tailWord_121546) baseStart_121546 baseEnd_121546 := by
    simpa [prefixWord, tailWord_121546, baseEnd_121546] using wordTrace_append hprefix tailTrace_121546
  have hstable : (prefixWord ++ tailWord_121546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_121546).length < 2 ^ (prefixWord ++ tailWord_121546).sum := by decide
  have hdescent : baseEnd_121546 < baseStart_121546 := by decide
  rcases family_descends (prefixWord ++ tailWord_121546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
