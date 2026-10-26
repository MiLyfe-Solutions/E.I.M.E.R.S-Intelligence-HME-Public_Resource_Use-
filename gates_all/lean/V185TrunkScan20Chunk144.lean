import V185TrunkScan20Chunk143

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_876439 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 5]
def baseStart_876439 : Nat := 118140960795 + 876439 * 2 ^ 59
def prefixEnd_876439 : Nat := 4983230072969 + 3 ^ 40 * 876439 * 2
def baseEnd_876439 : Nat := 400030641196445921850521

theorem tailTrace_876439 : CollatzResearch.WordTrace tailWord_876439 prefixEnd_876439 400030641196445921850521 := by
  unfold tailWord_876439
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966356471818661709368371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21310904314545774472912247 31966356471818661709368371)
  ·
    refine ⟨47949534707727992564052557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31966356471818661709368371 47949534707727992564052557)
    ·
      refine ⟨17981075515397997211519709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47949534707727992564052557 17981075515397997211519709)
      ·
        refine ⟨6742903318274248954319891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17981075515397997211519709 6742903318274248954319891)
        ·
          refine ⟨10114354977411373431479837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6742903318274248954319891 10114354977411373431479837)
          ·
            refine ⟨3792883116529265036804939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10114354977411373431479837 3792883116529265036804939)
            ·
              refine ⟨5689324674793897555207409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3792883116529265036804939 5689324674793897555207409)
              ·
                refine ⟨4266993506095423166405557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5689324674793897555207409 4266993506095423166405557)
                ·
                  refine ⟨400030641196445921850521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4266993506095423166405557 400030641196445921850521)
                  ·
                    rfl

theorem cell20_876439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_876439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876439 prefixEnd_876439 := by exact prefixLift 876439
  have htrace : WordTrace (prefixWord ++ tailWord_876439) baseStart_876439 baseEnd_876439 := by
    simpa [prefixWord, tailWord_876439, baseEnd_876439] using wordTrace_append hprefix tailTrace_876439
  have hstable : (prefixWord ++ tailWord_876439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876439).length < 2 ^ (prefixWord ++ tailWord_876439).sum := by decide
  have hdescent : baseEnd_876439 < baseStart_876439 := by decide
  rcases family_descends (prefixWord ++ tailWord_876439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876449 : List Nat := [1, 2, 3, 4, 2, 2, 6]
def baseStart_876449 : Nat := 118140960795 + 876449 * 2 ^ 59
def prefixEnd_876449 : Nat := 4983230072969 + 3 ^ 40 * 876449 * 2
def baseEnd_876449 : Nat := 44448356163214481279683

theorem tailTrace_876449 : CollatzResearch.WordTrace tailWord_876449 prefixEnd_876449 44448356163214481279683 := by
  unfold tailWord_876449
  simp only [CollatzResearch.WordTrace]
  refine ⟨31966721201782433417232401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21311147467854955611488267 31966721201782433417232401)
  ·
    refine ⟨23975040901336825062924301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31966721201782433417232401 23975040901336825062924301)
    ·
      refine ⟨8990640338001309398596613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23975040901336825062924301 8990640338001309398596613)
      ·
        refine ⟨1685745063375245512236865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8990640338001309398596613 1685745063375245512236865)
        ·
          refine ⟨1264308797531434134177649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685745063375245512236865 1264308797531434134177649)
          ·
            refine ⟨948231598148575600633237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264308797531434134177649 948231598148575600633237)
            ·
              refine ⟨44448356163214481279683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 948231598148575600633237 44448356163214481279683)
              ·
                rfl

theorem cell20_876449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_876449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876449 prefixEnd_876449 := by exact prefixLift 876449
  have htrace : WordTrace (prefixWord ++ tailWord_876449) baseStart_876449 baseEnd_876449 := by
    simpa [prefixWord, tailWord_876449, baseEnd_876449] using wordTrace_append hprefix tailTrace_876449
  have hstable : (prefixWord ++ tailWord_876449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876449).length < 2 ^ (prefixWord ++ tailWord_876449).sum := by decide
  have hdescent : baseEnd_876449 < baseStart_876449 := by decide
  rcases family_descends (prefixWord ++ tailWord_876449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876491 : List Nat := [1, 1, 1, 1, 3, 4, 1, 8]
def baseStart_876491 : Nat := 118140960795 + 876491 * 2 ^ 59
def prefixEnd_876491 : Nat := 4983230072969 + 3 ^ 40 * 876491 * 2
def baseEnd_876491 : Nat := 133351458471121617372325

theorem tailTrace_876491 : CollatzResearch.WordTrace tailWord_876491 prefixEnd_876491 133351458471121617372325 := by
  unfold tailWord_876491
  simp only [CollatzResearch.WordTrace]
  refine ⟨31968253067630274590261327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21312168711753516393507551 31968253067630274590261327)
  ·
    refine ⟨47952379601445411885391991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31968253067630274590261327 47952379601445411885391991)
    ·
      refine ⟨71928569402168117828087987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47952379601445411885391991 71928569402168117828087987)
      ·
        refine ⟨107892854103252176742131981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71928569402168117828087987 107892854103252176742131981)
        ·
          refine ⟨40459820288719566278299493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 107892854103252176742131981 40459820288719566278299493)
          ·
            refine ⟨7586216304134918677181155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40459820288719566278299493 7586216304134918677181155)
            ·
              refine ⟨11379324456202378015771733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7586216304134918677181155 11379324456202378015771733)
              ·
                refine ⟨133351458471121617372325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11379324456202378015771733 133351458471121617372325)
                ·
                  rfl

theorem cell20_876491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 8].length) (baseStart_876491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876491 prefixEnd_876491 := by exact prefixLift 876491
  have htrace : WordTrace (prefixWord ++ tailWord_876491) baseStart_876491 baseEnd_876491 := by
    simpa [prefixWord, tailWord_876491, baseEnd_876491] using wordTrace_append hprefix tailTrace_876491
  have hstable : (prefixWord ++ tailWord_876491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876491).length < 2 ^ (prefixWord ++ tailWord_876491).sum := by decide
  have hdescent : baseEnd_876491 < baseStart_876491 := by decide
  rcases family_descends (prefixWord ++ tailWord_876491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876514 : List Nat := [3, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_876514 : Nat := 118140960795 + 876514 * 2 ^ 59
def prefixEnd_876514 : Nat := 4983230072969 + 3 ^ 40 * 876514 * 2
def baseEnd_876514 : Nat := 400064873240078994350215

theorem tailTrace_876514 : CollatzResearch.WordTrace tailWord_876514 prefixEnd_876514 400064873240078994350215 := by
  unfold tailWord_876514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992272986636737379587149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21312727964364633012232397 7992272986636737379587149)
  ·
    refine ⟨2997102369988776517345181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7992272986636737379587149 2997102369988776517345181)
    ·
      refine ⟨1123913388745791194004443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2997102369988776517345181 1123913388745791194004443)
      ·
        refine ⟨1685870083118686791006665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123913388745791194004443 1685870083118686791006665)
        ·
          refine ⟨1264402562339015093254999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1685870083118686791006665 1264402562339015093254999)
          ·
            refine ⟨1896603843508522639882499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1264402562339015093254999 1896603843508522639882499)
            ·
              refine ⟨2844905765262783959823749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1896603843508522639882499 2844905765262783959823749)
              ·
                refine ⟨533419830986771992466953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2844905765262783959823749 533419830986771992466953)
                ·
                  refine ⟨400064873240078994350215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533419830986771992466953 400064873240078994350215)
                  ·
                    rfl

theorem cell20_876514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_876514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876514 prefixEnd_876514 := by exact prefixLift 876514
  have htrace : WordTrace (prefixWord ++ tailWord_876514) baseStart_876514 baseEnd_876514 := by
    simpa [prefixWord, tailWord_876514, baseEnd_876514] using wordTrace_append hprefix tailTrace_876514
  have hstable : (prefixWord ++ tailWord_876514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876514).length < 2 ^ (prefixWord ++ tailWord_876514).sum := by decide
  have hdescent : baseEnd_876514 < baseStart_876514 := by decide
  rcases family_descends (prefixWord ++ tailWord_876514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876542 : List Nat := [4, 2, 2, 2, 1, 2, 3, 4]
def baseStart_876542 : Nat := 118140960795 + 876542 * 2 ^ 59
def prefixEnd_876542 : Nat := 4983230072969 + 3 ^ 40 * 876542 * 2
def baseEnd_876542 : Nat := 133359217734345113805589

theorem tailTrace_876542 : CollatzResearch.WordTrace tailWord_876542 prefixEnd_876542 133359217734345113805589 := by
  unfold tailWord_876542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996264148805688787545985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21313408793630340200245253 3996264148805688787545985)
  ·
    refine ⟨2997198111604266590659489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3996264148805688787545985 2997198111604266590659489)
    ·
      refine ⟨2247898583703199942994617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2997198111604266590659489 2247898583703199942994617)
      ·
        refine ⟨1685923937777399957245963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2247898583703199942994617 1685923937777399957245963)
        ·
          refine ⟨2528885906666099935868945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1685923937777399957245963 2528885906666099935868945)
          ·
            refine ⟨1896664429999574951901709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2528885906666099935868945 1896664429999574951901709)
            ·
              refine ⟨711249161249840606963141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1896664429999574951901709 711249161249840606963141)
              ·
                refine ⟨133359217734345113805589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711249161249840606963141 133359217734345113805589)
                ·
                  rfl

theorem cell20_876542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_876542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876542 prefixEnd_876542 := by exact prefixLift 876542
  have htrace : WordTrace (prefixWord ++ tailWord_876542) baseStart_876542 baseEnd_876542 := by
    simpa [prefixWord, tailWord_876542, baseEnd_876542] using wordTrace_append hprefix tailTrace_876542
  have hstable : (prefixWord ++ tailWord_876542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876542).length < 2 ^ (prefixWord ++ tailWord_876542).sum := by decide
  have hdescent : baseEnd_876542 < baseStart_876542 := by decide
  rcases family_descends (prefixWord ++ tailWord_876542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876556 : List Nat := [2, 2, 1, 2, 3, 1, 4, 3, 2]
def baseStart_876556 : Nat := 118140960795 + 876556 * 2 ^ 59
def prefixEnd_876556 : Nat := 4983230072969 + 3 ^ 40 * 876556 * 2
def baseEnd_876556 : Nat := 400084043184513514950043

theorem tailTrace_876556 : CollatzResearch.WordTrace tailWord_876556 prefixEnd_876556 400084043184513514950043 := by
  unfold tailWord_876556
  simp only [CollatzResearch.WordTrace]
  refine ⟨15985311906197395345688761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21313749208263193794251681 15985311906197395345688761)
  ·
    refine ⟨11988983929648046509266571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15985311906197395345688761 11988983929648046509266571)
    ·
      refine ⟨17983475894472069763899857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11988983929648046509266571 17983475894472069763899857)
      ·
        refine ⟨13487606920854052322924893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17983475894472069763899857 13487606920854052322924893)
        ·
          refine ⟨5057852595320269621096835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13487606920854052322924893 5057852595320269621096835)
          ·
            refine ⟨7586778892980404431645253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5057852595320269621096835 7586778892980404431645253)
            ·
              refine ⟨1422521042433825830933485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7586778892980404431645253 1422521042433825830933485)
              ·
                refine ⟨533445390912684686600057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1422521042433825830933485 533445390912684686600057)
                ·
                  refine ⟨400084043184513514950043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533445390912684686600057 400084043184513514950043)
                  ·
                    rfl

theorem cell20_876556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_876556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876556 prefixEnd_876556 := by exact prefixLift 876556
  have htrace : WordTrace (prefixWord ++ tailWord_876556) baseStart_876556 baseEnd_876556 := by
    simpa [prefixWord, tailWord_876556, baseEnd_876556] using wordTrace_append hprefix tailTrace_876556
  have hstable : (prefixWord ++ tailWord_876556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876556).length < 2 ^ (prefixWord ++ tailWord_876556).sum := by decide
  have hdescent : baseEnd_876556 < baseStart_876556 := by decide
  rcases family_descends (prefixWord ++ tailWord_876556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876570 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_876570 : Nat := 118140960795 + 876570 * 2 ^ 59
def prefixEnd_876570 : Nat := 4983230072969 + 3 ^ 40 * 876570 * 2
def baseEnd_876570 : Nat := 400090433165991688483319

theorem tailTrace_876570 : CollatzResearch.WordTrace tailWord_876570 prefixEnd_876570 400090433165991688483319 := by
  unfold tailWord_876570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7992783608586017770596791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21314089622896047388258109 7992783608586017770596791)
  ·
    refine ⟨11989175412879026655895187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7992783608586017770596791 11989175412879026655895187)
    ·
      refine ⟨17983763119318539983842781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11989175412879026655895187 17983763119318539983842781)
      ·
        refine ⟨6743911169744452493941043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17983763119318539983842781 6743911169744452493941043)
        ·
          refine ⟨10115866754616678740911565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6743911169744452493941043 10115866754616678740911565)
          ·
            refine ⟨3793450032981254527841837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10115866754616678740911565 3793450032981254527841837)
            ·
              refine ⟨1422543762367970447940689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3793450032981254527841837 1422543762367970447940689)
              ·
                refine ⟨1066907821775977835955517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1422543762367970447940689 1066907821775977835955517)
                ·
                  refine ⟨400090433165991688483319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066907821775977835955517 400090433165991688483319)
                  ·
                    rfl

theorem cell20_876570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_876570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876570 prefixEnd_876570 := by exact prefixLift 876570
  have htrace : WordTrace (prefixWord ++ tailWord_876570) baseStart_876570 baseEnd_876570 := by
    simpa [prefixWord, tailWord_876570, baseEnd_876570] using wordTrace_append hprefix tailTrace_876570
  have hstable : (prefixWord ++ tailWord_876570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876570).length < 2 ^ (prefixWord ++ tailWord_876570).sum := by decide
  have hdescent : baseEnd_876570 < baseStart_876570 := by decide
  rcases family_descends (prefixWord ++ tailWord_876570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876622 : List Nat := [4, 1, 1, 1, 1, 6, 6]
def baseStart_876622 : Nat := 118140960795 + 876622 * 2 ^ 59
def prefixEnd_876622 : Nat := 4983230072969 + 3 ^ 40 * 876622 * 2
def baseEnd_876622 : Nat := 44457129709212290972197

theorem tailTrace_876622 : CollatzResearch.WordTrace tailWord_876622 prefixEnd_876622 44457129709212290972197 := by
  unfold tailWord_876622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996628878769460495410015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21315354020103789308853413 3996628878769460495410015)
  ·
    refine ⟨5994943318154190743115023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3996628878769460495410015 5994943318154190743115023)
    ·
      refine ⟨8992414977231286114672535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5994943318154190743115023 8992414977231286114672535)
      ·
        refine ⟨13488622465846929172008803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8992414977231286114672535 13488622465846929172008803)
        ·
          refine ⟨20232933698770393758013205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13488622465846929172008803 20232933698770393758013205)
          ·
            refine ⟨948418767129862207406869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20232933698770393758013205 948418767129862207406869)
            ·
              refine ⟨44457129709212290972197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 948418767129862207406869 44457129709212290972197)
              ·
                rfl

theorem cell20_876622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_876622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876622 prefixEnd_876622 := by exact prefixLift 876622
  have htrace : WordTrace (prefixWord ++ tailWord_876622) baseStart_876622 baseEnd_876622 := by
    simpa [prefixWord, tailWord_876622, baseEnd_876622] using wordTrace_append hprefix tailTrace_876622
  have hstable : (prefixWord ++ tailWord_876622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876622).length < 2 ^ (prefixWord ++ tailWord_876622).sum := by decide
  have hdescent : baseEnd_876622 < baseStart_876622 := by decide
  rcases family_descends (prefixWord ++ tailWord_876622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876629 : List Nat := [1, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_876629 : Nat := 118140960795 + 876629 * 2 ^ 59
def prefixEnd_876629 : Nat := 4983230072969 + 3 ^ 40 * 876629 * 2
def baseEnd_876629 : Nat := 400117362373649705516411

theorem tailTrace_876629 : CollatzResearch.WordTrace tailWord_876629 prefixEnd_876629 400117362373649705516411 := by
  unfold tailWord_876629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31973286341130324158784941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21315524227420216105856627 31973286341130324158784941)
  ·
    refine ⟨11989982377923871559544353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31973286341130324158784941 11989982377923871559544353)
    ·
      refine ⟨8992486783442903669658265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11989982377923871559544353 8992486783442903669658265)
      ·
        refine ⟨6744365087582177752243699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8992486783442903669658265 6744365087582177752243699)
        ·
          refine ⟨10116547631373266628365549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744365087582177752243699 10116547631373266628365549)
          ·
            refine ⟨3793705361764974985637081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10116547631373266628365549 3793705361764974985637081)
            ·
              refine ⟨2845279021323731239227811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3793705361764974985637081 2845279021323731239227811)
              ·
                refine ⟨4267918531985596858841717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2845279021323731239227811 4267918531985596858841717)
                ·
                  refine ⟨400117362373649705516411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4267918531985596858841717 400117362373649705516411)
                  ·
                    rfl

theorem cell20_876629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_876629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876629 prefixEnd_876629 := by exact prefixLift 876629
  have htrace : WordTrace (prefixWord ++ tailWord_876629) baseStart_876629 baseEnd_876629 := by
    simpa [prefixWord, tailWord_876629, baseEnd_876629] using wordTrace_append hprefix tailTrace_876629
  have hstable : (prefixWord ++ tailWord_876629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876629).length < 2 ^ (prefixWord ++ tailWord_876629).sum := by decide
  have hdescent : baseEnd_876629 < baseStart_876629 := by decide
  rcases family_descends (prefixWord ++ tailWord_876629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876638 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_876638 : Nat := 118140960795 + 876638 * 2 ^ 59
def prefixEnd_876638 : Nat := 4983230072969 + 3 ^ 40 * 876638 * 2
def baseEnd_876638 : Nat := 400121470218885674216375

theorem tailTrace_876638 : CollatzResearch.WordTrace tailWord_876638 prefixEnd_876638 400121470218885674216375 := by
  unfold tailWord_876638
  simp only [CollatzResearch.WordTrace]
  refine ⟨3996701824762214836982821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21315743065398479130575045 3996701824762214836982821)
  ·
    refine ⟨749381592142915281934279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3996701824762214836982821 749381592142915281934279)
    ·
      refine ⟨1124072388214372922901419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 749381592142915281934279 1124072388214372922901419)
      ·
        refine ⟨1686108582321559384352129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1124072388214372922901419 1686108582321559384352129)
        ·
          refine ⟨1264581436741169538264097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1686108582321559384352129 1264581436741169538264097)
          ·
            refine ⟨948436077555877153698073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1264581436741169538264097 948436077555877153698073)
            ·
              refine ⟨711327058166907865273555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948436077555877153698073 711327058166907865273555)
              ·
                refine ⟨1066990587250361797910333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711327058166907865273555 1066990587250361797910333)
                ·
                  refine ⟨400121470218885674216375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1066990587250361797910333 400121470218885674216375)
                  ·
                    rfl

theorem cell20_876638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_876638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876638 prefixEnd_876638 := by exact prefixLift 876638
  have htrace : WordTrace (prefixWord ++ tailWord_876638) baseStart_876638 baseEnd_876638 := by
    simpa [prefixWord, tailWord_876638, baseEnd_876638] using wordTrace_append hprefix tailTrace_876638
  have hstable : (prefixWord ++ tailWord_876638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876638).length < 2 ^ (prefixWord ++ tailWord_876638).sum := by decide
  have hdescent : baseEnd_876638 < baseStart_876638 := by decide
  rcases family_descends (prefixWord ++ tailWord_876638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876643 : List Nat := [1, 1, 1, 5, 1, 1, 3, 7]
def baseStart_876643 : Nat := 118140960795 + 876643 * 2 ^ 59
def prefixEnd_876643 : Nat := 4983230072969 + 3 ^ 40 * 876643 * 2
def baseEnd_876643 : Nat := 133374584118375959683229

theorem tailTrace_876643 : CollatzResearch.WordTrace tailWord_876643 prefixEnd_876643 133374584118375959683229 := by
  unfold tailWord_876643
  simp only [CollatzResearch.WordTrace]
  refine ⟨31973796963079604549794583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21315864642053069699863055 31973796963079604549794583)
  ·
    refine ⟨47960695444619406824691875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31973796963079604549794583 47960695444619406824691875)
    ·
      refine ⟨71941043166929110237037813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47960695444619406824691875 71941043166929110237037813)
      ·
        refine ⟨6744472796899604084722295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 71941043166929110237037813 6744472796899604084722295)
        ·
          refine ⟨10116709195349406127083443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6744472796899604084722295 10116709195349406127083443)
          ·
            refine ⟨15175063793024109190625165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10116709195349406127083443 15175063793024109190625165)
            ·
              refine ⟨5690648922384040946484437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15175063793024109190625165 5690648922384040946484437)
              ·
                refine ⟨133374584118375959683229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5690648922384040946484437 133374584118375959683229)
                ·
                  rfl

theorem cell20_876643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 7].length) (baseStart_876643 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876643 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876643 prefixEnd_876643 := by exact prefixLift 876643
  have htrace : WordTrace (prefixWord ++ tailWord_876643) baseStart_876643 baseEnd_876643 := by
    simpa [prefixWord, tailWord_876643, baseEnd_876643] using wordTrace_append hprefix tailTrace_876643
  have hstable : (prefixWord ++ tailWord_876643).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876643).length < 2 ^ (prefixWord ++ tailWord_876643).sum := by decide
  have hdescent : baseEnd_876643 < baseStart_876643 := by decide
  rcases family_descends (prefixWord ++ tailWord_876643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876798 : List Nat := [4, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_876798 : Nat := 118140960795 + 876798 * 2 ^ 59
def prefixEnd_876798 : Nat := 4983230072969 + 3 ^ 40 * 876798 * 2
def baseEnd_876798 : Nat := 400194498578636228882387

theorem tailTrace_876798 : CollatzResearch.WordTrace tailWord_876798 prefixEnd_876798 400194498578636228882387 := by
  unfold tailWord_876798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997431284689758252710881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21319633518345377347791365 3997431284689758252710881)
  ·
    refine ⟨2998073463517318689533161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3997431284689758252710881 2998073463517318689533161)
    ·
      refine ⟨2248555097637989017149871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2998073463517318689533161 2248555097637989017149871)
      ·
        refine ⟨3372832646456983525724807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248555097637989017149871 3372832646456983525724807)
        ·
          refine ⟨5059248969685475288587211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3372832646456983525724807 5059248969685475288587211)
          ·
            refine ⟨7588873454528212932880817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5059248969685475288587211 7588873454528212932880817)
            ·
              refine ⟨5691655090896159699660613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7588873454528212932880817 5691655090896159699660613)
              ·
                refine ⟨1067185329543029943686365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5691655090896159699660613 1067185329543029943686365)
                ·
                  refine ⟨400194498578636228882387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067185329543029943686365 400194498578636228882387)
                  ·
                    rfl

theorem cell20_876798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_876798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876798 prefixEnd_876798 := by exact prefixLift 876798
  have htrace : WordTrace (prefixWord ++ tailWord_876798) baseStart_876798 baseEnd_876798 := by
    simpa [prefixWord, tailWord_876798, baseEnd_876798] using wordTrace_append hprefix tailTrace_876798
  have hstable : (prefixWord ++ tailWord_876798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876798).length < 2 ^ (prefixWord ++ tailWord_876798).sum := by decide
  have hdescent : baseEnd_876798 < baseStart_876798 := by decide
  rcases family_descends (prefixWord ++ tailWord_876798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876833 : List Nat := [1, 2, 3, 2, 1, 1, 4, 6]
def baseStart_876833 : Nat := 118140960795 + 876833 * 2 ^ 59
def prefixEnd_876833 : Nat := 4983230072969 + 3 ^ 40 * 876833 * 2
def baseEnd_876833 : Nat := 133403491177443887571859

theorem tailTrace_876833 : CollatzResearch.WordTrace tailWord_876833 prefixEnd_876833 133403491177443887571859 := by
  unfold tailWord_876833
  simp only [CollatzResearch.WordTrace]
  refine ⟨31980726832391266999211153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21320484554927511332807435 31980726832391266999211153)
  ·
    refine ⟨23985545124293450249408365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31980726832391266999211153 23985545124293450249408365)
    ·
      refine ⟨8994579421610043843528137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23985545124293450249408365 8994579421610043843528137)
      ·
        refine ⟨6745934566207532882646103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8994579421610043843528137 6745934566207532882646103)
        ·
          refine ⟨10118901849311299323969155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6745934566207532882646103 10118901849311299323969155)
          ·
            refine ⟨15178352773966948985953733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10118901849311299323969155 15178352773966948985953733)
            ·
              refine ⟨2845941145118802934866325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15178352773966948985953733 2845941145118802934866325)
              ·
                refine ⟨133403491177443887571859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2845941145118802934866325 133403491177443887571859)
                ·
                  rfl

theorem cell20_876833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 6].length) (baseStart_876833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876833 prefixEnd_876833 := by exact prefixLift 876833
  have htrace : WordTrace (prefixWord ++ tailWord_876833) baseStart_876833 baseEnd_876833 := by
    simpa [prefixWord, tailWord_876833, baseEnd_876833] using wordTrace_append hprefix tailTrace_876833
  have hstable : (prefixWord ++ tailWord_876833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876833).length < 2 ^ (prefixWord ++ tailWord_876833).sum := by decide
  have hdescent : baseEnd_876833 < baseStart_876833 := by decide
  rcases family_descends (prefixWord ++ tailWord_876833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876850 : List Nat := [3, 2, 1, 1, 6, 7]
def baseStart_876850 : Nat := 118140960795 + 876850 * 2 ^ 59
def prefixEnd_876850 : Nat := 4983230072969 + 3 ^ 40 * 876850 * 2
def baseEnd_876850 : Nat := 14822897510946487375883

theorem tailTrace_876850 : CollatzResearch.WordTrace tailWord_876850 prefixEnd_876850 14822897510946487375883 := by
  unfold tailWord_876850
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995336718332419725645001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21320897915553119268386669 7995336718332419725645001)
  ·
    refine ⟨5996502538749314794233751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7995336718332419725645001 5996502538749314794233751)
    ·
      refine ⟨8994753808123972191350627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5996502538749314794233751 8994753808123972191350627)
      ·
        refine ⟨13492130712185958287025941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8994753808123972191350627 13492130712185958287025941)
        ·
          refine ⟨632443627133716794704341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13492130712185958287025941 632443627133716794704341)
          ·
            refine ⟨14822897510946487375883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 632443627133716794704341 14822897510946487375883)
            ·
              rfl

theorem cell20_876850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 7].length) (baseStart_876850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876850 prefixEnd_876850 := by exact prefixLift 876850
  have htrace : WordTrace (prefixWord ++ tailWord_876850) baseStart_876850 baseEnd_876850 := by
    simpa [prefixWord, tailWord_876850, baseEnd_876850] using wordTrace_append hprefix tailTrace_876850
  have hstable : (prefixWord ++ tailWord_876850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876850).length < 2 ^ (prefixWord ++ tailWord_876850).sum := by decide
  have hdescent : baseEnd_876850 < baseStart_876850 := by decide
  rcases family_descends (prefixWord ++ tailWord_876850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876898 : List Nat := [3, 3, 2, 1, 1, 2, 1, 5, 2]
def baseStart_876898 : Nat := 118140960795 + 876898 * 2 ^ 59
def prefixEnd_876898 : Nat := 4983230072969 + 3 ^ 40 * 876898 * 2
def baseEnd_876898 : Nat := 400240141303480325548645

theorem tailTrace_876898 : CollatzResearch.WordTrace tailWord_876898 prefixEnd_876898 400240141303480325548645 := by
  unfold tailWord_876898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7995774394288945775081837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21322065051437188733551565 7995774394288945775081837)
  ·
    refine ⟨2998415397858354665655689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7995774394288945775081837 2998415397858354665655689)
    ·
      refine ⟨2248811548393765999241767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2998415397858354665655689 2248811548393765999241767)
      ·
        refine ⟨3373217322590648998862651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2248811548393765999241767 3373217322590648998862651)
        ·
          refine ⟨5059825983885973498293977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373217322590648998862651 5059825983885973498293977)
          ·
            refine ⟨3794869487914480123720483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5059825983885973498293977 3794869487914480123720483)
            ·
              refine ⟨5692304231871720185580725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3794869487914480123720483 5692304231871720185580725)
              ·
                refine ⟨533653521737973767398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5692304231871720185580725 533653521737973767398193)
                ·
                  refine ⟨400240141303480325548645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533653521737973767398193 400240141303480325548645)
                  ·
                    rfl

theorem cell20_876898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_876898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876898 prefixEnd_876898 := by exact prefixLift 876898
  have htrace : WordTrace (prefixWord ++ tailWord_876898) baseStart_876898 baseEnd_876898 := by
    simpa [prefixWord, tailWord_876898, baseEnd_876898] using wordTrace_append hprefix tailTrace_876898
  have hstable : (prefixWord ++ tailWord_876898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876898).length < 2 ^ (prefixWord ++ tailWord_876898).sum := by decide
  have hdescent : baseEnd_876898 < baseStart_876898 := by decide
  rcases family_descends (prefixWord ++ tailWord_876898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876909 : List Nat := [1, 5, 1, 1, 1, 2, 9]
def baseStart_876909 : Nat := 118140960795 + 876909 * 2 ^ 59
def prefixEnd_876909 : Nat := 4983230072969 + 3 ^ 40 * 876909 * 2
def baseEnd_876909 : Nat := 44471684667023686242437

theorem tailTrace_876909 : CollatzResearch.WordTrace tailWord_876909 prefixEnd_876909 44471684667023686242437 := by
  unfold tailWord_876909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31983498780115931978977781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21322332520077287985985187 31983498780115931978977781)
  ·
    refine ⟨2998453010635868623029167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31983498780115931978977781 2998453010635868623029167)
    ·
      refine ⟨4497679515953802934543751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2998453010635868623029167 4497679515953802934543751)
      ·
        refine ⟨6746519273930704401815627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4497679515953802934543751 6746519273930704401815627)
        ·
          refine ⟨10119778910896056602723441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6746519273930704401815627 10119778910896056602723441)
          ·
            refine ⟨7589834183172042452042581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10119778910896056602723441 7589834183172042452042581)
            ·
              refine ⟨44471684667023686242437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7589834183172042452042581 44471684667023686242437)
              ·
                rfl

theorem cell20_876909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 9].length) (baseStart_876909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876909 prefixEnd_876909 := by exact prefixLift 876909
  have htrace : WordTrace (prefixWord ++ tailWord_876909) baseStart_876909 baseEnd_876909 := by
    simpa [prefixWord, tailWord_876909, baseEnd_876909] using wordTrace_append hprefix tailTrace_876909
  have hstable : (prefixWord ++ tailWord_876909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876909).length < 2 ^ (prefixWord ++ tailWord_876909).sum := by decide
  have hdescent : baseEnd_876909 < baseStart_876909 := by decide
  rcases family_descends (prefixWord ++ tailWord_876909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876912 : List Nat := [2, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_876912 : Nat := 118140960795 + 876912 * 2 ^ 59
def prefixEnd_876912 : Nat := 4983230072969 + 3 ^ 40 * 876912 * 2
def baseEnd_876912 : Nat := 400246531284958499081921

theorem tailTrace_876912 : CollatzResearch.WordTrace tailWord_876912 prefixEnd_876912 400246531284958499081921 := by
  unfold tailWord_876912
  simp only [CollatzResearch.WordTrace]
  refine ⟨15991804099552531745668495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21322405466070042327557993 15991804099552531745668495)
  ·
    refine ⟨23987706149328797618502743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15991804099552531745668495 23987706149328797618502743)
    ·
      refine ⟨35981559223993196427754115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23987706149328797618502743 35981559223993196427754115)
      ·
        refine ⟨53972338835989794641631173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35981559223993196427754115 53972338835989794641631173)
        ·
          refine ⟨10119813531748086495305845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53972338835989794641631173 10119813531748086495305845)
          ·
            refine ⟨948732518601383108934923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10119813531748086495305845 948732518601383108934923)
            ·
              refine ⟨1423098777902074663402385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948732518601383108934923 1423098777902074663402385)
              ·
                refine ⟨1067324083426555997551789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1423098777902074663402385 1067324083426555997551789)
                ·
                  refine ⟨400246531284958499081921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067324083426555997551789 400246531284958499081921)
                  ·
                    rfl

theorem cell20_876912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_876912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876912 prefixEnd_876912 := by exact prefixLift 876912
  have htrace : WordTrace (prefixWord ++ tailWord_876912) baseStart_876912 baseEnd_876912 := by
    simpa [prefixWord, tailWord_876912, baseEnd_876912] using wordTrace_append hprefix tailTrace_876912
  have hstable : (prefixWord ++ tailWord_876912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876912).length < 2 ^ (prefixWord ++ tailWord_876912).sum := by decide
  have hdescent : baseEnd_876912 < baseStart_876912 := by decide
  rcases family_descends (prefixWord ++ tailWord_876912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876929 : List Nat := [1, 2, 4, 3, 1, 2, 3, 1, 3]
def baseStart_876929 : Nat := 118140960795 + 876929 * 2 ^ 59
def prefixEnd_876929 : Nat := 4983230072969 + 3 ^ 40 * 876929 * 2
def baseEnd_876929 : Nat := 400254290548181995515185

theorem tailTrace_876929 : CollatzResearch.WordTrace tailWord_876929 prefixEnd_876929 400254290548181995515185 := by
  unfold tailWord_876929
  simp only [CollatzResearch.WordTrace]
  refine ⟨31984228240043475394705841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21322818826695650263137227 31984228240043475394705841)
  ·
    refine ⟨23988171180032606546029381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31984228240043475394705841 23988171180032606546029381)
    ·
      refine ⟨4497782096256113727380509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23988171180032606546029381 4497782096256113727380509)
      ·
        refine ⟨1686668286096042647767691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4497782096256113727380509 1686668286096042647767691)
        ·
          refine ⟨2530002429144063971651537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686668286096042647767691 2530002429144063971651537)
          ·
            refine ⟨1897501821858047978738653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530002429144063971651537 1897501821858047978738653)
            ·
              refine ⟨711563183196767992026995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1897501821858047978738653 711563183196767992026995)
              ·
                refine ⟨1067344774795151988040493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711563183196767992026995 1067344774795151988040493)
                ·
                  refine ⟨400254290548181995515185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067344774795151988040493 400254290548181995515185)
                  ·
                    rfl

theorem cell20_876929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3].length) (baseStart_876929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876929 prefixEnd_876929 := by exact prefixLift 876929
  have htrace : WordTrace (prefixWord ++ tailWord_876929) baseStart_876929 baseEnd_876929 := by
    simpa [prefixWord, tailWord_876929, baseEnd_876929] using wordTrace_append hprefix tailTrace_876929
  have hstable : (prefixWord ++ tailWord_876929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876929).length < 2 ^ (prefixWord ++ tailWord_876929).sum := by decide
  have hdescent : baseEnd_876929 < baseStart_876929 := by decide
  rcases family_descends (prefixWord ++ tailWord_876929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876940 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 4]
def baseStart_876940 : Nat := 118140960795 + 876940 * 2 ^ 59
def prefixEnd_876940 : Nat := 4983230072969 + 3 ^ 40 * 876940 * 2
def baseEnd_876940 : Nat := 400259311247914846148473

theorem tailTrace_876940 : CollatzResearch.WordTrace tailWord_876940 prefixEnd_876940 400259311247914846148473 := by
  unfold tailWord_876940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15992314721501812136678137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21323086295335749515570849 15992314721501812136678137)
  ·
    refine ⟨11994236041126359102508603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15992314721501812136678137 11994236041126359102508603)
    ·
      refine ⟨17991354061689538653762905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11994236041126359102508603 17991354061689538653762905)
      ·
        refine ⟨13493515546267153990322179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17991354061689538653762905 13493515546267153990322179)
        ·
          refine ⟨20240273319400730985483269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13493515546267153990322179 20240273319400730985483269)
          ·
            refine ⟨3795051247387637059778113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20240273319400730985483269 3795051247387637059778113)
            ·
              refine ⟨2846288435540727794833585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3795051247387637059778113 2846288435540727794833585)
              ·
                refine ⟨2134716326655545846125189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2846288435540727794833585 2134716326655545846125189)
                ·
                  refine ⟨400259311247914846148473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2134716326655545846125189 400259311247914846148473)
                  ·
                    rfl

theorem cell20_876940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_876940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876940 prefixEnd_876940 := by exact prefixLift 876940
  have htrace : WordTrace (prefixWord ++ tailWord_876940) baseStart_876940 baseEnd_876940 := by
    simpa [prefixWord, tailWord_876940, baseEnd_876940] using wordTrace_append hprefix tailTrace_876940
  have hstable : (prefixWord ++ tailWord_876940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876940).length < 2 ^ (prefixWord ++ tailWord_876940).sum := by decide
  have hdescent : baseEnd_876940 < baseStart_876940 := by decide
  rcases family_descends (prefixWord ++ tailWord_876940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876970 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 4]
def baseStart_876970 : Nat := 118140960795 + 876970 * 2 ^ 59
def prefixEnd_876970 : Nat := 4983230072969 + 3 ^ 40 * 876970 * 2
def baseEnd_876970 : Nat := 400273004065368075148351

theorem tailTrace_876970 : CollatzResearch.WordTrace tailWord_876970 prefixEnd_876970 400273004065368075148351 := by
  unfold tailWord_876970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7996430908223734849237091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21323815755263292931298909 7996430908223734849237091)
  ·
    refine ⟨11994646362335602273855637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7996430908223734849237091 11994646362335602273855637)
    ·
      refine ⟨562249048234481356586983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11994646362335602273855637 562249048234481356586983)
      ·
        refine ⟨843373572351722034880475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 562249048234481356586983 843373572351722034880475)
        ·
          refine ⟨1265060358527583052320713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843373572351722034880475 1265060358527583052320713)
          ·
            refine ⟨948795268895687289240535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265060358527583052320713 948795268895687289240535)
            ·
              refine ⟨1423192903343530933860803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 948795268895687289240535 1423192903343530933860803)
              ·
                refine ⟨2134789355015296400791205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423192903343530933860803 2134789355015296400791205)
                ·
                  refine ⟨400273004065368075148351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2134789355015296400791205 400273004065368075148351)
                  ·
                    rfl

theorem cell20_876970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_876970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876970 prefixEnd_876970 := by exact prefixLift 876970
  have htrace : WordTrace (prefixWord ++ tailWord_876970) baseStart_876970 baseEnd_876970 := by
    simpa [prefixWord, tailWord_876970, baseEnd_876970] using wordTrace_append hprefix tailTrace_876970
  have hstable : (prefixWord ++ tailWord_876970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876970).length < 2 ^ (prefixWord ++ tailWord_876970).sum := by decide
  have hdescent : baseEnd_876970 < baseStart_876970 := by decide
  rcases family_descends (prefixWord ++ tailWord_876970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876980 : List Nat := [2, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_876980 : Nat := 118140960795 + 876980 * 2 ^ 59
def prefixEnd_876980 : Nat := 4983230072969 + 3 ^ 40 * 876980 * 2
def baseEnd_876980 : Nat := 400277568337852484814977

theorem tailTrace_876980 : CollatzResearch.WordTrace tailWord_876980 prefixEnd_876980 400277568337852484814977 := by
  unfold tailWord_876980
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993044181429355552406197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21324058908572474069874929 15993044181429355552406197)
  ·
    refine ⟨1499347892009002083038081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15993044181429355552406197 1499347892009002083038081)
    ·
      refine ⟨1124510919006751562278561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1499347892009002083038081 1124510919006751562278561)
      ·
        refine ⟨843383189255063671708921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124510919006751562278561 843383189255063671708921)
        ·
          refine ⟨632537391941297753781691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843383189255063671708921 632537391941297753781691)
          ·
            refine ⟨948806087911946630672537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632537391941297753781691 948806087911946630672537)
            ·
              refine ⟨711604565933959973004403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948806087911946630672537 711604565933959973004403)
              ·
                refine ⟨1067406848900939959506605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711604565933959973004403 1067406848900939959506605)
                ·
                  refine ⟨400277568337852484814977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067406848900939959506605 400277568337852484814977)
                  ·
                    rfl

theorem cell20_876980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_876980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876980 prefixEnd_876980 := by exact prefixLift 876980
  have htrace : WordTrace (prefixWord ++ tailWord_876980) baseStart_876980 baseEnd_876980 := by
    simpa [prefixWord, tailWord_876980, baseEnd_876980] using wordTrace_append hprefix tailTrace_876980
  have hstable : (prefixWord ++ tailWord_876980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876980).length < 2 ^ (prefixWord ++ tailWord_876980).sum := by decide
  have hdescent : baseEnd_876980 < baseStart_876980 := by decide
  rcases family_descends (prefixWord ++ tailWord_876980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876985 : List Nat := [1, 2, 1, 4, 3, 1, 1, 7]
def baseStart_876985 : Nat := 118140960795 + 876985 * 2 ^ 59
def prefixEnd_876985 : Nat := 4983230072969 + 3 ^ 40 * 876985 * 2
def baseEnd_876985 : Nat := 133426616824698229882763

theorem tailTrace_876985 : CollatzResearch.WordTrace tailWord_876985 prefixEnd_876985 133426616824698229882763 := by
  unfold tailWord_876985
  simp only [CollatzResearch.WordTrace]
  refine ⟨31986270727840596958744409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21324180485227064639162939 31986270727840596958744409)
  ·
    refine ⟨23989703045880447719058307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31986270727840596958744409 23989703045880447719058307)
    ·
      refine ⟨35984554568820671578587461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23989703045880447719058307 35984554568820671578587461)
      ·
        refine ⟨6747103981653875920985149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35984554568820671578587461 6747103981653875920985149)
        ·
          refine ⟨2530163993120203470369431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6747103981653875920985149 2530163993120203470369431)
          ·
            refine ⟨3795245989680305205554147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530163993120203470369431 3795245989680305205554147)
            ·
              refine ⟨5692868984520457808331221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3795245989680305205554147 5692868984520457808331221)
              ·
                refine ⟨133426616824698229882763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5692868984520457808331221 133426616824698229882763)
                ·
                  rfl

theorem cell20_876985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 7].length) (baseStart_876985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876985 prefixEnd_876985 := by exact prefixLift 876985
  have htrace : WordTrace (prefixWord ++ tailWord_876985) baseStart_876985 baseEnd_876985 := by
    simpa [prefixWord, tailWord_876985, baseEnd_876985] using wordTrace_append hprefix tailTrace_876985
  have hstable : (prefixWord ++ tailWord_876985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876985).length < 2 ^ (prefixWord ++ tailWord_876985).sum := by decide
  have hdescent : baseEnd_876985 < baseStart_876985 := by decide
  rcases family_descends (prefixWord ++ tailWord_876985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_876988 : List Nat := [2, 2, 2, 4, 1, 2, 1, 3, 3]
def baseStart_876988 : Nat := 118140960795 + 876988 * 2 ^ 59
def prefixEnd_876988 : Nat := 4983230072969 + 3 ^ 40 * 876988 * 2
def baseEnd_876988 : Nat := 400281219755840012548277

theorem tailTrace_876988 : CollatzResearch.WordTrace tailWord_876988 prefixEnd_876988 400281219755840012548277 := by
  unfold tailWord_876988
  simp only [CollatzResearch.WordTrace]
  refine ⟨15993190073414864235551809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21324253431219818980735745 15993190073414864235551809)
  ·
    refine ⟨11994892555061148176663857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15993190073414864235551809 11994892555061148176663857)
    ·
      refine ⟨8996169416295861132497893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11994892555061148176663857 8996169416295861132497893)
      ·
        refine ⟨1686781765555473962343355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8996169416295861132497893 1686781765555473962343355)
        ·
          refine ⟨2530172648333210943515033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1686781765555473962343355 2530172648333210943515033)
          ·
            refine ⟨1897629486249908207636275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530172648333210943515033 1897629486249908207636275)
            ·
              refine ⟨2846444229374862311454413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897629486249908207636275 2846444229374862311454413)
              ·
                refine ⟨1067416586015573366795405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2846444229374862311454413 1067416586015573366795405)
                ·
                  refine ⟨400281219755840012548277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067416586015573366795405 400281219755840012548277)
                  ·
                    rfl

theorem cell20_876988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_876988 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_876988 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_876988 prefixEnd_876988 := by exact prefixLift 876988
  have htrace : WordTrace (prefixWord ++ tailWord_876988) baseStart_876988 baseEnd_876988 := by
    simpa [prefixWord, tailWord_876988, baseEnd_876988] using wordTrace_append hprefix tailTrace_876988
  have hstable : (prefixWord ++ tailWord_876988).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_876988).length < 2 ^ (prefixWord ++ tailWord_876988).sum := by decide
  have hdescent : baseEnd_876988 < baseStart_876988 := by decide
  rcases family_descends (prefixWord ++ tailWord_876988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877075 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 6]
def baseStart_877075 : Nat := 118140960795 + 877075 * 2 ^ 59
def prefixEnd_877075 : Nat := 4983230072969 + 3 ^ 40 * 877075 * 2
def baseEnd_877075 : Nat := 400320928926454376647921

theorem tailTrace_877075 : CollatzResearch.WordTrace tailWord_877075 prefixEnd_877075 400320928926454376647921 := by
  unfold tailWord_877075
  simp only [CollatzResearch.WordTrace]
  refine ⟨31989553297514542329520679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21326368865009694886347119 31989553297514542329520679)
  ·
    refine ⟨47984329946271813494281019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31989553297514542329520679 47984329946271813494281019)
    ·
      refine ⟨71976494919407720241421529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47984329946271813494281019 71976494919407720241421529)
      ·
        refine ⟨53982371189555790181066147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71976494919407720241421529 53982371189555790181066147)
        ·
          refine ⟨80973556784333685271599221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53982371189555790181066147 80973556784333685271599221)
          ·
            refine ⟨7591270948531282994212427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 80973556784333685271599221 7591270948531282994212427)
            ·
              refine ⟨11386906422796924491318641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7591270948531282994212427 11386906422796924491318641)
              ·
                refine ⟨8540179817097693368488981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11386906422796924491318641 8540179817097693368488981)
                ·
                  refine ⟨400320928926454376647921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8540179817097693368488981 400320928926454376647921)
                  ·
                    rfl

theorem cell20_877075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_877075 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877075 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877075 prefixEnd_877075 := by exact prefixLift 877075
  have htrace : WordTrace (prefixWord ++ tailWord_877075) baseStart_877075 baseEnd_877075 := by
    simpa [prefixWord, tailWord_877075, baseEnd_877075] using wordTrace_append hprefix tailTrace_877075
  have hstable : (prefixWord ++ tailWord_877075).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877075).length < 2 ^ (prefixWord ++ tailWord_877075).sum := by decide
  have hdescent : baseEnd_877075 < baseStart_877075 := by decide
  rcases family_descends (prefixWord ++ tailWord_877075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877085 : List Nat := [1, 4, 2, 2, 1, 3, 1, 1, 5]
def baseStart_877085 : Nat := 118140960795 + 877085 * 2 ^ 59
def prefixEnd_877085 : Nat := 4983230072969 + 3 ^ 40 * 877085 * 2
def baseEnd_877085 : Nat := 400325493198938786314547

theorem tailTrace_877085 : CollatzResearch.WordTrace tailWord_877085 prefixEnd_877085 400325493198938786314547 := by
  unfold tailWord_877085
  simp only [CollatzResearch.WordTrace]
  refine ⟨31989918027478314037384709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21326612018318876024923139 31989918027478314037384709)
  ·
    refine ⟨5998109630152183882009633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31989918027478314037384709 5998109630152183882009633)
    ·
      refine ⟨4498582222614137911507225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5998109630152183882009633 4498582222614137911507225)
      ·
        refine ⟨3373936666960603433630419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4498582222614137911507225 3373936666960603433630419)
        ·
          refine ⟨5060905000440905150445629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3373936666960603433630419 5060905000440905150445629)
          ·
            refine ⟨1897839375165339431417111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5060905000440905150445629 1897839375165339431417111)
            ·
              refine ⟨2846759062748009147125667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1897839375165339431417111 2846759062748009147125667)
              ·
                refine ⟨4270138594122013720688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846759062748009147125667 4270138594122013720688501)
                ·
                  refine ⟨400325493198938786314547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270138594122013720688501 400325493198938786314547)
                  ·
                    rfl

theorem cell20_877085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_877085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877085 prefixEnd_877085 := by exact prefixLift 877085
  have htrace : WordTrace (prefixWord ++ tailWord_877085) baseStart_877085 baseEnd_877085 := by
    simpa [prefixWord, tailWord_877085, baseEnd_877085] using wordTrace_append hprefix tailTrace_877085
  have hstable : (prefixWord ++ tailWord_877085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877085).length < 2 ^ (prefixWord ++ tailWord_877085).sum := by decide
  have hdescent : baseEnd_877085 < baseStart_877085 := by decide
  rcases family_descends (prefixWord ++ tailWord_877085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877116 : List Nat := [2, 2, 2, 2, 3, 1, 4, 4]
def baseStart_877116 : Nat := 118140960795 + 877116 * 2 ^ 59
def prefixEnd_877116 : Nat := 4983230072969 + 3 ^ 40 * 877116 * 2
def baseEnd_877116 : Nat := 133446547481213485427029

theorem tailTrace_877116 : CollatzResearch.WordTrace tailWord_877116 prefixEnd_877116 133446547481213485427029 := by
  unfold tailWord_877116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15995524345183003165881601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21327365793577337554508801 15995524345183003165881601)
  ·
    refine ⟨11996643258887252374411201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15995524345183003165881601 11996643258887252374411201)
    ·
      refine ⟨8997482444165439280808401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11996643258887252374411201 8997482444165439280808401)
      ·
        refine ⟨6748111833124079460606301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8997482444165439280808401 6748111833124079460606301)
        ·
          refine ⟨2530541937421529797727363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6748111833124079460606301 2530541937421529797727363)
          ·
            refine ⟨3795812906132294696591045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2530541937421529797727363 3795812906132294696591045)
            ·
              refine ⟨711714919899805255610821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3795812906132294696591045 711714919899805255610821)
              ·
                refine ⟨133446547481213485427029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711714919899805255610821 133446547481213485427029)
                ·
                  rfl

theorem cell20_877116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 4, 4].length) (baseStart_877116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877116 prefixEnd_877116 := by exact prefixLift 877116
  have htrace : WordTrace (prefixWord ++ tailWord_877116) baseStart_877116 baseEnd_877116 := by
    simpa [prefixWord, tailWord_877116, baseEnd_877116] using wordTrace_append hprefix tailTrace_877116
  have hstable : (prefixWord ++ tailWord_877116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877116).length < 2 ^ (prefixWord ++ tailWord_877116).sum := by decide
  have hdescent : baseEnd_877116 < baseStart_877116 := by decide
  rcases family_descends (prefixWord ++ tailWord_877116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877137 : List Nat := [1, 2, 2, 1, 3, 5, 6]
def baseStart_877137 : Nat := 118140960795 + 877137 * 2 ^ 59
def prefixEnd_877137 : Nat := 4983230072969 + 3 ^ 40 * 877137 * 2
def baseEnd_877137 : Nat := 44483247490650857397889

theorem tailTrace_877137 : CollatzResearch.WordTrace tailWord_877137 prefixEnd_877137 44483247490650857397889 := by
  unfold tailWord_877137
  simp only [CollatzResearch.WordTrace]
  refine ⟨31991814623289926918277665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21327876415526617945518443 31991814623289926918277665)
  ·
    refine ⟨23993860967467445188708249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31991814623289926918277665 23993860967467445188708249)
    ·
      refine ⟨17995395725600583891531187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23993860967467445188708249 17995395725600583891531187)
      ·
        refine ⟨26993093588400875837296781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17995395725600583891531187 26993093588400875837296781)
        ·
          refine ⟨10122410095650328438986293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26993093588400875837296781 10122410095650328438986293)
          ·
            refine ⟨948975946467218291154965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10122410095650328438986293 948975946467218291154965)
            ·
              refine ⟨44483247490650857397889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 948975946467218291154965 44483247490650857397889)
              ·
                rfl

theorem cell20_877137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_877137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877137 prefixEnd_877137 := by exact prefixLift 877137
  have htrace : WordTrace (prefixWord ++ tailWord_877137) baseStart_877137 baseEnd_877137 := by
    simpa [prefixWord, tailWord_877137, baseEnd_877137] using wordTrace_append hprefix tailTrace_877137
  have hstable : (prefixWord ++ tailWord_877137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877137).length < 2 ^ (prefixWord ++ tailWord_877137).sum := by decide
  have hdescent : baseEnd_877137 < baseStart_877137 := by decide
  rcases family_descends (prefixWord ++ tailWord_877137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877144 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_877144 : Nat := 118140960795 + 877144 * 2 ^ 59
def prefixEnd_877144 : Nat := 4983230072969 + 3 ^ 40 * 877144 * 2
def baseEnd_877144 : Nat := 400352422406596803347639

theorem tailTrace_877144 : CollatzResearch.WordTrace tailWord_877144 prefixEnd_877144 400352422406596803347639 := by
  unfold tailWord_877144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15996034967132283556891243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21328046622843044742521657 15996034967132283556891243)
  ·
    refine ⟨23994052450698425335336865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15996034967132283556891243 23994052450698425335336865)
    ·
      refine ⟨17995539338023819001502649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23994052450698425335336865 17995539338023819001502649)
      ·
        refine ⟨13496654503517864251126987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17995539338023819001502649 13496654503517864251126987)
        ·
          refine ⟨20244981755276796376690481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13496654503517864251126987 20244981755276796376690481)
          ·
            refine ⟨15183736316457597282517861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20244981755276796376690481 15183736316457597282517861)
            ·
              refine ⟨2846950559335799490472099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15183736316457597282517861 2846950559335799490472099)
              ·
                refine ⟨4270425839003699235708149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2846950559335799490472099 4270425839003699235708149)
                ·
                  refine ⟨400352422406596803347639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4270425839003699235708149 400352422406596803347639)
                  ·
                    rfl

theorem cell20_877144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_877144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877144 prefixEnd_877144 := by exact prefixLift 877144
  have htrace : WordTrace (prefixWord ++ tailWord_877144) baseStart_877144 baseEnd_877144 := by
    simpa [prefixWord, tailWord_877144, baseEnd_877144] using wordTrace_append hprefix tailTrace_877144
  have hstable : (prefixWord ++ tailWord_877144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877144).length < 2 ^ (prefixWord ++ tailWord_877144).sum := by decide
  have hdescent : baseEnd_877144 < baseStart_877144 := by decide
  rcases family_descends (prefixWord ++ tailWord_877144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877157 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 3]
def baseStart_877157 : Nat := 118140960795 + 877157 * 2 ^ 59
def prefixEnd_877157 : Nat := 4983230072969 + 3 ^ 40 * 877157 * 2
def baseEnd_877157 : Nat := 400358355960826535914253

theorem tailTrace_877157 : CollatzResearch.WordTrace tailWord_877157 prefixEnd_877157 400358355960826535914253 := by
  unfold tailWord_877157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31992544083217470334005725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21328362722144980222670483 31992544083217470334005725)
  ·
    refine ⟨11997204031206551375252147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31992544083217470334005725 11997204031206551375252147)
    ·
      refine ⟨17995806046809827062878221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11997204031206551375252147 17995806046809827062878221)
      ·
        refine ⟨6748427267553685148579333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17995806046809827062878221 6748427267553685148579333)
        ·
          refine ⟨1265330112666315965358625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6748427267553685148579333 1265330112666315965358625)
          ·
            refine ⟨948997584499736974018969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265330112666315965358625 948997584499736974018969)
            ·
              refine ⟨711748188374802730514227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 948997584499736974018969 711748188374802730514227)
              ·
                refine ⟨1067622282562204095771341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 711748188374802730514227 1067622282562204095771341)
                ·
                  refine ⟨400358355960826535914253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1067622282562204095771341 400358355960826535914253)
                  ·
                    rfl

theorem cell20_877157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_877157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877157 prefixEnd_877157 := by exact prefixLift 877157
  have htrace : WordTrace (prefixWord ++ tailWord_877157) baseStart_877157 baseEnd_877157 := by
    simpa [prefixWord, tailWord_877157, baseEnd_877157] using wordTrace_append hprefix tailTrace_877157
  have hstable : (prefixWord ++ tailWord_877157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877157).length < 2 ^ (prefixWord ++ tailWord_877157).sum := by decide
  have hdescent : baseEnd_877157 < baseStart_877157 := by decide
  rcases family_descends (prefixWord ++ tailWord_877157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877185 : List Nat := [1, 2, 4, 2, 1, 1, 2, 5, 2]
def baseStart_877185 : Nat := 118140960795 + 877185 * 2 ^ 59
def prefixEnd_877185 : Nat := 4983230072969 + 3 ^ 40 * 877185 * 2
def baseEnd_877185 : Nat := 400371135923782882980805

theorem tailTrace_877185 : CollatzResearch.WordTrace tailWord_877185 prefixEnd_877185 400371135923782882980805 := by
  unfold tailWord_877185
  simp only [CollatzResearch.WordTrace]
  refine ⟨31993565327116031116025009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21329043551410687410683339 31993565327116031116025009)
  ·
    refine ⟨23995173995337023337018757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31993565327116031116025009 23995173995337023337018757)
    ·
      refine ⟨4499095124125691875691017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23995173995337023337018757 4499095124125691875691017)
      ·
        refine ⟨3374321343094268906768263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499095124125691875691017 3374321343094268906768263)
        ·
          refine ⟨5061482014641403360152395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374321343094268906768263 5061482014641403360152395)
          ·
            refine ⟨7592223021962105040228593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5061482014641403360152395 7592223021962105040228593)
            ·
              refine ⟨5694167266471578780171445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7592223021962105040228593 5694167266471578780171445)
              ·
                refine ⟨533828181231710510641073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5694167266471578780171445 533828181231710510641073)
                ·
                  refine ⟨400371135923782882980805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533828181231710510641073 400371135923782882980805)
                  ·
                    rfl

theorem cell20_877185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_877185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877185 prefixEnd_877185 := by exact prefixLift 877185
  have htrace : WordTrace (prefixWord ++ tailWord_877185) baseStart_877185 baseEnd_877185 := by
    simpa [prefixWord, tailWord_877185, baseEnd_877185] using wordTrace_append hprefix tailTrace_877185
  have hstable : (prefixWord ++ tailWord_877185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877185).length < 2 ^ (prefixWord ++ tailWord_877185).sum := by decide
  have hdescent : baseEnd_877185 < baseStart_877185 := by decide
  rcases family_descends (prefixWord ++ tailWord_877185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877202 : List Nat := [3, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_877202 : Nat := 118140960795 + 877202 * 2 ^ 59
def prefixEnd_877202 : Nat := 4983230072969 + 3 ^ 40 * 877202 * 2
def baseEnd_877202 : Nat := 400378895187006379414069

theorem tailTrace_877202 : CollatzResearch.WordTrace tailWord_877202 prefixEnd_877202 400378895187006379414069 := by
  unfold tailWord_877202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998546342013610754848465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21329456912036295346262573 7998546342013610754848465)
  ·
    refine ⟨5998909756510208066136349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7998546342013610754848465 5998909756510208066136349)
    ·
      refine ⟨2249591158691328024801131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5998909756510208066136349 2249591158691328024801131)
      ·
        refine ⟨3374386738036992037201697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2249591158691328024801131 3374386738036992037201697)
        ·
          refine ⟨2530790053527744027901273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3374386738036992037201697 2530790053527744027901273)
          ·
            refine ⟨1898092540145808020925955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2530790053527744027901273 1898092540145808020925955)
            ·
              refine ⟨2847138810218712031388933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898092540145808020925955 2847138810218712031388933)
              ·
                refine ⟨533838526916008505885425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847138810218712031388933 533838526916008505885425)
                ·
                  refine ⟨400378895187006379414069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533838526916008505885425 400378895187006379414069)
                  ·
                    rfl

theorem cell20_877202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_877202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877202 prefixEnd_877202 := by exact prefixLift 877202
  have htrace : WordTrace (prefixWord ++ tailWord_877202) baseStart_877202 baseEnd_877202 := by
    simpa [prefixWord, tailWord_877202, baseEnd_877202] using wordTrace_append hprefix tailTrace_877202
  have hstable : (prefixWord ++ tailWord_877202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877202).length < 2 ^ (prefixWord ++ tailWord_877202).sum := by decide
  have hdescent : baseEnd_877202 < baseStart_877202 := by decide
  rcases family_descends (prefixWord ++ tailWord_877202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877213 : List Nat := [1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_877213 : Nat := 118140960795 + 877213 * 2 ^ 59
def prefixEnd_877213 : Nat := 4983230072969 + 3 ^ 40 * 877213 * 2
def baseEnd_877213 : Nat := 133461305295579743349119

theorem tailTrace_877213 : CollatzResearch.WordTrace tailWord_877213 prefixEnd_877213 133461305295579743349119 := by
  unfold tailWord_877213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31994586571014591898044293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21329724380676394598696195 31994586571014591898044293)
  ·
    refine ⟨5998984982065235980883305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31994586571014591898044293 5998984982065235980883305)
    ·
      refine ⟨4499238736548926985662479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5998984982065235980883305 4499238736548926985662479)
      ·
        refine ⟨6748858104823390478493719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4499238736548926985662479 6748858104823390478493719)
        ·
          refine ⟨10123287157235085717740579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6748858104823390478493719 10123287157235085717740579)
          ·
            refine ⟨15184930735852628576610869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10123287157235085717740579 15184930735852628576610869)
            ·
              refine ⟨1423587256486183929057269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15184930735852628576610869 1423587256486183929057269)
              ·
                refine ⟨133461305295579743349119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1423587256486183929057269 133461305295579743349119)
                ·
                  rfl

theorem cell20_877213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_877213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877213 prefixEnd_877213 := by exact prefixLift 877213
  have htrace : WordTrace (prefixWord ++ tailWord_877213) baseStart_877213 baseEnd_877213 := by
    simpa [prefixWord, tailWord_877213, baseEnd_877213] using wordTrace_append hprefix tailTrace_877213
  have hstable : (prefixWord ++ tailWord_877213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877213).length < 2 ^ (prefixWord ++ tailWord_877213).sum := by decide
  have hdescent : baseEnd_877213 < baseStart_877213 := by decide
  rcases family_descends (prefixWord ++ tailWord_877213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877226 : List Nat := [3, 1, 5, 2, 1, 1, 3, 4]
def baseStart_877226 : Nat := 118140960795 + 877226 * 2 ^ 59
def prefixEnd_877226 : Nat := 4983230072969 + 3 ^ 40 * 877226 * 2
def baseEnd_877226 : Nat := 133463283146989654204657

theorem tailTrace_877226 : CollatzResearch.WordTrace tailWord_877226 prefixEnd_877226 133463283146989654204657 := by
  unfold tailWord_877226
  simp only [CollatzResearch.WordTrace]
  refine ⟨7998765179991873779566883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21330040479978330078845021 7998765179991873779566883)
  ·
    refine ⟨11998147769987810669350325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7998765179991873779566883 11998147769987810669350325)
    ·
      refine ⟨1124826353436357250251593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11998147769987810669350325 1124826353436357250251593)
      ·
        refine ⟨843619765077267937688695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1124826353436357250251593 843619765077267937688695)
        ·
          refine ⟨1265429647615901906533043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 843619765077267937688695 1265429647615901906533043)
          ·
            refine ⟨1898144471423852859799565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265429647615901906533043 1898144471423852859799565)
            ·
              refine ⟨711804176783944822424837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1898144471423852859799565 711804176783944822424837)
              ·
                refine ⟨133463283146989654204657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711804176783944822424837 133463283146989654204657)
                ·
                  rfl

theorem cell20_877226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_877226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877226 prefixEnd_877226 := by exact prefixLift 877226
  have htrace : WordTrace (prefixWord ++ tailWord_877226) baseStart_877226 baseEnd_877226 := by
    simpa [prefixWord, tailWord_877226, baseEnd_877226] using wordTrace_append hprefix tailTrace_877226
  have hstable : (prefixWord ++ tailWord_877226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877226).length < 2 ^ (prefixWord ++ tailWord_877226).sum := by decide
  have hdescent : baseEnd_877226 < baseStart_877226 := by decide
  rcases family_descends (prefixWord ++ tailWord_877226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877289 : List Nat := [1, 2, 1, 1, 1, 2, 8, 4]
def baseStart_877289 : Nat := 118140960795 + 877289 * 2 ^ 59
def prefixEnd_877289 : Nat := 4983230072969 + 3 ^ 40 * 877289 * 2
def baseEnd_877289 : Nat := 133472868119206914504571

theorem tailTrace_877289 : CollatzResearch.WordTrace tailWord_877289 prefixEnd_877289 133472868119206914504571 := by
  unfold tailWord_877289
  simp only [CollatzResearch.WordTrace]
  refine ⟨31997358518739256877810921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21331572345826171251873947 31997358518739256877810921)
  ·
    refine ⟨23998018889054442658358191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31997358518739256877810921 23998018889054442658358191)
    ·
      refine ⟨35997028333581663987537287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23998018889054442658358191 35997028333581663987537287)
      ·
        refine ⟨53995542500372495981305931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35997028333581663987537287 53995542500372495981305931)
        ·
          refine ⟨80993313750558743971958897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53995542500372495981305931 80993313750558743971958897)
          ·
            refine ⟨60744985312919057978969173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80993313750558743971958897 60744985312919057978969173)
            ·
              refine ⟨711855296635770210691045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 60744985312919057978969173 711855296635770210691045)
              ·
                refine ⟨133472868119206914504571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 711855296635770210691045 133472868119206914504571)
                ·
                  rfl

theorem cell20_877289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 4].length) (baseStart_877289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877289 prefixEnd_877289 := by exact prefixLift 877289
  have htrace : WordTrace (prefixWord ++ tailWord_877289) baseStart_877289 baseEnd_877289 := by
    simpa [prefixWord, tailWord_877289, baseEnd_877289] using wordTrace_append hprefix tailTrace_877289
  have hstable : (prefixWord ++ tailWord_877289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877289).length < 2 ^ (prefixWord ++ tailWord_877289).sum := by decide
  have hdescent : baseEnd_877289 < baseStart_877289 := by decide
  rcases family_descends (prefixWord ++ tailWord_877289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877316 : List Nat := [2, 3, 2, 2, 1, 1, 5, 2, 2]
def baseStart_877316 : Nat := 118140960795 + 877316 * 2 ^ 59
def prefixEnd_877316 : Nat := 4983230072969 + 3 ^ 40 * 877316 * 2
def baseEnd_877316 : Nat := 400430927893328649613603

theorem tailTrace_877316 : CollatzResearch.WordTrace tailWord_877316 prefixEnd_877316 400430927893328649613603 := by
  unfold tailWord_877316
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999171644820720244521901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21332228859760960326029201 15999171644820720244521901)
  ·
    refine ⟨5999689366807770091695713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15999171644820720244521901 5999689366807770091695713)
    ·
      refine ⟨4499767025105827568771785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5999689366807770091695713 4499767025105827568771785)
      ·
        refine ⟨3374825268829370676578839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4499767025105827568771785 3374825268829370676578839)
        ·
          refine ⟨5062237903244056014868259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3374825268829370676578839 5062237903244056014868259)
          ·
            refine ⟨7593356854866084022302389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5062237903244056014868259 7593356854866084022302389)
            ·
              refine ⟨711877205143695377090849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7593356854866084022302389 711877205143695377090849)
              ·
                refine ⟨533907903857771532818137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 711877205143695377090849 533907903857771532818137)
                ·
                  refine ⟨400430927893328649613603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533907903857771532818137 400430927893328649613603)
                  ·
                    rfl

theorem cell20_877316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_877316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877316 prefixEnd_877316 := by exact prefixLift 877316
  have htrace : WordTrace (prefixWord ++ tailWord_877316) baseStart_877316 baseEnd_877316 := by
    simpa [prefixWord, tailWord_877316, baseEnd_877316] using wordTrace_append hprefix tailTrace_877316
  have hstable : (prefixWord ++ tailWord_877316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877316).length < 2 ^ (prefixWord ++ tailWord_877316).sum := by decide
  have hdescent : baseEnd_877316 < baseStart_877316 := by decide
  rcases family_descends (prefixWord ++ tailWord_877316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877320 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_877320 : Nat := 118140960795 + 877320 * 2 ^ 59
def prefixEnd_877320 : Nat := 4983230072969 + 3 ^ 40 * 877320 * 2
def baseEnd_877320 : Nat := 400432753602322413480253

theorem tailTrace_877320 : CollatzResearch.WordTrace tailWord_877320 prefixEnd_877320 400432753602322413480253 := by
  unfold tailWord_877320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15999244590813474586094707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21332326121084632781459609 15999244590813474586094707)
  ·
    refine ⟨23998866886220211879142061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15999244590813474586094707 23998866886220211879142061)
    ·
      refine ⟨8999575082332579454678273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23998866886220211879142061 8999575082332579454678273)
      ·
        refine ⟨6749681311749434591008705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8999575082332579454678273 6749681311749434591008705)
        ·
          refine ⟨5062260983812075943256529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6749681311749434591008705 5062260983812075943256529)
          ·
            refine ⟨3796695737859056957442397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5062260983812075943256529 3796695737859056957442397)
            ·
              refine ⟨1423760901697146359040899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3796695737859056957442397 1423760901697146359040899)
              ·
                refine ⟨2135641352545719538561349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1423760901697146359040899 2135641352545719538561349)
                ·
                  refine ⟨400432753602322413480253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135641352545719538561349 400432753602322413480253)
                  ·
                    rfl

theorem cell20_877320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_877320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877320 prefixEnd_877320 := by exact prefixLift 877320
  have htrace : WordTrace (prefixWord ++ tailWord_877320) baseStart_877320 baseEnd_877320 := by
    simpa [prefixWord, tailWord_877320, baseEnd_877320] using wordTrace_append hprefix tailTrace_877320
  have hstable : (prefixWord ++ tailWord_877320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877320).length < 2 ^ (prefixWord ++ tailWord_877320).sum := by decide
  have hdescent : baseEnd_877320 < baseStart_877320 := by decide
  rcases family_descends (prefixWord ++ tailWord_877320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877375 : List Nat := [1, 1, 2, 2, 5, 2, 1, 4, 2]
def baseStart_877375 : Nat := 118140960795 + 877375 * 2 ^ 59
def prefixEnd_877375 : Nat := 4983230072969 + 3 ^ 40 * 877375 * 2
def baseEnd_877375 : Nat := 400457857100986666646695

theorem tailTrace_877375 : CollatzResearch.WordTrace tailWord_877375 prefixEnd_877375 400457857100986666646695 := by
  unfold tailWord_877375
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000495196427693565441579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21333663464285129043627719 32000495196427693565441579)
  ·
    refine ⟨48000742794641540348162369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32000495196427693565441579 48000742794641540348162369)
    ·
      refine ⟨36000557095981155261121777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48000742794641540348162369 36000557095981155261121777)
      ·
        refine ⟨27000417821985866445841333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36000557095981155261121777 27000417821985866445841333)
        ·
          refine ⟨2531289170811174979297625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27000417821985866445841333 2531289170811174979297625)
          ·
            refine ⟨1898466878108381234473219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2531289170811174979297625 1898466878108381234473219)
            ·
              refine ⟨2847700317162571851709829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898466878108381234473219 2847700317162571851709829)
              ·
                refine ⟨533943809467982222195593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847700317162571851709829 533943809467982222195593)
                ·
                  refine ⟨400457857100986666646695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533943809467982222195593 400457857100986666646695)
                  ·
                    rfl

theorem cell20_877375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 4, 2].length) (baseStart_877375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877375 prefixEnd_877375 := by exact prefixLift 877375
  have htrace : WordTrace (prefixWord ++ tailWord_877375) baseStart_877375 baseEnd_877375 := by
    simpa [prefixWord, tailWord_877375, baseEnd_877375] using wordTrace_append hprefix tailTrace_877375
  have hstable : (prefixWord ++ tailWord_877375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877375).length < 2 ^ (prefixWord ++ tailWord_877375).sum := by decide
  have hdescent : baseEnd_877375 < baseStart_877375 := by decide
  rcases family_descends (prefixWord ++ tailWord_877375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877379 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 4]
def baseStart_877379 : Nat := 118140960795 + 877379 * 2 ^ 59
def prefixEnd_877379 : Nat := 4983230072969 + 3 ^ 40 * 877379 * 2
def baseEnd_877379 : Nat := 400459682809980430513345

theorem tailTrace_877379 : CollatzResearch.WordTrace tailWord_877379 prefixEnd_877379 400459682809980430513345 := by
  unfold tailWord_877379
  simp only [CollatzResearch.WordTrace]
  refine ⟨32000641088413202248587191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21333760725608801499058127 32000641088413202248587191)
  ·
    refine ⟨48000961632619803372880787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32000641088413202248587191 48000961632619803372880787)
    ·
      refine ⟨72001442448929705059321181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48000961632619803372880787 72001442448929705059321181)
      ·
        refine ⟨27000540918348639397245443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 72001442448929705059321181 27000540918348639397245443)
        ·
          refine ⟨40500811377522959095868165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27000540918348639397245443 40500811377522959095868165)
          ·
            refine ⟨7593902133285554830475281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40500811377522959095868165 7593902133285554830475281)
            ·
              refine ⟨5695426599964166122856461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7593902133285554830475281 5695426599964166122856461)
              ·
                refine ⟨2135784974986562296071173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5695426599964166122856461 2135784974986562296071173)
                ·
                  refine ⟨400459682809980430513345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2135784974986562296071173 400459682809980430513345)
                  ·
                    rfl

theorem cell20_877379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_877379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877379 prefixEnd_877379 := by exact prefixLift 877379
  have htrace : WordTrace (prefixWord ++ tailWord_877379) baseStart_877379 baseEnd_877379 := by
    simpa [prefixWord, tailWord_877379, baseEnd_877379] using wordTrace_append hprefix tailTrace_877379
  have hstable : (prefixWord ++ tailWord_877379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877379).length < 2 ^ (prefixWord ++ tailWord_877379).sum := by decide
  have hdescent : baseEnd_877379 < baseStart_877379 := by decide
  rcases family_descends (prefixWord ++ tailWord_877379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877386 : List Nat := [3, 1, 2, 1, 1, 1, 2, 9]
def baseStart_877386 : Nat := 118140960795 + 877386 * 2 ^ 59
def prefixEnd_877386 : Nat := 4983230072969 + 3 ^ 40 * 877386 * 2
def baseEnd_877386 : Nat := 133487625933573172426661

theorem tailTrace_877386 : CollatzResearch.WordTrace tailWord_877386 prefixEnd_877386 133487625933573172426661 := by
  unfold tailWord_877386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000224099846960611023003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21333930932925228296061341 8000224099846960611023003)
  ·
    refine ⟨12000336149770440916534505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000224099846960611023003 12000336149770440916534505)
    ·
      refine ⟨9000252112327830687400879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12000336149770440916534505 9000252112327830687400879)
      ·
        refine ⟨13500378168491746031101319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9000252112327830687400879 13500378168491746031101319)
        ·
          refine ⟨20250567252737619046651979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13500378168491746031101319 20250567252737619046651979)
          ·
            refine ⟨30375850879106428569977969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20250567252737619046651979 30375850879106428569977969)
            ·
              refine ⟨22781888159329821427483477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30375850879106428569977969 22781888159329821427483477)
              ·
                refine ⟨133487625933573172426661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22781888159329821427483477 133487625933573172426661)
                ·
                  rfl

theorem cell20_877386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_877386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877386 prefixEnd_877386 := by exact prefixLift 877386
  have htrace : WordTrace (prefixWord ++ tailWord_877386) baseStart_877386 baseEnd_877386 := by
    simpa [prefixWord, tailWord_877386, baseEnd_877386] using wordTrace_append hprefix tailTrace_877386
  have hstable : (prefixWord ++ tailWord_877386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877386).length < 2 ^ (prefixWord ++ tailWord_877386).sum := by decide
  have hdescent : baseEnd_877386 < baseStart_877386 := by decide
  rcases family_descends (prefixWord ++ tailWord_877386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877430 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_877430 : Nat := 118140960795 + 877430 * 2 ^ 59
def prefixEnd_877430 : Nat := 4983230072969 + 3 ^ 40 * 877430 * 2
def baseEnd_877430 : Nat := 400482960599650919813137

theorem tailTrace_877430 : CollatzResearch.WordTrace tailWord_877430 prefixEnd_877430 400482960599650919813137 := by
  unfold tailWord_877430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000156325701777372418359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21335000807485625305795829 2000156325701777372418359)
  ·
    refine ⟨3000234488552666058627539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2000156325701777372418359 3000234488552666058627539)
    ·
      refine ⟨4500351732828999087941309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000234488552666058627539 4500351732828999087941309)
      ·
        refine ⟨1687631899810874657977991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4500351732828999087941309 1687631899810874657977991)
        ·
          refine ⟨2531447849716311986966987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1687631899810874657977991 2531447849716311986966987)
          ·
            refine ⟨3797171774574467980450481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2531447849716311986966987 3797171774574467980450481)
            ·
              refine ⟨2847878830930850985337861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3797171774574467980450481 2847878830930850985337861)
              ·
                refine ⟨533977280799534559750849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2847878830930850985337861 533977280799534559750849)
                ·
                  refine ⟨400482960599650919813137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 533977280799534559750849 400482960599650919813137)
                  ·
                    rfl

theorem cell20_877430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_877430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877430 prefixEnd_877430 := by exact prefixLift 877430
  have htrace : WordTrace (prefixWord ++ tailWord_877430) baseStart_877430 baseEnd_877430 := by
    simpa [prefixWord, tailWord_877430, baseEnd_877430] using wordTrace_append hprefix tailTrace_877430
  have hstable : (prefixWord ++ tailWord_877430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877430).length < 2 ^ (prefixWord ++ tailWord_877430).sum := by decide
  have hdescent : baseEnd_877430 < baseStart_877430 := by decide
  rcases family_descends (prefixWord ++ tailWord_877430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877458 : List Nat := [3, 2, 3, 2, 2, 1, 1, 6]
def baseStart_877458 : Nat := 118140960795 + 877458 * 2 ^ 59
def prefixEnd_877458 : Nat := 4983230072969 + 3 ^ 40 * 877458 * 2
def baseEnd_877458 : Nat := 133498580187535755626563

theorem tailTrace_877458 : CollatzResearch.WordTrace tailWord_877458 prefixEnd_877458 133498580187535755626563 := by
  unfold tailWord_877458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000880613781749685178257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21335681636751332493808685 8000880613781749685178257)
  ·
    refine ⟨6000660460336312263883693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8000880613781749685178257 6000660460336312263883693)
    ·
      refine ⟨2250247672626117098956385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6000660460336312263883693 2250247672626117098956385)
      ·
        refine ⟨1687685754469587824217289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2250247672626117098956385 1687685754469587824217289)
        ·
          refine ⟨1265764315852190868162967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1687685754469587824217289 1265764315852190868162967)
          ·
            refine ⟨1898646473778286302244451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1265764315852190868162967 1898646473778286302244451)
            ·
              refine ⟨2847969710667429453366677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1898646473778286302244451 2847969710667429453366677)
              ·
                refine ⟨133498580187535755626563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2847969710667429453366677 133498580187535755626563)
                ·
                  rfl

theorem cell20_877458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_877458 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877458 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877458 prefixEnd_877458 := by exact prefixLift 877458
  have htrace : WordTrace (prefixWord ++ tailWord_877458) baseStart_877458 baseEnd_877458 := by
    simpa [prefixWord, tailWord_877458, baseEnd_877458] using wordTrace_append hprefix tailTrace_877458
  have hstable : (prefixWord ++ tailWord_877458).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877458).length < 2 ^ (prefixWord ++ tailWord_877458).sum := by decide
  have hdescent : baseEnd_877458 < baseStart_877458 := by decide
  rcases family_descends (prefixWord ++ tailWord_877458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877485 : List Nat := [1, 5, 2, 3, 2, 1, 1, 1, 4]
def baseStart_877485 : Nat := 118140960795 + 877485 * 2 ^ 59
def prefixEnd_877485 : Nat := 4983230072969 + 3 ^ 40 * 877485 * 2
def baseEnd_877485 : Nat := 400508064098315172979579

theorem tailTrace_877485 : CollatzResearch.WordTrace tailWord_877485 prefixEnd_877485 400508064098315172979579 := by
  unfold tailWord_877485
  simp only [CollatzResearch.WordTrace]
  refine ⟨32004507226029182351945909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21336338150686121567963939 32004507226029182351945909)
  ·
    refine ⟨3000422552440235845494929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32004507226029182351945909 3000422552440235845494929)
    ·
      refine ⟨2250316914330176884121197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3000422552440235845494929 2250316914330176884121197)
      ·
        refine ⟨843868842873816331545449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2250316914330176884121197 843868842873816331545449)
        ·
          refine ⟨632901632155362248659087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843868842873816331545449 632901632155362248659087)
          ·
            refine ⟨949352448233043372988631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 632901632155362248659087 949352448233043372988631)
            ·
              refine ⟨1424028672349565059482947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949352448233043372988631 1424028672349565059482947)
              ·
                refine ⟨2136043008524347589224421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424028672349565059482947 2136043008524347589224421)
                ·
                  refine ⟨400508064098315172979579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136043008524347589224421 400508064098315172979579)
                  ·
                    rfl

theorem cell20_877485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_877485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877485 prefixEnd_877485 := by exact prefixLift 877485
  have htrace : WordTrace (prefixWord ++ tailWord_877485) baseStart_877485 baseEnd_877485 := by
    simpa [prefixWord, tailWord_877485, baseEnd_877485] using wordTrace_append hprefix tailTrace_877485
  have hstable : (prefixWord ++ tailWord_877485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877485).length < 2 ^ (prefixWord ++ tailWord_877485).sum := by decide
  have hdescent : baseEnd_877485 < baseStart_877485 := by decide
  rcases family_descends (prefixWord ++ tailWord_877485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877489 : List Nat := [1, 2, 2, 4, 3, 2, 1, 1, 4]
def baseStart_877489 : Nat := 118140960795 + 877489 * 2 ^ 59
def prefixEnd_877489 : Nat := 4983230072969 + 3 ^ 40 * 877489 * 2
def baseEnd_877489 : Nat := 400509889807308936846229

theorem tailTrace_877489 : CollatzResearch.WordTrace tailWord_877489 prefixEnd_877489 400509889807308936846229 := by
  unfold tailWord_877489
  simp only [CollatzResearch.WordTrace]
  refine ⟨32004653118014691035091521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21336435412009794023394347 32004653118014691035091521)
  ·
    refine ⟨24003489838511018276318641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32004653118014691035091521 24003489838511018276318641)
    ·
      refine ⟨18002617378883263707238981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24003489838511018276318641 18002617378883263707238981)
      ·
        refine ⟨3375490758540611945107309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18002617378883263707238981 3375490758540611945107309)
        ·
          refine ⟨1265809034452729479415241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3375490758540611945107309 1265809034452729479415241)
          ·
            refine ⟨949356775839547109561431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265809034452729479415241 949356775839547109561431)
            ·
              refine ⟨1424035163759320664342147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949356775839547109561431 1424035163759320664342147)
              ·
                refine ⟨2136052745638980996513221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424035163759320664342147 2136052745638980996513221)
                ·
                  refine ⟨400509889807308936846229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136052745638980996513221 400509889807308936846229)
                  ·
                    rfl

theorem cell20_877489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 4].length) (baseStart_877489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877489 prefixEnd_877489 := by exact prefixLift 877489
  have htrace : WordTrace (prefixWord ++ tailWord_877489) baseStart_877489 baseEnd_877489 := by
    simpa [prefixWord, tailWord_877489, baseEnd_877489] using wordTrace_append hprefix tailTrace_877489
  have hstable : (prefixWord ++ tailWord_877489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877489).length < 2 ^ (prefixWord ++ tailWord_877489).sum := by decide
  have hdescent : baseEnd_877489 < baseStart_877489 := by decide
  rcases family_descends (prefixWord ++ tailWord_877489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877569 : List Nat := [1, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_877569 : Nat := 118140960795 + 877569 * 2 ^ 59
def prefixEnd_877569 : Nat := 4983230072969 + 3 ^ 40 * 877569 * 2
def baseEnd_877569 : Nat := 400546403987184214179235

theorem tailTrace_877569 : CollatzResearch.WordTrace tailWord_877569 prefixEnd_877569 400546403987184214179235 := by
  unfold tailWord_877569
  simp only [CollatzResearch.WordTrace]
  refine ⟨32007570957724864698003761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21338380638483243132002507 32007570957724864698003761)
  ·
    refine ⟨24005678218293648523502821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32007570957724864698003761 24005678218293648523502821)
    ·
      refine ⟨4501064665930059098156779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24005678218293648523502821 4501064665930059098156779)
      ·
        refine ⟨6751596998895088647235169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501064665930059098156779 6751596998895088647235169)
        ·
          refine ⟨5063697749171316485426377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6751596998895088647235169 5063697749171316485426377)
          ·
            refine ⟨3797773311878487364069783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5063697749171316485426377 3797773311878487364069783)
            ·
              refine ⟨5696659967817731046104675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3797773311878487364069783 5696659967817731046104675)
              ·
                refine ⟨8544989951726596569157013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5696659967817731046104675 8544989951726596569157013)
                ·
                  refine ⟨400546403987184214179235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8544989951726596569157013 400546403987184214179235)
                  ·
                    rfl

theorem cell20_877569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_877569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877569 prefixEnd_877569 := by exact prefixLift 877569
  have htrace : WordTrace (prefixWord ++ tailWord_877569) baseStart_877569 baseEnd_877569 := by
    simpa [prefixWord, tailWord_877569, baseEnd_877569] using wordTrace_append hprefix tailTrace_877569
  have hstable : (prefixWord ++ tailWord_877569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877569).length < 2 ^ (prefixWord ++ tailWord_877569).sum := by decide
  have hdescent : baseEnd_877569 < baseStart_877569 := by decide
  rcases family_descends (prefixWord ++ tailWord_877569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877596 : List Nat := [2, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_877596 : Nat := 118140960795 + 877596 * 2 ^ 59
def prefixEnd_877596 : Nat := 4983230072969 + 3 ^ 40 * 877596 * 2
def baseEnd_877596 : Nat := 400558727522892120279125

theorem tailTrace_877596 : CollatzResearch.WordTrace tailWord_877596 prefixEnd_877596 400558727522892120279125 := by
  unfold tailWord_877596
  simp only [CollatzResearch.WordTrace]
  refine ⟨16004277864313524154618321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21339037152418032206157761 16004277864313524154618321)
  ·
    refine ⟨12003208398235143115963741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16004277864313524154618321 12003208398235143115963741)
    ·
      refine ⟨4501203149338178668486403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12003208398235143115963741 4501203149338178668486403)
      ·
        refine ⟨6751804724007268002729605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501203149338178668486403 6751804724007268002729605)
        ·
          refine ⟨1265963385751362750511801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6751804724007268002729605 1265963385751362750511801)
          ·
            refine ⟨949472539313522062883851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1265963385751362750511801 949472539313522062883851)
            ·
              refine ⟨1424208808970283094325777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949472539313522062883851 1424208808970283094325777)
              ·
                refine ⟨1068156606727712320744333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424208808970283094325777 1068156606727712320744333)
                ·
                  refine ⟨400558727522892120279125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068156606727712320744333 400558727522892120279125)
                  ·
                    rfl

theorem cell20_877596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_877596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877596 prefixEnd_877596 := by exact prefixLift 877596
  have htrace : WordTrace (prefixWord ++ tailWord_877596) baseStart_877596 baseEnd_877596 := by
    simpa [prefixWord, tailWord_877596, baseEnd_877596] using wordTrace_append hprefix tailTrace_877596
  have hstable : (prefixWord ++ tailWord_877596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877596).length < 2 ^ (prefixWord ++ tailWord_877596).sum := by decide
  have hdescent : baseEnd_877596 < baseStart_877596 := by decide
  rcases family_descends (prefixWord ++ tailWord_877596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877617 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 3]
def baseStart_877617 : Nat := 118140960795 + 877617 * 2 ^ 59
def prefixEnd_877617 : Nat := 4983230072969 + 3 ^ 40 * 877617 * 2
def baseEnd_877617 : Nat := 400568312495109380579039

theorem tailTrace_877617 : CollatzResearch.WordTrace tailWord_877617 prefixEnd_877617 400568312495109380579039 := by
  unfold tailWord_877617
  simp only [CollatzResearch.WordTrace]
  refine ⟨32009321661550968895751105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21339547774367312597167403 32009321661550968895751105)
  ·
    refine ⟨24006991246163226671813329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32009321661550968895751105 24006991246163226671813329)
    ·
      refine ⟨18005243434622420003859997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24006991246163226671813329 18005243434622420003859997)
      ·
        refine ⟨6751966287983407501447499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18005243434622420003859997 6751966287983407501447499)
        ·
          refine ⟨10127949431975111252171249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6751966287983407501447499 10127949431975111252171249)
          ·
            refine ⟨7595962073981333439128437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10127949431975111252171249 7595962073981333439128437)
            ·
              refine ⟨712121444435750009918291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7595962073981333439128437 712121444435750009918291)
              ·
                refine ⟨1068182166653625014877437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712121444435750009918291 1068182166653625014877437)
                ·
                  refine ⟨400568312495109380579039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068182166653625014877437 400568312495109380579039)
                  ·
                    rfl

theorem cell20_877617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_877617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877617 prefixEnd_877617 := by exact prefixLift 877617
  have htrace : WordTrace (prefixWord ++ tailWord_877617) baseStart_877617 baseEnd_877617 := by
    simpa [prefixWord, tailWord_877617, baseEnd_877617] using wordTrace_append hprefix tailTrace_877617
  have hstable : (prefixWord ++ tailWord_877617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877617).length < 2 ^ (prefixWord ++ tailWord_877617).sum := by decide
  have hdescent : baseEnd_877617 < baseStart_877617 := by decide
  rcases family_descends (prefixWord ++ tailWord_877617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877652 : List Nat := [2, 4, 1, 1, 1, 1, 10]
def baseStart_877652 : Nat := 118140960795 + 877652 * 2 ^ 59
def prefixEnd_877652 : Nat := 4983230072969 + 3 ^ 40 * 877652 * 2
def baseEnd_877652 : Nat := 44509365272089423823581

theorem tailTrace_877652 : CollatzResearch.WordTrace tailWord_877652 prefixEnd_877652 44509365272089423823581 := by
  unfold tailWord_877652
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005299108212084936637605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21340398810949446582183473 16005299108212084936637605)
  ·
    refine ⟨3000993582789765925619551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16005299108212084936637605 3000993582789765925619551)
    ·
      refine ⟨4501490374184648888429327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000993582789765925619551 4501490374184648888429327)
      ·
        refine ⟨6752235561276973332643991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4501490374184648888429327 6752235561276973332643991)
        ·
          refine ⟨10128353341915459998965987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6752235561276973332643991 10128353341915459998965987)
          ·
            refine ⟨15192530012873189998448981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10128353341915459998965987 15192530012873189998448981)
            ·
              refine ⟨44509365272089423823581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15192530012873189998448981 44509365272089423823581)
              ·
                rfl

theorem cell20_877652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 10].length) (baseStart_877652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877652 prefixEnd_877652 := by exact prefixLift 877652
  have htrace : WordTrace (prefixWord ++ tailWord_877652) baseStart_877652 baseEnd_877652 := by
    simpa [prefixWord, tailWord_877652, baseEnd_877652] using wordTrace_append hprefix tailTrace_877652
  have hstable : (prefixWord ++ tailWord_877652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877652).length < 2 ^ (prefixWord ++ tailWord_877652).sum := by decide
  have hdescent : baseEnd_877652 < baseStart_877652 := by decide
  rcases family_descends (prefixWord ++ tailWord_877652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877654 : List Nat := [5, 2, 2, 1, 2, 1, 3, 2, 2]
def baseStart_877654 : Nat := 118140960795 + 877654 * 2 ^ 59
def prefixEnd_877654 : Nat := 4983230072969 + 3 ^ 40 * 877654 * 2
def baseEnd_877654 : Nat := 400585200303301696345555

theorem tailTrace_877654 : CollatzResearch.WordTrace tailWord_877654 prefixEnd_877654 400585200303301696345555 := by
  unfold tailWord_877654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2000666947651057763428001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21340447441611282809898677 2000666947651057763428001)
  ·
    refine ⟨1500500210738293322571001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2000666947651057763428001 1500500210738293322571001)
    ·
      refine ⟨1125375158053719991928251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1500500210738293322571001 1125375158053719991928251)
      ·
        refine ⟨1688062737080579987892377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125375158053719991928251 1688062737080579987892377)
        ·
          refine ⟨1266047052810434990919283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688062737080579987892377 1266047052810434990919283)
          ·
            refine ⟨1899070579215652486378925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266047052810434990919283 1899070579215652486378925)
            ·
              refine ⟨712151467205869682392097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1899070579215652486378925 712151467205869682392097)
              ·
                refine ⟨534113600404402261794073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712151467205869682392097 534113600404402261794073)
                ·
                  refine ⟨400585200303301696345555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534113600404402261794073 400585200303301696345555)
                  ·
                    rfl

theorem cell20_877654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_877654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877654 prefixEnd_877654 := by exact prefixLift 877654
  have htrace : WordTrace (prefixWord ++ tailWord_877654) baseStart_877654 baseEnd_877654 := by
    simpa [prefixWord, tailWord_877654, baseEnd_877654] using wordTrace_append hprefix tailTrace_877654
  have hstable : (prefixWord ++ tailWord_877654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877654).length < 2 ^ (prefixWord ++ tailWord_877654).sum := by decide
  have hdescent : baseEnd_877654 < baseStart_877654 := by decide
  rcases family_descends (prefixWord ++ tailWord_877654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877672 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 3]
def baseStart_877672 : Nat := 118140960795 + 877672 * 2 ^ 59
def prefixEnd_877672 : Nat := 4983230072969 + 3 ^ 40 * 877672 * 2
def baseEnd_877672 : Nat := 400593415993773633745481

theorem tailTrace_877672 : CollatzResearch.WordTrace tailWord_877672 prefixEnd_877672 400593415993773633745481 := by
  unfold tailWord_877672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005663838175856644501635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21340885117567808859335513 16005663838175856644501635)
  ·
    refine ⟨24008495757263784966752453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16005663838175856644501635 24008495757263784966752453)
    ·
      refine ⟨4501592954486959681266085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24008495757263784966752453 4501592954486959681266085)
      ·
        refine ⟨844048678966304940237391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4501592954486959681266085 844048678966304940237391)
        ·
          refine ⟨1266073018449457410356087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 844048678966304940237391 1266073018449457410356087)
          ·
            refine ⟨1899109527674186115534131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266073018449457410356087 1899109527674186115534131)
            ·
              refine ⟨2848664291511279173301197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899109527674186115534131 2848664291511279173301197)
              ·
                refine ⟨1068249109316729689987949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848664291511279173301197 1068249109316729689987949)
                ·
                  refine ⟨400593415993773633745481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068249109316729689987949 400593415993773633745481)
                  ·
                    rfl

theorem cell20_877672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3].length) (baseStart_877672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877672 prefixEnd_877672 := by exact prefixLift 877672
  have htrace : WordTrace (prefixWord ++ tailWord_877672) baseStart_877672 baseEnd_877672 := by
    simpa [prefixWord, tailWord_877672, baseEnd_877672] using wordTrace_append hprefix tailTrace_877672
  have hstable : (prefixWord ++ tailWord_877672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877672).length < 2 ^ (prefixWord ++ tailWord_877672).sum := by decide
  have hdescent : baseEnd_877672 < baseStart_877672 := by decide
  rcases family_descends (prefixWord ++ tailWord_877672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877676 : List Nat := [2, 2, 1, 1, 3, 2, 3, 3, 3]
def baseStart_877676 : Nat := 118140960795 + 877676 * 2 ^ 59
def prefixEnd_877676 : Nat := 4983230072969 + 3 ^ 40 * 877676 * 2
def baseEnd_877676 : Nat := 400595241702767397612131

theorem tailTrace_877676 : CollatzResearch.WordTrace tailWord_877676 prefixEnd_877676 400595241702767397612131 := by
  unfold tailWord_877676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16005736784168610986074441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21340982378891481314765921 16005736784168610986074441)
  ·
    refine ⟨12004302588126458239555831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16005736784168610986074441 12004302588126458239555831)
    ·
      refine ⟨18006453882189687359333747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12004302588126458239555831 18006453882189687359333747)
      ·
        refine ⟨27009680823284531039000621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18006453882189687359333747 27009680823284531039000621)
        ·
          refine ⟨10128630308731699139625233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27009680823284531039000621 10128630308731699139625233)
          ·
            refine ⟨7596472731548774354718925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10128630308731699139625233 7596472731548774354718925)
            ·
              refine ⟨2848677274330790383019597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7596472731548774354718925 2848677274330790383019597)
              ·
                refine ⟨1068253977874046393632349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2848677274330790383019597 1068253977874046393632349)
                ·
                  refine ⟨400595241702767397612131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068253977874046393632349 400595241702767397612131)
                  ·
                    rfl

theorem cell20_877676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_877676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877676 prefixEnd_877676 := by exact prefixLift 877676
  have htrace : WordTrace (prefixWord ++ tailWord_877676) baseStart_877676 baseEnd_877676 := by
    simpa [prefixWord, tailWord_877676, baseEnd_877676] using wordTrace_append hprefix tailTrace_877676
  have hstable : (prefixWord ++ tailWord_877676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877676).length < 2 ^ (prefixWord ++ tailWord_877676).sum := by decide
  have hdescent : baseEnd_877676 < baseStart_877676 := by decide
  rcases family_descends (prefixWord ++ tailWord_877676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877738 : List Nat := [3, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_877738 : Nat := 118140960795 + 877738 * 2 ^ 59
def prefixEnd_877738 : Nat := 4983230072969 + 3 ^ 40 * 877738 * 2
def baseEnd_877738 : Nat := 400623540192170737545211

theorem tailTrace_877738 : CollatzResearch.WordTrace tailWord_877738 prefixEnd_877738 400623540192170737545211 := by
  unfold tailWord_877738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003433723528151640226467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21342489929408404373937245 8003433723528151640226467)
  ·
    refine ⟨12005150585292227460339701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8003433723528151640226467 12005150585292227460339701)
    ·
      refine ⟨1125482867371146324406847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12005150585292227460339701 1125482867371146324406847)
      ·
        refine ⟨1688224301056719486610271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125482867371146324406847 1688224301056719486610271)
        ·
          refine ⟨2532336451585079229915407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1688224301056719486610271 2532336451585079229915407)
          ·
            refine ⟨3798504677377618844873111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532336451585079229915407 3798504677377618844873111)
            ·
              refine ⟨5697757016066428267309667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798504677377618844873111 5697757016066428267309667)
              ·
                refine ⟨8546635524099642400964501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5697757016066428267309667 8546635524099642400964501)
                ·
                  refine ⟨400623540192170737545211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8546635524099642400964501 400623540192170737545211)
                  ·
                    rfl

theorem cell20_877738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_877738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877738 prefixEnd_877738 := by exact prefixLift 877738
  have htrace : WordTrace (prefixWord ++ tailWord_877738) baseStart_877738 baseEnd_877738 := by
    simpa [prefixWord, tailWord_877738, baseEnd_877738] using wordTrace_append hprefix tailTrace_877738
  have hstable : (prefixWord ++ tailWord_877738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877738).length < 2 ^ (prefixWord ++ tailWord_877738).sum := by decide
  have hdescent : baseEnd_877738 < baseStart_877738 := by decide
  rcases family_descends (prefixWord ++ tailWord_877738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877804 : List Nat := [2, 2, 1, 1, 2, 5, 1, 6]
def baseStart_877804 : Nat := 118140960795 + 877804 * 2 ^ 59
def prefixEnd_877804 : Nat := 4983230072969 + 3 ^ 40 * 877804 * 2
def baseEnd_877804 : Nat := 133551221463522613781647

theorem tailTrace_877804 : CollatzResearch.WordTrace tailWord_877804 prefixEnd_877804 133551221463522613781647 := by
  unfold tailWord_877804
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008071055936749916404233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21344094741248999888538977 16008071055936749916404233)
  ·
    refine ⟨12006053291952562437303175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16008071055936749916404233 12006053291952562437303175)
    ·
      refine ⟨18009079937928843655954763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12006053291952562437303175 18009079937928843655954763)
      ·
        refine ⟨27013619906893265483932145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18009079937928843655954763 27013619906893265483932145)
        ·
          refine ⟨20260214930169949112949109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27013619906893265483932145 20260214930169949112949109)
          ·
            refine ⟨1899395149703432729338979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20260214930169949112949109 1899395149703432729338979)
            ·
              refine ⟨2849092724555149094008469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899395149703432729338979 2849092724555149094008469)
              ·
                refine ⟨133551221463522613781647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2849092724555149094008469 133551221463522613781647)
                ·
                  rfl

theorem cell20_877804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 6].length) (baseStart_877804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877804 prefixEnd_877804 := by exact prefixLift 877804
  have htrace : WordTrace (prefixWord ++ tailWord_877804) baseStart_877804 baseEnd_877804 := by
    simpa [prefixWord, tailWord_877804, baseEnd_877804] using wordTrace_append hprefix tailTrace_877804
  have hstable : (prefixWord ++ tailWord_877804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877804).length < 2 ^ (prefixWord ++ tailWord_877804).sum := by decide
  have hdescent : baseEnd_877804 < baseStart_877804 := by decide
  rcases family_descends (prefixWord ++ tailWord_877804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877810 : List Nat := [3, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_877810 : Nat := 118140960795 + 877810 * 2 ^ 59
def prefixEnd_877810 : Nat := 4983230072969 + 3 ^ 40 * 877810 * 2
def baseEnd_877810 : Nat := 400656402954058487144917

theorem tailTrace_877810 : CollatzResearch.WordTrace tailWord_877810 prefixEnd_877810 400656402954058487144917 := by
  unfold tailWord_877810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8004090237462940714381721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21344240633234508571684589 8004090237462940714381721)
  ·
    refine ⟨6003067678097205535786291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8004090237462940714381721 6003067678097205535786291)
    ·
      refine ⟨9004601517145808303679437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6003067678097205535786291 9004601517145808303679437)
      ·
        refine ⟨3376725568929678113879789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9004601517145808303679437 3376725568929678113879789)
        ·
          refine ⟨1266272088348629292704921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3376725568929678113879789 1266272088348629292704921)
          ·
            refine ⟨949704066261471969528691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1266272088348629292704921 949704066261471969528691)
            ·
              refine ⟨1424556099392207954293037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949704066261471969528691 1424556099392207954293037)
              ·
                refine ⟨534208537272077982859889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424556099392207954293037 534208537272077982859889)
                ·
                  refine ⟨400656402954058487144917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534208537272077982859889 400656402954058487144917)
                  ·
                    rfl

theorem cell20_877810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_877810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877810 prefixEnd_877810 := by exact prefixLift 877810
  have htrace : WordTrace (prefixWord ++ tailWord_877810) baseStart_877810 baseEnd_877810 := by
    simpa [prefixWord, tailWord_877810, baseEnd_877810] using wordTrace_append hprefix tailTrace_877810
  have hstable : (prefixWord ++ tailWord_877810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877810).length < 2 ^ (prefixWord ++ tailWord_877810).sum := by decide
  have hdescent : baseEnd_877810 < baseStart_877810 := by decide
  rcases family_descends (prefixWord ++ tailWord_877810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877811 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 5]
def baseStart_877811 : Nat := 118140960795 + 877811 * 2 ^ 59
def prefixEnd_877811 : Nat := 4983230072969 + 3 ^ 40 * 877811 * 2
def baseEnd_877811 : Nat := 400656859381306928111579

theorem tailTrace_877811 : CollatzResearch.WordTrace tailWord_877811 prefixEnd_877811 400656859381306928111579 := by
  unfold tailWord_877811
  simp only [CollatzResearch.WordTrace]
  refine ⟨32016397422848140028313287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21344264948565426685542191 32016397422848140028313287)
  ·
    refine ⟨48024596134272210042469931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32016397422848140028313287 48024596134272210042469931)
    ·
      refine ⟨72036894201408315063704897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48024596134272210042469931 72036894201408315063704897)
      ·
        refine ⟨54027670651056236297778673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72036894201408315063704897 54027670651056236297778673)
        ·
          refine ⟨40520752988292177223334005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54027670651056236297778673 40520752988292177223334005)
          ·
            refine ⟨3798820592652391614687563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 40520752988292177223334005 3798820592652391614687563)
            ·
              refine ⟨5698230888978587422031345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3798820592652391614687563 5698230888978587422031345)
              ·
                refine ⟨4273673166733940566523509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5698230888978587422031345 4273673166733940566523509)
                ·
                  refine ⟨400656859381306928111579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273673166733940566523509 400656859381306928111579)
                  ·
                    rfl

theorem cell20_877811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 5].length) (baseStart_877811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877811 prefixEnd_877811 := by exact prefixLift 877811
  have htrace : WordTrace (prefixWord ++ tailWord_877811) baseStart_877811 baseEnd_877811 := by
    simpa [prefixWord, tailWord_877811, baseEnd_877811] using wordTrace_append hprefix tailTrace_877811
  have hstable : (prefixWord ++ tailWord_877811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877811).length < 2 ^ (prefixWord ++ tailWord_877811).sum := by decide
  have hdescent : baseEnd_877811 < baseStart_877811 := by decide
  rcases family_descends (prefixWord ++ tailWord_877811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877828 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_877828 : Nat := 118140960795 + 877828 * 2 ^ 59
def prefixEnd_877828 : Nat := 4983230072969 + 3 ^ 40 * 877828 * 2
def baseEnd_877828 : Nat := 400664618644530424544843

theorem tailTrace_877828 : CollatzResearch.WordTrace tailWord_877828 prefixEnd_877828 400664618644530424544843 := by
  unfold tailWord_877828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16008508731893275965841069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21344678309191034621121425 16008508731893275965841069)
  ·
    refine ⟨6003190774459978487190401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16008508731893275965841069 6003190774459978487190401)
    ·
      refine ⟨4502393080844983865392801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6003190774459978487190401 4502393080844983865392801)
      ·
        refine ⟨3376794810633737899044601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4502393080844983865392801 3376794810633737899044601)
        ·
          refine ⟨2532596107975303424283451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3376794810633737899044601 2532596107975303424283451)
          ·
            refine ⟨3798894161962955136425177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2532596107975303424283451 3798894161962955136425177)
            ·
              refine ⟨2849170621472216352318883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3798894161962955136425177 2849170621472216352318883)
              ·
                refine ⟨4273755932208324528478325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2849170621472216352318883 4273755932208324528478325)
                ·
                  refine ⟨400664618644530424544843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4273755932208324528478325 400664618644530424544843)
                  ·
                    rfl

theorem cell20_877828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_877828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877828 prefixEnd_877828 := by exact prefixLift 877828
  have htrace : WordTrace (prefixWord ++ tailWord_877828) baseStart_877828 baseEnd_877828 := by
    simpa [prefixWord, tailWord_877828, baseEnd_877828] using wordTrace_append hprefix tailTrace_877828
  have hstable : (prefixWord ++ tailWord_877828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877828).length < 2 ^ (prefixWord ++ tailWord_877828).sum := by decide
  have hdescent : baseEnd_877828 < baseStart_877828 := by decide
  rcases family_descends (prefixWord ++ tailWord_877828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877835 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_877835 : Nat := 118140960795 + 877835 * 2 ^ 59
def prefixEnd_877835 : Nat := 4983230072969 + 3 ^ 40 * 877835 * 2
def baseEnd_877835 : Nat := 400667813635269511311481

theorem tailTrace_877835 : CollatzResearch.WordTrace tailWord_877835 prefixEnd_877835 400667813635269511311481 := by
  unfold tailWord_877835
  simp only [CollatzResearch.WordTrace]
  refine ⟨32017272774761192127186959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21344848516507461418124639 32017272774761192127186959)
  ·
    refine ⟨48025909162141788190780439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32017272774761192127186959 48025909162141788190780439)
    ·
      refine ⟨72038863743212682286170659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48025909162141788190780439 72038863743212682286170659)
      ·
        refine ⟨108058295614819023429255989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72038863743212682286170659 108058295614819023429255989)
        ·
          refine ⟨10130465213889283446492749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 108058295614819023429255989 10130465213889283446492749)
          ·
            refine ⟨3798924455208481292434781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10130465213889283446492749 3798924455208481292434781)
            ·
              refine ⟨1424596670703180484663043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3798924455208481292434781 1424596670703180484663043)
              ·
                refine ⟨2136895006054770726994565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424596670703180484663043 2136895006054770726994565)
                ·
                  refine ⟨400667813635269511311481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2136895006054770726994565 400667813635269511311481)
                  ·
                    rfl

theorem cell20_877835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_877835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877835 prefixEnd_877835 := by exact prefixLift 877835
  have htrace : WordTrace (prefixWord ++ tailWord_877835) baseStart_877835 baseEnd_877835 := by
    simpa [prefixWord, tailWord_877835, baseEnd_877835] using wordTrace_append hprefix tailTrace_877835
  have hstable : (prefixWord ++ tailWord_877835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877835).length < 2 ^ (prefixWord ++ tailWord_877835).sum := by decide
  have hdescent : baseEnd_877835 < baseStart_877835 := by decide
  rcases family_descends (prefixWord ++ tailWord_877835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877911 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_877911 : Nat := 118140960795 + 877911 * 2 ^ 59
def prefixEnd_877911 : Nat := 4983230072969 + 3 ^ 40 * 877911 * 2
def baseEnd_877911 : Nat := 400702502106151024777837

theorem tailTrace_877911 : CollatzResearch.WordTrace tailWord_877911 prefixEnd_877911 400702502106151024777837 := by
  unfold tailWord_877911
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020044722485857106953587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21346696481657238071302391 32020044722485857106953587)
  ·
    refine ⟨48030067083728785660430381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32020044722485857106953587 48030067083728785660430381)
    ·
      refine ⟨18011275156398294622661393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48030067083728785660430381 18011275156398294622661393)
      ·
        refine ⟨13508456367298720966996045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18011275156398294622661393 13508456367298720966996045)
        ·
          refine ⟨5065671137737020362623517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13508456367298720966996045 5065671137737020362623517)
          ·
            refine ⟨1899626676651382635983819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5065671137737020362623517 1899626676651382635983819)
            ·
              refine ⟨2849440014977073953975729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1899626676651382635983819 2849440014977073953975729)
              ·
                refine ⟨2137080011232805465481797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2849440014977073953975729 2137080011232805465481797)
                ·
                  refine ⟨400702502106151024777837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137080011232805465481797 400702502106151024777837)
                  ·
                    rfl

theorem cell20_877911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_877911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877911 prefixEnd_877911 := by exact prefixLift 877911
  have htrace : WordTrace (prefixWord ++ tailWord_877911) baseStart_877911 baseEnd_877911 := by
    simpa [prefixWord, tailWord_877911, baseEnd_877911] using wordTrace_append hprefix tailTrace_877911
  have hstable : (prefixWord ++ tailWord_877911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877911).length < 2 ^ (prefixWord ++ tailWord_877911).sum := by decide
  have hdescent : baseEnd_877911 < baseStart_877911 := by decide
  rcases family_descends (prefixWord ++ tailWord_877911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877925 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_877925 : Nat := 118140960795 + 877925 * 2 ^ 59
def prefixEnd_877925 : Nat := 4983230072969 + 3 ^ 40 * 877925 * 2
def baseEnd_877925 : Nat := 400708892087629198311113

theorem tailTrace_877925 : CollatzResearch.WordTrace tailWord_877925 prefixEnd_877925 400708892087629198311113 := by
  unfold tailWord_877925
  simp only [CollatzResearch.WordTrace]
  refine ⟨32020555344435137497963229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21347036896290091665308819 32020555344435137497963229)
  ·
    refine ⟨12007708254163176561736211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32020555344435137497963229 12007708254163176561736211)
    ·
      refine ⟨18011562381244764842604317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12007708254163176561736211 18011562381244764842604317)
      ·
        refine ⟨6754335892966786815976619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18011562381244764842604317 6754335892966786815976619)
        ·
          refine ⟨10131503839450180223964929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6754335892966786815976619 10131503839450180223964929)
          ·
            refine ⟨7598627879587635167973697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10131503839450180223964929 7598627879587635167973697)
            ·
              refine ⟨5698970909690726375980273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7598627879587635167973697 5698970909690726375980273)
              ·
                refine ⟨4274228182268044781985205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5698970909690726375980273 4274228182268044781985205)
                ·
                  refine ⟨400708892087629198311113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4274228182268044781985205 400708892087629198311113)
                  ·
                    rfl

theorem cell20_877925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_877925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877925 prefixEnd_877925 := by exact prefixLift 877925
  have htrace : WordTrace (prefixWord ++ tailWord_877925) baseStart_877925 baseEnd_877925 := by
    simpa [prefixWord, tailWord_877925, baseEnd_877925] using wordTrace_append hprefix tailTrace_877925
  have hstable : (prefixWord ++ tailWord_877925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877925).length < 2 ^ (prefixWord ++ tailWord_877925).sum := by decide
  have hdescent : baseEnd_877925 < baseStart_877925 := by decide
  rcases family_descends (prefixWord ++ tailWord_877925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877949 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 4]
def baseStart_877949 : Nat := 118140960795 + 877949 * 2 ^ 59
def prefixEnd_877949 : Nat := 4983230072969 + 3 ^ 40 * 877949 * 2
def baseEnd_877949 : Nat := 400719846341591781511015

theorem tailTrace_877949 : CollatzResearch.WordTrace tailWord_877949 prefixEnd_877949 400719846341591781511015 := by
  unfold tailWord_877949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021430696348189596836901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21347620464232126397891267 32021430696348189596836901)
  ·
    refine ⟨6004018255565285549406919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32021430696348189596836901 6004018255565285549406919)
    ·
      refine ⟨9006027383347928324110379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6004018255565285549406919 9006027383347928324110379)
      ·
        refine ⟨13509041075021892486165569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9006027383347928324110379 13509041075021892486165569)
        ·
          refine ⟨10131780806266419364624177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13509041075021892486165569 10131780806266419364624177)
          ·
            refine ⟨7598835604699814523468133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10131780806266419364624177 7598835604699814523468133)
            ·
              refine ⟨1424781675881215223150275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7598835604699814523468133 1424781675881215223150275)
              ·
                refine ⟨2137172513821822834725413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1424781675881215223150275 2137172513821822834725413)
                ·
                  refine ⟨400719846341591781511015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137172513821822834725413 400719846341591781511015)
                  ·
                    rfl

theorem cell20_877949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_877949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877949 prefixEnd_877949 := by exact prefixLift 877949
  have htrace : WordTrace (prefixWord ++ tailWord_877949) baseStart_877949 baseEnd_877949 := by
    simpa [prefixWord, tailWord_877949, baseEnd_877949] using wordTrace_append hprefix tailTrace_877949
  have hstable : (prefixWord ++ tailWord_877949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877949).length < 2 ^ (prefixWord ++ tailWord_877949).sum := by decide
  have hdescent : baseEnd_877949 < baseStart_877949 := by decide
  rcases family_descends (prefixWord ++ tailWord_877949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877959 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 3]
def baseStart_877959 : Nat := 118140960795 + 877959 * 2 ^ 59
def prefixEnd_877959 : Nat := 4983230072969 + 3 ^ 40 * 877959 * 2
def baseEnd_877959 : Nat := 400724410614076191177641

theorem tailTrace_877959 : CollatzResearch.WordTrace tailWord_877959 prefixEnd_877959 400724410614076191177641 := by
  unfold tailWord_877959
  simp only [CollatzResearch.WordTrace]
  refine ⟨32021795426311961304700931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21347863617541307536467287 32021795426311961304700931)
  ·
    refine ⟨48032693139467941957051397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32021795426311961304700931 48032693139467941957051397)
    ·
      refine ⟨9006129963650239116947137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48032693139467941957051397 9006129963650239116947137)
      ·
        refine ⟨6754597472737679337710353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9006129963650239116947137 6754597472737679337710353)
        ·
          refine ⟨5065948104553259503282765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6754597472737679337710353 5065948104553259503282765)
          ·
            refine ⟨1899730539207472313731037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5065948104553259503282765 1899730539207472313731037)
            ·
              refine ⟨712398952202802117649139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1899730539207472313731037 712398952202802117649139)
              ·
                refine ⟨1068598428304203176473709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712398952202802117649139 1068598428304203176473709)
                ·
                  refine ⟨400724410614076191177641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068598428304203176473709 400724410614076191177641)
                  ·
                    rfl

theorem cell20_877959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 3].length) (baseStart_877959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877959 prefixEnd_877959 := by exact prefixLift 877959
  have htrace : WordTrace (prefixWord ++ tailWord_877959) baseStart_877959 baseEnd_877959 := by
    simpa [prefixWord, tailWord_877959, baseEnd_877959] using wordTrace_append hprefix tailTrace_877959
  have hstable : (prefixWord ++ tailWord_877959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877959).length < 2 ^ (prefixWord ++ tailWord_877959).sum := by decide
  have hdescent : baseEnd_877959 < baseStart_877959 := by decide
  rcases family_descends (prefixWord ++ tailWord_877959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_877983 : List Nat := [1, 1, 2, 5, 1, 4, 1, 3, 2]
def baseStart_877983 : Nat := 118140960795 + 877983 * 2 ^ 59
def prefixEnd_877983 : Nat := 4983230072969 + 3 ^ 40 * 877983 * 2
def baseEnd_877983 : Nat := 400735364868038774377543

theorem tailTrace_877983 : CollatzResearch.WordTrace tailWord_877983 prefixEnd_877983 400735364868038774377543 := by
  unfold tailWord_877983
  simp only [CollatzResearch.WordTrace]
  refine ⟨32022670778225013403574603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21348447185483342269049735 32022670778225013403574603)
  ·
    refine ⟨48034006167337520105361905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32022670778225013403574603 48034006167337520105361905)
    ·
      refine ⟨36025504625503140079021429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48034006167337520105361905 36025504625503140079021429)
      ·
        refine ⟨3377391058640919382408259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36025504625503140079021429 3377391058640919382408259)
        ·
          refine ⟨5066086587961379073612389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377391058640919382408259 5066086587961379073612389)
          ·
            refine ⟨949891235242758576302323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5066086587961379073612389 949891235242758576302323)
            ·
              refine ⟨1424836852864137864453485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 949891235242758576302323 1424836852864137864453485)
              ·
                refine ⟨534313819824051699170057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1424836852864137864453485 534313819824051699170057)
                ·
                  refine ⟨400735364868038774377543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534313819824051699170057 400735364868038774377543)
                  ·
                    rfl

theorem cell20_877983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2].length) (baseStart_877983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_877983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_877983 prefixEnd_877983 := by exact prefixLift 877983
  have htrace : WordTrace (prefixWord ++ tailWord_877983) baseStart_877983 baseEnd_877983 := by
    simpa [prefixWord, tailWord_877983, baseEnd_877983] using wordTrace_append hprefix tailTrace_877983
  have hstable : (prefixWord ++ tailWord_877983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_877983).length < 2 ^ (prefixWord ++ tailWord_877983).sum := by decide
  have hdescent : baseEnd_877983 < baseStart_877983 := by decide
  rcases family_descends (prefixWord ++ tailWord_877983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878001 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_878001 : Nat := 118140960795 + 878001 * 2 ^ 59
def prefixEnd_878001 : Nat := 4983230072969 + 3 ^ 40 * 878001 * 2
def baseEnd_878001 : Nat := 400743580558510711777469

theorem tailTrace_878001 : CollatzResearch.WordTrace tailWord_878001 prefixEnd_878001 400743580558510711777469 := by
  unfold tailWord_878001
  simp only [CollatzResearch.WordTrace]
  refine ⟨32023327292159802477729857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21348884861439868318486571 32023327292159802477729857)
  ·
    refine ⟨24017495469119851858297393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32023327292159802477729857 24017495469119851858297393)
    ·
      refine ⟨18013121601839888893723045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24017495469119851858297393 18013121601839888893723045)
      ·
        refine ⟨3377460300344979167573071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18013121601839888893723045 3377460300344979167573071)
        ·
          refine ⟨5066190450517468751359607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3377460300344979167573071 5066190450517468751359607)
          ·
            refine ⟨7599285675776203127039411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5066190450517468751359607 7599285675776203127039411)
            ·
              refine ⟨11398928513664304690559117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7599285675776203127039411 11398928513664304690559117)
              ·
                refine ⟨4274598192624114258959669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11398928513664304690559117 4274598192624114258959669)
                ·
                  refine ⟨400743580558510711777469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4274598192624114258959669 400743580558510711777469)
                  ·
                    rfl

theorem cell20_878001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_878001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878001 prefixEnd_878001 := by exact prefixLift 878001
  have htrace : WordTrace (prefixWord ++ tailWord_878001) baseStart_878001 baseEnd_878001 := by
    simpa [prefixWord, tailWord_878001, baseEnd_878001] using wordTrace_append hprefix tailTrace_878001
  have hstable : (prefixWord ++ tailWord_878001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878001).length < 2 ^ (prefixWord ++ tailWord_878001).sum := by decide
  have hdescent : baseEnd_878001 < baseStart_878001 := by decide
  rcases family_descends (prefixWord ++ tailWord_878001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878056 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 3]
def baseStart_878056 : Nat := 118140960795 + 878056 * 2 ^ 59
def prefixEnd_878056 : Nat := 4983230072969 + 3 ^ 40 * 878056 * 2
def baseEnd_878056 : Nat := 400768684057174964943911

theorem tailTrace_878056 : CollatzResearch.WordTrace tailWord_878056 prefixEnd_878056 400768684057174964943911 := by
  unfold tailWord_878056
  simp only [CollatzResearch.WordTrace]
  refine ⟨16012666653480273435491011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21350222204640364580654681 16012666653480273435491011)
  ·
    refine ⟨24018999980220410153236517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16012666653480273435491011 24018999980220410153236517)
    ·
      refine ⟨4503562496291326903731847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24018999980220410153236517 4503562496291326903731847)
      ·
        refine ⟨6755343744436990355597771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4503562496291326903731847 6755343744436990355597771)
        ·
          refine ⟨10133015616655485533396657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755343744436990355597771 10133015616655485533396657)
          ·
            refine ⟨7599761712491614150047493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10133015616655485533396657 7599761712491614150047493)
            ·
              refine ⟨1424955321092177653133905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7599761712491614150047493 1424955321092177653133905)
              ·
                refine ⟨1068716490819133239850429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1424955321092177653133905 1068716490819133239850429)
                ·
                  refine ⟨400768684057174964943911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1068716490819133239850429 400768684057174964943911)
                  ·
                    rfl

theorem cell20_878056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 3].length) (baseStart_878056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878056 prefixEnd_878056 := by exact prefixLift 878056
  have htrace : WordTrace (prefixWord ++ tailWord_878056) baseStart_878056 baseEnd_878056 := by
    simpa [prefixWord, tailWord_878056, baseEnd_878056] using wordTrace_append hprefix tailTrace_878056
  have hstable : (prefixWord ++ tailWord_878056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878056).length < 2 ^ (prefixWord ++ tailWord_878056).sum := by decide
  have hdescent : baseEnd_878056 < baseStart_878056 := by decide
  rcases family_descends (prefixWord ++ tailWord_878056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878087 : List Nat := [1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_878087 : Nat := 118140960795 + 878087 * 2 ^ 59
def prefixEnd_878087 : Nat := 4983230072969 + 3 ^ 40 * 878087 * 2
def baseEnd_878087 : Nat := 133594277767292211636817

theorem tailTrace_878087 : CollatzResearch.WordTrace tailWord_878087 prefixEnd_878087 133594277767292211636817 := by
  unfold tailWord_878087
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026463969848239165360515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21350975979898826110240343 32026463969848239165360515)
  ·
    refine ⟨48039695954772358748040773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32026463969848239165360515 48039695954772358748040773)
    ·
      refine ⟨9007442991519817265257645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48039695954772358748040773 9007442991519817265257645)
      ·
        refine ⟨3377791121819931474471617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9007442991519817265257645 3377791121819931474471617)
        ·
          refine ⟨2533343341364948605853713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3377791121819931474471617 2533343341364948605853713)
          ·
            refine ⟨1900007506023711454390285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2533343341364948605853713 1900007506023711454390285)
            ·
              refine ⟨712502814758891795396357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1900007506023711454390285 712502814758891795396357)
              ·
                refine ⟨133594277767292211636817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712502814758891795396357 133594277767292211636817)
                ·
                  rfl

theorem cell20_878087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_878087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878087 prefixEnd_878087 := by exact prefixLift 878087
  have htrace : WordTrace (prefixWord ++ tailWord_878087) baseStart_878087 baseEnd_878087 := by
    simpa [prefixWord, tailWord_878087, baseEnd_878087] using wordTrace_append hprefix tailTrace_878087
  have hstable : (prefixWord ++ tailWord_878087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878087).length < 2 ^ (prefixWord ++ tailWord_878087).sum := by decide
  have hdescent : baseEnd_878087 < baseStart_878087 := by decide
  rcases family_descends (prefixWord ++ tailWord_878087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878093 : List Nat := [1, 7, 1, 1, 2, 1, 2, 3, 2]
def baseStart_878093 : Nat := 118140960795 + 878093 * 2 ^ 59
def prefixEnd_878093 : Nat := 4983230072969 + 3 ^ 40 * 878093 * 2
def baseEnd_878093 : Nat := 400785571865367280710427

theorem tailTrace_878093 : CollatzResearch.WordTrace tailWord_878093 prefixEnd_878093 400785571865367280710427 := by
  unfold tailWord_878093
  simp only [CollatzResearch.WordTrace]
  refine ⟨32026682807826502190078933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21351121871884334793385955 32026682807826502190078933)
  ·
    refine ⟨750625378308433645079975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 32026682807826502190078933 750625378308433645079975)
    ·
      refine ⟨1125938067462650467619963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 750625378308433645079975 1125938067462650467619963)
      ·
        refine ⟨1688907101193975701429945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1125938067462650467619963 1688907101193975701429945)
        ·
          refine ⟨1266680325895481776072459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1688907101193975701429945 1266680325895481776072459)
          ·
            refine ⟨1900020488843222664108689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266680325895481776072459 1900020488843222664108689)
            ·
              refine ⟨1425015366632416998081517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900020488843222664108689 1425015366632416998081517)
              ·
                refine ⟨534380762487156374280569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425015366632416998081517 534380762487156374280569)
                ·
                  refine ⟨400785571865367280710427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534380762487156374280569 400785571865367280710427)
                  ·
                    rfl

theorem cell20_878093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_878093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878093 prefixEnd_878093 := by exact prefixLift 878093
  have htrace : WordTrace (prefixWord ++ tailWord_878093) baseStart_878093 baseEnd_878093 := by
    simpa [prefixWord, tailWord_878093, baseEnd_878093] using wordTrace_append hprefix tailTrace_878093
  have hstable : (prefixWord ++ tailWord_878093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878093).length < 2 ^ (prefixWord ++ tailWord_878093).sum := by decide
  have hdescent : baseEnd_878093 < baseStart_878093 := by decide
  rcases family_descends (prefixWord ++ tailWord_878093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878129 : List Nat := [1, 2, 2, 3, 1, 1, 1, 9]
def baseStart_878129 : Nat := 118140960795 + 878129 * 2 ^ 59
def prefixEnd_878129 : Nat := 4983230072969 + 3 ^ 40 * 878129 * 2
def baseEnd_878129 : Nat := 133600667748770385170093

theorem tailTrace_878129 : CollatzResearch.WordTrace tailWord_878129 prefixEnd_878129 133600667748770385170093 := by
  unfold tailWord_878129
  simp only [CollatzResearch.WordTrace]
  refine ⟨32027995835696080338389441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21351997223797386892259627 32027995835696080338389441)
  ·
    refine ⟨24020996876772060253792081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32027995835696080338389441 24020996876772060253792081)
    ·
      refine ⟨18015747657579045190344061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24020996876772060253792081 18015747657579045190344061)
      ·
        refine ⟨6755905371592141946379023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18015747657579045190344061 6755905371592141946379023)
        ·
          refine ⟨10133858057388212919568535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6755905371592141946379023 10133858057388212919568535)
          ·
            refine ⟨15200787086082319379352803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10133858057388212919568535 15200787086082319379352803)
            ·
              refine ⟨22801180629123479069029205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15200787086082319379352803 22801180629123479069029205)
              ·
                refine ⟨133600667748770385170093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22801180629123479069029205 133600667748770385170093)
                ·
                  rfl

theorem cell20_878129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_878129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878129 prefixEnd_878129 := by exact prefixLift 878129
  have htrace : WordTrace (prefixWord ++ tailWord_878129) baseStart_878129 baseEnd_878129 := by
    simpa [prefixWord, tailWord_878129, baseEnd_878129] using wordTrace_append hprefix tailTrace_878129
  have hstable : (prefixWord ++ tailWord_878129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878129).length < 2 ^ (prefixWord ++ tailWord_878129).sum := by decide
  have hdescent : baseEnd_878129 < baseStart_878129 := by decide
  rcases family_descends (prefixWord ++ tailWord_878129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878156 : List Nat := [2, 2, 1, 3, 1, 3, 3, 3, 2]
def baseStart_878156 : Nat := 118140960795 + 878156 * 2 ^ 59
def prefixEnd_878156 : Nat := 4983230072969 + 3 ^ 40 * 878156 * 2
def baseEnd_878156 : Nat := 400814326782019061610169

theorem tailTrace_878156 : CollatzResearch.WordTrace tailWord_878156 prefixEnd_878156 400814326782019061610169 := by
  unfold tailWord_878156
  simp only [CollatzResearch.WordTrace]
  refine ⟨16014490303299131974811161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21352653737732175966414881 16014490303299131974811161)
  ·
    refine ⟨12010867727474348981108371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16014490303299131974811161 12010867727474348981108371)
    ·
      refine ⟨18016301591211523471662557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12010867727474348981108371 18016301591211523471662557)
      ·
        refine ⟨6756113096704321301873459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18016301591211523471662557 6756113096704321301873459)
        ·
          refine ⟨10134169645056481952810189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6756113096704321301873459 10134169645056481952810189)
          ·
            refine ⟨3800313616896180732303821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10134169645056481952810189 3800313616896180732303821)
            ·
              refine ⟨1425117606336067774613933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3800313616896180732303821 1425117606336067774613933)
              ·
                refine ⟨534419102376025415480225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1425117606336067774613933 534419102376025415480225)
                ·
                  refine ⟨400814326782019061610169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534419102376025415480225 400814326782019061610169)
                  ·
                    rfl

theorem cell20_878156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2].length) (baseStart_878156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878156 prefixEnd_878156 := by exact prefixLift 878156
  have htrace : WordTrace (prefixWord ++ tailWord_878156) baseStart_878156 baseEnd_878156 := by
    simpa [prefixWord, tailWord_878156, baseEnd_878156] using wordTrace_append hprefix tailTrace_878156
  have hstable : (prefixWord ++ tailWord_878156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878156).length < 2 ^ (prefixWord ++ tailWord_878156).sum := by decide
  have hdescent : baseEnd_878156 < baseStart_878156 := by decide
  rcases family_descends (prefixWord ++ tailWord_878156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878167 : List Nat := [1, 1, 3, 2, 2, 3, 8]
def baseStart_878167 : Nat := 118140960795 + 878167 * 2 ^ 59
def prefixEnd_878167 : Nat := 4983230072969 + 3 ^ 40 * 878167 * 2
def baseEnd_878167 : Nat := 44535483053527990249273

theorem tailTrace_878167 : CollatzResearch.WordTrace tailWord_878167 prefixEnd_878167 44535483053527990249273 := by
  unfold tailWord_878167
  simp only [CollatzResearch.WordTrace]
  refine ⟨32029381809558412828272755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21352921206372275218848503 32029381809558412828272755)
  ·
    refine ⟨48044072714337619242409133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32029381809558412828272755 48044072714337619242409133)
    ·
      refine ⟨18016527267876607215903425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48044072714337619242409133 18016527267876607215903425)
      ·
        refine ⟨13512395450907455411927569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18016527267876607215903425 13512395450907455411927569)
        ·
          refine ⟨10134296588180591558945677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13512395450907455411927569 10134296588180591558945677)
          ·
            refine ⟨3800361220567721834604629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10134296588180591558945677 3800361220567721834604629)
            ·
              refine ⟨44535483053527990249273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3800361220567721834604629 44535483053527990249273)
              ·
                rfl

theorem cell20_878167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 8].length) (baseStart_878167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878167 prefixEnd_878167 := by exact prefixLift 878167
  have htrace : WordTrace (prefixWord ++ tailWord_878167) baseStart_878167 baseEnd_878167 := by
    simpa [prefixWord, tailWord_878167, baseEnd_878167] using wordTrace_append hprefix tailTrace_878167
  have hstable : (prefixWord ++ tailWord_878167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878167).length < 2 ^ (prefixWord ++ tailWord_878167).sum := by decide
  have hdescent : baseEnd_878167 < baseStart_878167 := by decide
  rcases family_descends (prefixWord ++ tailWord_878167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878184 : List Nat := [2, 1, 4, 3, 1, 1, 1, 7]
def baseStart_878184 : Nat := 118140960795 + 878184 * 2 ^ 59
def prefixEnd_878184 : Nat := 4983230072969 + 3 ^ 40 * 878184 * 2
def baseEnd_878184 : Nat := 133609035581658469558907

theorem tailTrace_878184 : CollatzResearch.WordTrace tailWord_878184 prefixEnd_878184 133609035581658469558907 := by
  unfold tailWord_878184
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015000925248412365820803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21353334566997883154427737 16015000925248412365820803)
  ·
    refine ⟨24022501387872618548731205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015000925248412365820803 24022501387872618548731205)
    ·
      refine ⟨4504219010226115977887101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24022501387872618548731205 4504219010226115977887101)
      ·
        refine ⟨1689082128834793491707663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4504219010226115977887101 1689082128834793491707663)
        ·
          refine ⟨2533623193252190237561495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1689082128834793491707663 2533623193252190237561495)
          ·
            refine ⟨3800434789878285356342243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2533623193252190237561495 3800434789878285356342243)
            ·
              refine ⟨5700652184817428034513365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800434789878285356342243 5700652184817428034513365)
              ·
                refine ⟨133609035581658469558907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5700652184817428034513365 133609035581658469558907)
                ·
                  rfl

theorem cell20_878184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_878184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878184 prefixEnd_878184 := by exact prefixLift 878184
  have htrace : WordTrace (prefixWord ++ tailWord_878184) baseStart_878184 baseEnd_878184 := by
    simpa [prefixWord, tailWord_878184, baseEnd_878184] using wordTrace_append hprefix tailTrace_878184
  have hstable : (prefixWord ++ tailWord_878184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878184).length < 2 ^ (prefixWord ++ tailWord_878184).sum := by decide
  have hdescent : baseEnd_878184 < baseStart_878184 := by decide
  rcases family_descends (prefixWord ++ tailWord_878184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878232 : List Nat := [2, 1, 2, 4, 1, 3, 1, 4, 2]
def baseStart_878232 : Nat := 118140960795 + 878232 * 2 ^ 59
def prefixEnd_878232 : Nat := 4983230072969 + 3 ^ 40 * 878232 * 2
def baseEnd_878232 : Nat := 400849015252900575076525

theorem tailTrace_878232 : CollatzResearch.WordTrace tailWord_878232 prefixEnd_878232 400849015252900575076525 := by
  unfold tailWord_878232
  simp only [CollatzResearch.WordTrace]
  refine ⟨16015876277161464464694475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21354501702881952619592633 16015876277161464464694475)
  ·
    refine ⟨24023814415742196697041713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16015876277161464464694475 24023814415742196697041713)
    ·
      refine ⟨18017860811806647522781285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24023814415742196697041713 18017860811806647522781285)
      ·
        refine ⟨3378348902213746410521491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18017860811806647522781285 3378348902213746410521491)
        ·
          refine ⟨5067523353320619615782237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378348902213746410521491 5067523353320619615782237)
          ·
            refine ⟨1900321257495232355918339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5067523353320619615782237 1900321257495232355918339)
            ·
              refine ⟨2850481886242848533877509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900321257495232355918339 2850481886242848533877509)
              ·
                refine ⟨534465353670534100102033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2850481886242848533877509 534465353670534100102033)
                ·
                  refine ⟨400849015252900575076525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534465353670534100102033 400849015252900575076525)
                  ·
                    rfl

theorem cell20_878232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_878232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878232 prefixEnd_878232 := by exact prefixLift 878232
  have htrace : WordTrace (prefixWord ++ tailWord_878232) baseStart_878232 baseEnd_878232 := by
    simpa [prefixWord, tailWord_878232, baseEnd_878232] using wordTrace_append hprefix tailTrace_878232
  have hstable : (prefixWord ++ tailWord_878232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878232).length < 2 ^ (prefixWord ++ tailWord_878232).sum := by decide
  have hdescent : baseEnd_878232 < baseStart_878232 := by decide
  rcases family_descends (prefixWord ++ tailWord_878232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878253 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_878253 : Nat := 118140960795 + 878253 * 2 ^ 59
def prefixEnd_878253 : Nat := 4983230072969 + 3 ^ 40 * 878253 * 2
def baseEnd_878253 : Nat := 400858600225117835376439

theorem tailTrace_878253 : CollatzResearch.WordTrace tailWord_878253 prefixEnd_878253 400858600225117835376439 := by
  unfold tailWord_878253
  simp only [CollatzResearch.WordTrace]
  refine ⟨32032518487246849515903413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21355012324831233010602275 32032518487246849515903413)
  ·
    refine ⟨3003048608179392142115945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32032518487246849515903413 3003048608179392142115945)
    ·
      refine ⟨2252286456134544106586959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3003048608179392142115945 2252286456134544106586959)
      ·
        refine ⟨3378429684201816159880439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2252286456134544106586959 3378429684201816159880439)
        ·
          refine ⟨5067644526302724239820659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378429684201816159880439 5067644526302724239820659)
          ·
            refine ⟨7601466789454086359730989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067644526302724239820659 7601466789454086359730989)
            ·
              refine ⟨2850550046045282384899121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7601466789454086359730989 2850550046045282384899121)
              ·
                refine ⟨2137912534533961788674341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2850550046045282384899121 2137912534533961788674341)
                ·
                  refine ⟨400858600225117835376439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2137912534533961788674341 400858600225117835376439)
                  ·
                    rfl

theorem cell20_878253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_878253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878253 prefixEnd_878253 := by exact prefixLift 878253
  have htrace : WordTrace (prefixWord ++ tailWord_878253) baseStart_878253 baseEnd_878253 := by
    simpa [prefixWord, tailWord_878253, baseEnd_878253] using wordTrace_append hprefix tailTrace_878253
  have hstable : (prefixWord ++ tailWord_878253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878253).length < 2 ^ (prefixWord ++ tailWord_878253).sum := by decide
  have hdescent : baseEnd_878253 < baseStart_878253 := by decide
  rcases family_descends (prefixWord ++ tailWord_878253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878270 : List Nat := [4, 2, 1, 1, 2, 2, 1, 5, 2]
def baseStart_878270 : Nat := 118140960795 + 878270 * 2 ^ 59
def prefixEnd_878270 : Nat := 4983230072969 + 3 ^ 40 * 878270 * 2
def baseEnd_878270 : Nat := 400866359488341331809703

theorem tailTrace_878270 : CollatzResearch.WordTrace tailWord_878270 prefixEnd_878270 400866359488341331809703 := by
  unfold tailWord_878270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004142316023157677409033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21355425685456840946181509 4004142316023157677409033)
  ·
    refine ⟨3003106737017368258056775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4004142316023157677409033 3003106737017368258056775)
    ·
      refine ⟨4504660105526052387085163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003106737017368258056775 4504660105526052387085163)
      ·
        refine ⟨6756990158289078580627745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4504660105526052387085163 6756990158289078580627745)
        ·
          refine ⟨5067742618716808935470809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6756990158289078580627745 5067742618716808935470809)
          ·
            refine ⟨3800806964037606701603107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5067742618716808935470809 3800806964037606701603107)
            ·
              refine ⟨5701210446056410052404661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3800806964037606701603107 5701210446056410052404661)
              ·
                refine ⟨534488479317788442412937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5701210446056410052404661 534488479317788442412937)
                ·
                  refine ⟨400866359488341331809703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534488479317788442412937 400866359488341331809703)
                  ·
                    rfl

theorem cell20_878270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_878270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878270 prefixEnd_878270 := by exact prefixLift 878270
  have htrace : WordTrace (prefixWord ++ tailWord_878270) baseStart_878270 baseEnd_878270 := by
    simpa [prefixWord, tailWord_878270, baseEnd_878270] using wordTrace_append hprefix tailTrace_878270
  have hstable : (prefixWord ++ tailWord_878270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878270).length < 2 ^ (prefixWord ++ tailWord_878270).sum := by decide
  have hdescent : baseEnd_878270 < baseStart_878270 := by decide
  rcases family_descends (prefixWord ++ tailWord_878270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878284 : List Nat := [2, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_878284 : Nat := 118140960795 + 878284 * 2 ^ 59
def prefixEnd_878284 : Nat := 4983230072969 + 3 ^ 40 * 878284 * 2
def baseEnd_878284 : Nat := 400872749469819505342979

theorem tailTrace_878284 : CollatzResearch.WordTrace tailWord_878284 prefixEnd_878284 400872749469819505342979 := by
  unfold tailWord_878284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16016824575067270905140953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21355766100089694540187937 16016824575067270905140953)
  ·
    refine ⟨12012618431300453178855715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16016824575067270905140953 12012618431300453178855715)
    ·
      refine ⟨18018927646950679768283573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12012618431300453178855715 18018927646950679768283573)
      ·
        refine ⟨1689274466901626228276585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18018927646950679768283573 1689274466901626228276585)
        ·
          refine ⟨1266955850176219671207439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1689274466901626228276585 1266955850176219671207439)
          ·
            refine ⟨1900433775264329506811159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1266955850176219671207439 1900433775264329506811159)
            ·
              refine ⟨2850650662896494260216739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1900433775264329506811159 2850650662896494260216739)
              ·
                refine ⟨4275975994344741390325109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2850650662896494260216739 4275975994344741390325109)
                ·
                  refine ⟨400872749469819505342979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4275975994344741390325109 400872749469819505342979)
                  ·
                    rfl

theorem cell20_878284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_878284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878284 prefixEnd_878284 := by exact prefixLift 878284
  have htrace : WordTrace (prefixWord ++ tailWord_878284) baseStart_878284 baseEnd_878284 := by
    simpa [prefixWord, tailWord_878284, baseEnd_878284] using wordTrace_append hprefix tailTrace_878284
  have hstable : (prefixWord ++ tailWord_878284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878284).length < 2 ^ (prefixWord ++ tailWord_878284).sum := by decide
  have hdescent : baseEnd_878284 < baseStart_878284 := by decide
  rcases family_descends (prefixWord ++ tailWord_878284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878311 : List Nat := [1, 1, 5, 4, 2, 1, 2, 4]
def baseStart_878311 : Nat := 118140960795 + 878311 * 2 ^ 59
def prefixEnd_878311 : Nat := 4983230072969 + 3 ^ 40 * 878311 * 2
def baseEnd_878311 : Nat := 133628357668509137147623

theorem tailTrace_878311 : CollatzResearch.WordTrace tailWord_878311 prefixEnd_878311 133628357668509137147623 := by
  unfold tailWord_878311
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034633921036725421514787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21356422614024483614343191 32034633921036725421514787)
  ·
    refine ⟨48051950881555088132272181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32034633921036725421514787 48051950881555088132272181)
    ·
      refine ⟨4504870395145789512400517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48051950881555088132272181 4504870395145789512400517)
      ·
        refine ⟨844663199089835533575097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4504870395145789512400517 844663199089835533575097)
        ·
          refine ⟨633497399317376650181323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 844663199089835533575097 633497399317376650181323)
          ·
            refine ⟨950246098976064975271985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633497399317376650181323 950246098976064975271985)
            ·
              refine ⟨712684574232048731453989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950246098976064975271985 712684574232048731453989)
              ·
                refine ⟨133628357668509137147623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712684574232048731453989 133628357668509137147623)
                ·
                  rfl

theorem cell20_878311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 4].length) (baseStart_878311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878311 prefixEnd_878311 := by exact prefixLift 878311
  have htrace : WordTrace (prefixWord ++ tailWord_878311) baseStart_878311 baseEnd_878311 := by
    simpa [prefixWord, tailWord_878311, baseEnd_878311] using wordTrace_append hprefix tailTrace_878311
  have hstable : (prefixWord ++ tailWord_878311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878311).length < 2 ^ (prefixWord ++ tailWord_878311).sum := by decide
  have hdescent : baseEnd_878311 < baseStart_878311 := by decide
  rcases family_descends (prefixWord ++ tailWord_878311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878319 : List Nat := [1, 1, 2, 1, 5, 1, 3, 6]
def baseStart_878319 : Nat := 118140960795 + 878319 * 2 ^ 59
def prefixEnd_878319 : Nat := 4983230072969 + 3 ^ 40 * 878319 * 2
def baseEnd_878319 : Nat := 133629574807838313058723

theorem tailTrace_878319 : CollatzResearch.WordTrace tailWord_878319 prefixEnd_878319 133629574807838313058723 := by
  unfold tailWord_878319
  simp only [CollatzResearch.WordTrace]
  refine ⟨32034925705007742787806011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21356617136671828525204007 32034925705007742787806011)
  ·
    refine ⟨48052388557511614181709017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32034925705007742787806011 48052388557511614181709017)
    ·
      refine ⟨36039291418133710636281763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48052388557511614181709017 36039291418133710636281763)
      ·
        refine ⟨54058937127200565954422645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36039291418133710636281763 54058937127200565954422645)
        ·
          refine ⟨5068025355675053058227123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 54058937127200565954422645 5068025355675053058227123)
          ·
            refine ⟨7602038033512579587340685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068025355675053058227123 7602038033512579587340685)
            ·
              refine ⟨2850764262567217345252757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7602038033512579587340685 2850764262567217345252757)
              ·
                refine ⟨133629574807838313058723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2850764262567217345252757 133629574807838313058723)
                ·
                  rfl

theorem cell20_878319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_878319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878319 prefixEnd_878319 := by exact prefixLift 878319
  have htrace : WordTrace (prefixWord ++ tailWord_878319) baseStart_878319 baseEnd_878319 := by
    simpa [prefixWord, tailWord_878319, baseEnd_878319] using wordTrace_append hprefix tailTrace_878319
  have hstable : (prefixWord ++ tailWord_878319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878319).length < 2 ^ (prefixWord ++ tailWord_878319).sum := by decide
  have hdescent : baseEnd_878319 < baseStart_878319 := by decide
  rcases family_descends (prefixWord ++ tailWord_878319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878357 : List Nat := [1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_878357 : Nat := 118140960795 + 878357 * 2 ^ 59
def prefixEnd_878357 : Nat := 4983230072969 + 3 ^ 40 * 878357 * 2
def baseEnd_878357 : Nat := 133635356219651898636449

theorem tailTrace_878357 : CollatzResearch.WordTrace tailWord_878357 prefixEnd_878357 133635356219651898636449 := by
  unfold tailWord_878357
  simp only [CollatzResearch.WordTrace]
  refine ⟨32036311678870075277689325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21357541119246716851792883 32036311678870075277689325)
  ·
    refine ⟨12013616879576278229133497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32036311678870075277689325 12013616879576278229133497)
    ·
      refine ⟨9010212659682208671850123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12013616879576278229133497 9010212659682208671850123)
      ·
        refine ⟨13515318989523313007775185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9010212659682208671850123 13515318989523313007775185)
        ·
          refine ⟨10136489242142484755831389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13515318989523313007775185 10136489242142484755831389)
          ·
            refine ⟨3801183465803431783436771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10136489242142484755831389 3801183465803431783436771)
            ·
              refine ⟨5701775198705147675155157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801183465803431783436771 5701775198705147675155157)
              ·
                refine ⟨133635356219651898636449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5701775198705147675155157 133635356219651898636449)
                ·
                  rfl

theorem cell20_878357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_878357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878357 prefixEnd_878357 := by exact prefixLift 878357
  have htrace : WordTrace (prefixWord ++ tailWord_878357) baseStart_878357 baseEnd_878357 := by
    simpa [prefixWord, tailWord_878357, baseEnd_878357] using wordTrace_append hprefix tailTrace_878357
  have hstable : (prefixWord ++ tailWord_878357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878357).length < 2 ^ (prefixWord ++ tailWord_878357).sum := by decide
  have hdescent : baseEnd_878357 < baseStart_878357 := by decide
  rcases family_descends (prefixWord ++ tailWord_878357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878360 : List Nat := [2, 1, 2, 3, 1, 1, 6, 1, 3]
def baseStart_878360 : Nat := 118140960795 + 878360 * 2 ^ 59
def prefixEnd_878360 : Nat := 4983230072969 + 3 ^ 40 * 878360 * 2
def baseEnd_878360 : Nat := 400907437940701018809335

theorem tailTrace_878360 : CollatzResearch.WordTrace tailWord_878360 prefixEnd_878360 400907437940701018809335 := by
  unfold tailWord_878360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16018210548929603395024267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21357614065239471193365689 16018210548929603395024267)
  ·
    refine ⟨24027315823394405092536401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16018210548929603395024267 24027315823394405092536401)
    ·
      refine ⟨18020486867545803819402301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24027315823394405092536401 18020486867545803819402301)
      ·
        refine ⟨6757682575329676432275863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18020486867545803819402301 6757682575329676432275863)
        ·
          refine ⟨10136523862994514648413795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6757682575329676432275863 10136523862994514648413795)
          ·
            refine ⟨15204785794491771972620693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10136523862994514648413795 15204785794491771972620693)
            ·
              refine ⟨712724334116801811216595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15204785794491771972620693 712724334116801811216595)
              ·
                refine ⟨1069086501175202716824893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712724334116801811216595 1069086501175202716824893)
                ·
                  refine ⟨400907437940701018809335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069086501175202716824893 400907437940701018809335)
                  ·
                    rfl

theorem cell20_878360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_878360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878360 prefixEnd_878360 := by exact prefixLift 878360
  have htrace : WordTrace (prefixWord ++ tailWord_878360) baseStart_878360 baseEnd_878360 := by
    simpa [prefixWord, tailWord_878360, baseEnd_878360] using wordTrace_append hprefix tailTrace_878360
  have hstable : (prefixWord ++ tailWord_878360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878360).length < 2 ^ (prefixWord ++ tailWord_878360).sum := by decide
  have hdescent : baseEnd_878360 < baseStart_878360 := by decide
  rcases family_descends (prefixWord ++ tailWord_878360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878398 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_878398 : Nat := 118140960795 + 878398 * 2 ^ 59
def prefixEnd_878398 : Nat := 4983230072969 + 3 ^ 40 * 878398 * 2
def baseEnd_878398 : Nat := 400924782176141775542513

theorem tailTrace_878398 : CollatzResearch.WordTrace tailWord_878398 prefixEnd_878398 400924782176141775542513 := by
  unfold tailWord_878398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004725883965192409991481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21358538047814359519954565 4004725883965192409991481)
  ·
    refine ⟨3003544412973894307493611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4004725883965192409991481 3003544412973894307493611)
    ·
      refine ⟨4505316619460841461240417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003544412973894307493611 4505316619460841461240417)
      ·
        refine ⟨3378987464595631095930313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4505316619460841461240417 3378987464595631095930313)
        ·
          refine ⟨2534240598446723321947735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3378987464595631095930313 2534240598446723321947735)
          ·
            refine ⟨3801360897670084982921603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2534240598446723321947735 3801360897670084982921603)
            ·
              refine ⟨5702041346505127474382405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3801360897670084982921603 5702041346505127474382405)
              ·
                refine ⟨1069132752469711401446701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5702041346505127474382405 1069132752469711401446701)
                ·
                  refine ⟨400924782176141775542513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069132752469711401446701 400924782176141775542513)
                  ·
                    rfl

theorem cell20_878398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_878398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878398 prefixEnd_878398 := by exact prefixLift 878398
  have htrace : WordTrace (prefixWord ++ tailWord_878398) baseStart_878398 baseEnd_878398 := by
    simpa [prefixWord, tailWord_878398, baseEnd_878398] using wordTrace_append hprefix tailTrace_878398
  have hstable : (prefixWord ++ tailWord_878398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878398).length < 2 ^ (prefixWord ++ tailWord_878398).sum := by decide
  have hdescent : baseEnd_878398 < baseStart_878398 := by decide
  rcases family_descends (prefixWord ++ tailWord_878398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878405 : List Nat := [1, 3, 1, 1, 1, 2, 5, 4, 2]
def baseStart_878405 : Nat := 118140960795 + 878405 * 2 ^ 59
def prefixEnd_878405 : Nat := 4983230072969 + 3 ^ 40 * 878405 * 2
def baseEnd_878405 : Nat := 400927977166880862309151

theorem tailTrace_878405 : CollatzResearch.WordTrace tailWord_878405 prefixEnd_878405 400927977166880862309151 := by
  unfold tailWord_878405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32038062382696179475436669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21358708255130786316957779 32038062382696179475436669)
  ·
    refine ⟨12014273393511067303288751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32038062382696179475436669 12014273393511067303288751)
    ·
      refine ⟨18021410090266600954933127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014273393511067303288751 18021410090266600954933127)
      ·
        refine ⟨27032115135399901432399691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18021410090266600954933127 27032115135399901432399691)
        ·
          refine ⟨40548172703099852148599537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27032115135399901432399691 40548172703099852148599537)
          ·
            refine ⟨30411129527324889111449653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40548172703099852148599537 30411129527324889111449653)
            ·
              refine ⟨2851043393186708354198405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30411129527324889111449653 2851043393186708354198405)
              ·
                refine ⟨534570636222507816412201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2851043393186708354198405 534570636222507816412201)
                ·
                  refine ⟨400927977166880862309151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534570636222507816412201 400927977166880862309151)
                  ·
                    rfl

theorem cell20_878405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 4, 2].length) (baseStart_878405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878405 prefixEnd_878405 := by exact prefixLift 878405
  have htrace : WordTrace (prefixWord ++ tailWord_878405) baseStart_878405 baseEnd_878405 := by
    simpa [prefixWord, tailWord_878405, baseEnd_878405] using wordTrace_append hprefix tailTrace_878405
  have hstable : (prefixWord ++ tailWord_878405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878405).length < 2 ^ (prefixWord ++ tailWord_878405).sum := by decide
  have hdescent : baseEnd_878405 < baseStart_878405 := by decide
  rcases family_descends (prefixWord ++ tailWord_878405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878426 : List Nat := [3, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_878426 : Nat := 118140960795 + 878426 * 2 ^ 59
def prefixEnd_878426 : Nat := 4983230072969 + 3 ^ 40 * 878426 * 2
def baseEnd_878426 : Nat := 400937562139098122609065

theorem tailTrace_878426 : CollatzResearch.WordTrace tailWord_878426 prefixEnd_878426 400937562139098122609065 := by
  unfold tailWord_878426
  simp only [CollatzResearch.WordTrace]
  refine ⟨8009707078905025015487783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21359218877080066707967421 8009707078905025015487783)
  ·
    refine ⟨12014560618357537523231675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8009707078905025015487783 12014560618357537523231675)
    ·
      refine ⟨18021840927536306284847513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12014560618357537523231675 18021840927536306284847513)
      ·
        refine ⟨13516380695652229713635635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18021840927536306284847513 13516380695652229713635635)
        ·
          refine ⟨20274571043478344570453453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13516380695652229713635635 20274571043478344570453453)
          ·
            refine ⟨7602964141304379213920045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20274571043478344570453453 7602964141304379213920045)
            ·
              refine ⟨2851111552989142205220017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7602964141304379213920045 2851111552989142205220017)
              ·
                refine ⟨2138333664741856653915013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2851111552989142205220017 2138333664741856653915013)
                ·
                  refine ⟨400937562139098122609065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138333664741856653915013 400937562139098122609065)
                  ·
                    rfl

theorem cell20_878426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_878426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878426 prefixEnd_878426 := by exact prefixLift 878426
  have htrace : WordTrace (prefixWord ++ tailWord_878426) baseStart_878426 baseEnd_878426 := by
    simpa [prefixWord, tailWord_878426, baseEnd_878426] using wordTrace_append hprefix tailTrace_878426
  have hstable : (prefixWord ++ tailWord_878426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878426).length < 2 ^ (prefixWord ++ tailWord_878426).sum := by decide
  have hdescent : baseEnd_878426 < baseStart_878426 := by decide
  rcases family_descends (prefixWord ++ tailWord_878426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878464 : List Nat := [2, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_878464 : Nat := 118140960795 + 878464 * 2 ^ 59
def prefixEnd_878464 : Nat := 4983230072969 + 3 ^ 40 * 878464 * 2
def baseEnd_878464 : Nat := 400954906374538879342243

theorem tailTrace_878464 : CollatzResearch.WordTrace tailWord_878464 prefixEnd_878464 400954906374538879342243 := by
  unfold tailWord_878464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16020107144741216275917223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21360142859654955034556297 16020107144741216275917223)
  ·
    refine ⟨24030160717111824413875835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16020107144741216275917223 24030160717111824413875835)
    ·
      refine ⟨36045241075667736620813753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24030160717111824413875835 36045241075667736620813753)
      ·
        refine ⟨27033930806750802465610315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36045241075667736620813753 27033930806750802465610315)
        ·
          refine ⟨40550896210126203698415473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27033930806750802465610315 40550896210126203698415473)
          ·
            refine ⟨30413172157594652773811605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40550896210126203698415473 30413172157594652773811605)
            ·
              refine ⟨1425617444887249348772419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30413172157594652773811605 1425617444887249348772419)
              ·
                refine ⟨2138426167330874023158629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425617444887249348772419 2138426167330874023158629)
                ·
                  refine ⟨400954906374538879342243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138426167330874023158629 400954906374538879342243)
                  ·
                    rfl

theorem cell20_878464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_878464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878464 prefixEnd_878464 := by exact prefixLift 878464
  have htrace : WordTrace (prefixWord ++ tailWord_878464) baseStart_878464 baseEnd_878464 := by
    simpa [prefixWord, tailWord_878464, baseEnd_878464] using wordTrace_append hprefix tailTrace_878464
  have hstable : (prefixWord ++ tailWord_878464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878464).length < 2 ^ (prefixWord ++ tailWord_878464).sum := by decide
  have hdescent : baseEnd_878464 < baseStart_878464 := by decide
  rcases family_descends (prefixWord ++ tailWord_878464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878526 : List Nat := [4, 2, 1, 1, 1, 4, 2, 5]
def baseStart_878526 : Nat := 118140960795 + 878526 * 2 ^ 59
def prefixEnd_878526 : Nat := 4983230072969 + 3 ^ 40 * 878526 * 2
def baseEnd_878526 : Nat := 133661068287980739758441

theorem tailTrace_878526 : CollatzResearch.WordTrace tailWord_878526 prefixEnd_878526 133661068287980739758441 := by
  unfold tailWord_878526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005309451907227142573929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21361650410171878093727621 4005309451907227142573929)
  ·
    refine ⟨3003982088930420356930447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4005309451907227142573929 3003982088930420356930447)
    ·
      refine ⟨4505973133395630535395671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3003982088930420356930447 4505973133395630535395671)
      ·
        refine ⟨6758959700093445803093507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4505973133395630535395671 6758959700093445803093507)
        ·
          refine ⟨10138439550140168704640261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6758959700093445803093507 10138439550140168704640261)
          ·
            refine ⟨1900957415651281632120049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10138439550140168704640261 1900957415651281632120049)
            ·
              refine ⟨1425718061738461224090037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1900957415651281632120049 1425718061738461224090037)
              ·
                refine ⟨133661068287980739758441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1425718061738461224090037 133661068287980739758441)
                ·
                  rfl

theorem cell20_878526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_878526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878526 prefixEnd_878526 := by exact prefixLift 878526
  have htrace : WordTrace (prefixWord ++ tailWord_878526) baseStart_878526 baseEnd_878526 := by
    simpa [prefixWord, tailWord_878526, baseEnd_878526] using wordTrace_append hprefix tailTrace_878526
  have hstable : (prefixWord ++ tailWord_878526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878526).length < 2 ^ (prefixWord ++ tailWord_878526).sum := by decide
  have hdescent : baseEnd_878526 < baseStart_878526 := by decide
  rcases family_descends (prefixWord ++ tailWord_878526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878574 : List Nat := [4, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_878574 : Nat := 118140960795 + 878574 * 2 ^ 59
def prefixEnd_878574 : Nat := 4983230072969 + 3 ^ 40 * 878574 * 2
def baseEnd_878574 : Nat := 401005113371867385675127

theorem tailTrace_878574 : CollatzResearch.WordTrace tailWord_878574 prefixEnd_878574 401005113371867385675127 := by
  unfold tailWord_878574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005528289885490167292347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21362817546055947558892517 4005528289885490167292347)
  ·
    refine ⟨6008292434828235250938521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005528289885490167292347 6008292434828235250938521)
    ·
      refine ⟨4506219326121176438203891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6008292434828235250938521 4506219326121176438203891)
      ·
        refine ⟨6759328989181764657305837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4506219326121176438203891 6759328989181764657305837)
        ·
          refine ⟨2534748370943161746489689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6759328989181764657305837 2534748370943161746489689)
          ·
            refine ⟨1901061278207371309867267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2534748370943161746489689 1901061278207371309867267)
            ·
              refine ⟨2851591917311056964800901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1901061278207371309867267 2851591917311056964800901)
              ·
                refine ⟨534673484495823180900169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2851591917311056964800901 534673484495823180900169)
                ·
                  refine ⟨401005113371867385675127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534673484495823180900169 401005113371867385675127)
                  ·
                    rfl

theorem cell20_878574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_878574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878574 prefixEnd_878574 := by exact prefixLift 878574
  have htrace : WordTrace (prefixWord ++ tailWord_878574) baseStart_878574 baseEnd_878574 := by
    simpa [prefixWord, tailWord_878574, baseEnd_878574] using wordTrace_append hprefix tailTrace_878574
  have hstable : (prefixWord ++ tailWord_878574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878574).length < 2 ^ (prefixWord ++ tailWord_878574).sum := by decide
  have hdescent : baseEnd_878574 < baseStart_878574 := by decide
  rcases family_descends (prefixWord ++ tailWord_878574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878585 : List Nat := [1, 2, 1, 3, 1, 4, 3, 5]
def baseStart_878585 : Nat := 118140960795 + 878585 * 2 ^ 59
def prefixEnd_878585 : Nat := 4983230072969 + 3 ^ 40 * 878585 * 2
def baseEnd_878585 : Nat := 133670044690533412102805

theorem tailTrace_878585 : CollatzResearch.WordTrace tailWord_878585 prefixEnd_878585 133670044690533412102805 := by
  unfold tailWord_878585
  simp only [CollatzResearch.WordTrace]
  refine ⟨32044627522044070216989209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21363085014696046811326139 32044627522044070216989209)
  ·
    refine ⟨24033470641533052662741907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32044627522044070216989209 24033470641533052662741907)
    ·
      refine ⟨36050205962299578994112861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24033470641533052662741907 36050205962299578994112861)
      ·
        refine ⟨13518827235862342122792323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36050205962299578994112861 13518827235862342122792323)
        ·
          refine ⟨20278240853793513184188485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13518827235862342122792323 20278240853793513184188485)
          ·
            refine ⟨3802170160086283722035341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20278240853793513184188485 3802170160086283722035341)
            ·
              refine ⟨1425813810032356395763253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3802170160086283722035341 1425813810032356395763253)
              ·
                refine ⟨133670044690533412102805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1425813810032356395763253 133670044690533412102805)
                ·
                  rfl

theorem cell20_878585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 5].length) (baseStart_878585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878585 prefixEnd_878585 := by exact prefixLift 878585
  have htrace : WordTrace (prefixWord ++ tailWord_878585) baseStart_878585 baseEnd_878585 := by
    simpa [prefixWord, tailWord_878585, baseEnd_878585] using wordTrace_append hprefix tailTrace_878585
  have hstable : (prefixWord ++ tailWord_878585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878585).length < 2 ^ (prefixWord ++ tailWord_878585).sum := by decide
  have hdescent : baseEnd_878585 < baseStart_878585 := by decide
  rcases family_descends (prefixWord ++ tailWord_878585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878657 : List Nat := [1, 2, 5, 1, 2, 3, 2, 4]
def baseStart_878657 : Nat := 118140960795 + 878657 * 2 ^ 59
def prefixEnd_878657 : Nat := 4983230072969 + 3 ^ 40 * 878657 * 2
def baseEnd_878657 : Nat := 133680998944495995302707

theorem tailTrace_878657 : CollatzResearch.WordTrace tailWord_878657 prefixEnd_878657 133680998944495995302707 := by
  unfold tailWord_878657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32047253577783226513610225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21364835718522151009073483 32047253577783226513610225)
  ·
    refine ⟨24035440183337419885207669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32047253577783226513610225 24035440183337419885207669)
    ·
      refine ⟨2253322517187883114238219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24035440183337419885207669 2253322517187883114238219)
      ·
        refine ⟨3379983775781824671357329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253322517187883114238219 3379983775781824671357329)
        ·
          refine ⟨2534987831836368503517997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3379983775781824671357329 2534987831836368503517997)
          ·
            refine ⟨950620436938638188819249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2534987831836368503517997 950620436938638188819249)
            ·
              refine ⟨712965327703978641614437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950620436938638188819249 712965327703978641614437)
              ·
                refine ⟨133680998944495995302707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 712965327703978641614437 133680998944495995302707)
                ·
                  rfl

theorem cell20_878657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 4].length) (baseStart_878657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878657 prefixEnd_878657 := by exact prefixLift 878657
  have htrace : WordTrace (prefixWord ++ tailWord_878657) baseStart_878657 baseEnd_878657 := by
    simpa [prefixWord, tailWord_878657, baseEnd_878657] using wordTrace_append hprefix tailTrace_878657
  have hstable : (prefixWord ++ tailWord_878657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878657).length < 2 ^ (prefixWord ++ tailWord_878657).sum := by decide
  have hdescent : baseEnd_878657 < baseStart_878657 := by decide
  rcases family_descends (prefixWord ++ tailWord_878657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878668 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_878668 : Nat := 118140960795 + 878668 * 2 ^ 59
def prefixEnd_878668 : Nat := 4983230072969 + 3 ^ 40 * 878668 * 2
def baseEnd_878668 : Nat := 401048017533220836541409

theorem tailTrace_878668 : CollatzResearch.WordTrace tailWord_878668 prefixEnd_878668 401048017533220836541409 := by
  unfold tailWord_878668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16023827390371687696130329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21365103187162250261507105 16023827390371687696130329)
  ·
    refine ⟨12017870542778765772097747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16023827390371687696130329 12017870542778765772097747)
    ·
      refine ⟨18026805814168148658146621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12017870542778765772097747 18026805814168148658146621)
      ·
        refine ⟨6760052180313055746804983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18026805814168148658146621 6760052180313055746804983)
        ·
          refine ⟨10140078270469583620207475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6760052180313055746804983 10140078270469583620207475)
          ·
            refine ⟨15210117405704375430311213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140078270469583620207475 15210117405704375430311213)
            ·
              refine ⟨5703794027139140786366705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15210117405704375430311213 5703794027139140786366705)
              ·
                refine ⟨4277845520354355589775029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5703794027139140786366705 4277845520354355589775029)
                ·
                  refine ⟨401048017533220836541409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4277845520354355589775029 401048017533220836541409)
                  ·
                    rfl

theorem cell20_878668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_878668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878668 prefixEnd_878668 := by exact prefixLift 878668
  have htrace : WordTrace (prefixWord ++ tailWord_878668) baseStart_878668 baseEnd_878668 := by
    simpa [prefixWord, tailWord_878668, baseEnd_878668] using wordTrace_append hprefix tailTrace_878668
  have hstable : (prefixWord ++ tailWord_878668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878668).length < 2 ^ (prefixWord ++ tailWord_878668).sum := by decide
  have hdescent : baseEnd_878668 < baseStart_878668 := by decide
  rcases family_descends (prefixWord ++ tailWord_878668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878688 : List Nat := [2, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_878688 : Nat := 118140960795 + 878688 * 2 ^ 59
def prefixEnd_878688 : Nat := 4983230072969 + 3 ^ 40 * 878688 * 2
def baseEnd_878688 : Nat := 401057146078189655874661

theorem tailTrace_878688 : CollatzResearch.WordTrace tailWord_878688 prefixEnd_878688 401057146078189655874661 := by
  unfold tailWord_878688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024192120335459403994359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21365589493780612538659145 16024192120335459403994359)
  ·
    refine ⟨24036288180503189105991539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16024192120335459403994359 24036288180503189105991539)
    ·
      refine ⟨36054432270754783658987309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24036288180503189105991539 36054432270754783658987309)
      ·
        refine ⟨13520412101533043872120241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36054432270754783658987309 13520412101533043872120241)
        ·
          refine ⟨10140309076149782904090181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13520412101533043872120241 10140309076149782904090181)
          ·
            refine ⟨1901307951778084294516909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10140309076149782904090181 1901307951778084294516909)
            ·
              refine ⟨712990481916781610443841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901307951778084294516909 712990481916781610443841)
              ·
                refine ⟨534742861437586207832881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 712990481916781610443841 534742861437586207832881)
                ·
                  refine ⟨401057146078189655874661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534742861437586207832881 401057146078189655874661)
                  ·
                    rfl

theorem cell20_878688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_878688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878688 prefixEnd_878688 := by exact prefixLift 878688
  have htrace : WordTrace (prefixWord ++ tailWord_878688) baseStart_878688 baseEnd_878688 := by
    simpa [prefixWord, tailWord_878688, baseEnd_878688] using wordTrace_append hprefix tailTrace_878688
  have hstable : (prefixWord ++ tailWord_878688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878688).length < 2 ^ (prefixWord ++ tailWord_878688).sum := by decide
  have hdescent : baseEnd_878688 < baseStart_878688 := by decide
  rcases family_descends (prefixWord ++ tailWord_878688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878692 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_878692 : Nat := 118140960795 + 878692 * 2 ^ 59
def prefixEnd_878692 : Nat := 4983230072969 + 3 ^ 40 * 878692 * 2
def baseEnd_878692 : Nat := 401058971787183419741311

theorem tailTrace_878692 : CollatzResearch.WordTrace tailWord_878692 prefixEnd_878692 401058971787183419741311 := by
  unfold tailWord_878692
  simp only [CollatzResearch.WordTrace]
  refine ⟨16024265066328213745567165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21365686755104284994089553 16024265066328213745567165)
  ·
    refine ⟨6009099399873080154587687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16024265066328213745567165 6009099399873080154587687)
    ·
      refine ⟨9013649099809620231881531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6009099399873080154587687 9013649099809620231881531)
      ·
        refine ⟨13520473649714430347822297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9013649099809620231881531 13520473649714430347822297)
        ·
          refine ⟨10140355237285822760866723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13520473649714430347822297 10140355237285822760866723)
          ·
            refine ⟨15210532855928734141300085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10140355237285822760866723 15210532855928734141300085)
            ·
              refine ⟨1425987455243318825746883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15210532855928734141300085 1425987455243318825746883)
              ·
                refine ⟨2138981182864978238620325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1425987455243318825746883 2138981182864978238620325)
                ·
                  refine ⟨401058971787183419741311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2138981182864978238620325 401058971787183419741311)
                  ·
                    rfl

theorem cell20_878692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_878692 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878692 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878692 prefixEnd_878692 := by exact prefixLift 878692
  have htrace : WordTrace (prefixWord ++ tailWord_878692) baseStart_878692 baseEnd_878692 := by
    simpa [prefixWord, tailWord_878692, baseEnd_878692] using wordTrace_append hprefix tailTrace_878692
  have hstable : (prefixWord ++ tailWord_878692).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878692).length < 2 ^ (prefixWord ++ tailWord_878692).sum := by decide
  have hdescent : baseEnd_878692 < baseStart_878692 := by decide
  rcases family_descends (prefixWord ++ tailWord_878692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878698 : List Nat := [3, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_878698 : Nat := 118140960795 + 878698 * 2 ^ 59
def prefixEnd_878698 : Nat := 4983230072969 + 3 ^ 40 * 878698 * 2
def baseEnd_878698 : Nat := 401061710350674065541287

theorem tailTrace_878698 : CollatzResearch.WordTrace tailWord_878698 prefixEnd_878698 401061710350674065541287 := by
  unfold tailWord_878698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012187242658672628963187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21365832647089793677235165 8012187242658672628963187)
  ·
    refine ⟨12018280863988008943444781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8012187242658672628963187 12018280863988008943444781)
    ·
      refine ⟨4506855323995503353791793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12018280863988008943444781 4506855323995503353791793)
      ·
        refine ⟨3380141492996627515343845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4506855323995503353791793 3380141492996627515343845)
        ·
          refine ⟨633776529936867659126971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3380141492996627515343845 633776529936867659126971)
          ·
            refine ⟨950664794905301488690457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633776529936867659126971 950664794905301488690457)
            ·
              refine ⟨712998596178976116517843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950664794905301488690457 712998596178976116517843)
              ·
                refine ⟨1069497894268464174776765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712998596178976116517843 1069497894268464174776765)
                ·
                  refine ⟨401061710350674065541287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069497894268464174776765 401061710350674065541287)
                  ·
                    rfl

theorem cell20_878698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_878698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878698 prefixEnd_878698 := by exact prefixLift 878698
  have htrace : WordTrace (prefixWord ++ tailWord_878698) baseStart_878698 baseEnd_878698 := by
    simpa [prefixWord, tailWord_878698, baseEnd_878698] using wordTrace_append hprefix tailTrace_878698
  have hstable : (prefixWord ++ tailWord_878698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878698).length < 2 ^ (prefixWord ++ tailWord_878698).sum := by decide
  have hdescent : baseEnd_878698 < baseStart_878698 := by decide
  rcases family_descends (prefixWord ++ tailWord_878698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878743 : List Nat := [1, 1, 3, 3, 4, 2, 2, 2, 2]
def baseStart_878743 : Nat := 118140960795 + 878743 * 2 ^ 59
def prefixEnd_878743 : Nat := 4983230072969 + 3 ^ 40 * 878743 * 2
def baseEnd_878743 : Nat := 401082249576853909041103

theorem tailTrace_878743 : CollatzResearch.WordTrace tailWord_878743 prefixEnd_878743 401082249576853909041103 := by
  unfold tailWord_878743
  simp only [CollatzResearch.WordTrace]
  refine ⟨32050390255471663201240883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21366926836981108800827255 32050390255471663201240883)
  ·
    refine ⟨48075585383207494801861325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32050390255471663201240883 48075585383207494801861325)
    ·
      refine ⟨18028344518702810550697997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48075585383207494801861325 18028344518702810550697997)
      ·
        refine ⟨6760629194513553956511749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18028344518702810550697997 6760629194513553956511749)
        ·
          refine ⟨1267617973971291366845953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6760629194513553956511749 1267617973971291366845953)
          ·
            refine ⟨950713480478468525134465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1267617973971291366845953 950713480478468525134465)
            ·
              refine ⟨713035110358851393850849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 950713480478468525134465 713035110358851393850849)
              ·
                refine ⟨534776332769138545388137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713035110358851393850849 534776332769138545388137)
                ·
                  refine ⟨401082249576853909041103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534776332769138545388137 401082249576853909041103)
                  ·
                    rfl

theorem cell20_878743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 2, 2, 2].length) (baseStart_878743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878743 prefixEnd_878743 := by exact prefixLift 878743
  have htrace : WordTrace (prefixWord ++ tailWord_878743) baseStart_878743 baseEnd_878743 := by
    simpa [prefixWord, tailWord_878743, baseEnd_878743] using wordTrace_append hprefix tailTrace_878743
  have hstable : (prefixWord ++ tailWord_878743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878743).length < 2 ^ (prefixWord ++ tailWord_878743).sum := by decide
  have hdescent : baseEnd_878743 < baseStart_878743 := by decide
  rcases family_descends (prefixWord ++ tailWord_878743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878750 : List Nat := [4, 3, 1, 1, 4, 1, 1, 5]
def baseStart_878750 : Nat := 118140960795 + 878750 * 2 ^ 59
def prefixEnd_878750 : Nat := 4983230072969 + 3 ^ 40 * 878750 * 2
def baseEnd_878750 : Nat := 133695148189197665269247

theorem tailTrace_878750 : CollatzResearch.WordTrace tailWord_878750 prefixEnd_878750 133695148189197665269247 := by
  unfold tailWord_878750
  simp only [CollatzResearch.WordTrace]
  refine ⟨4006330695805787924593213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21367097044297535597830469 4006330695805787924593213)
  ·
    refine ⟨1502374010927170471722455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4006330695805787924593213 1502374010927170471722455)
    ·
      refine ⟨2253561016390755707583683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502374010927170471722455 2253561016390755707583683)
      ·
        refine ⟨3380341524586133561375525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2253561016390755707583683 3380341524586133561375525)
        ·
          refine ⟨633814035859900042757911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3380341524586133561375525 633814035859900042757911)
          ·
            refine ⟨950721053789850064136867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633814035859900042757911 950721053789850064136867)
            ·
              refine ⟨1426081580684775096205301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950721053789850064136867 1426081580684775096205301)
              ·
                refine ⟨133695148189197665269247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1426081580684775096205301 133695148189197665269247)
                ·
                  rfl

theorem cell20_878750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_878750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878750 prefixEnd_878750 := by exact prefixLift 878750
  have htrace : WordTrace (prefixWord ++ tailWord_878750) baseStart_878750 baseEnd_878750 := by
    simpa [prefixWord, tailWord_878750, baseEnd_878750] using wordTrace_append hprefix tailTrace_878750
  have hstable : (prefixWord ++ tailWord_878750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878750).length < 2 ^ (prefixWord ++ tailWord_878750).sum := by decide
  have hdescent : baseEnd_878750 < baseStart_878750 := by decide
  rcases family_descends (prefixWord ++ tailWord_878750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878754 : List Nat := [3, 3, 1, 3, 1, 1, 3, 5]
def baseStart_878754 : Nat := 118140960795 + 878754 * 2 ^ 59
def prefixEnd_878754 : Nat := 4983230072969 + 3 ^ 40 * 878754 * 2
def baseEnd_878754 : Nat := 133695756758862253224797

theorem tailTrace_878754 : CollatzResearch.WordTrace tailWord_878754 prefixEnd_878754 133695756758862253224797 := by
  unfold tailWord_878754
  simp only [CollatzResearch.WordTrace]
  refine ⟨8012697864607953019972829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21367194305621208053260877 8012697864607953019972829)
  ·
    refine ⟨3004761699227982382489811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8012697864607953019972829 3004761699227982382489811)
    ·
      refine ⟨4507142548841973573734717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3004761699227982382489811 4507142548841973573734717)
      ·
        refine ⟨1690178455815740090150519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4507142548841973573734717 1690178455815740090150519)
        ·
          refine ⟨2535267683723610135225779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690178455815740090150519 2535267683723610135225779)
          ·
            refine ⟨3802901525585415202838669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2535267683723610135225779 3802901525585415202838669)
            ·
              refine ⟨1426088072094530701064501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3802901525585415202838669 1426088072094530701064501)
              ·
                refine ⟨133695756758862253224797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1426088072094530701064501 133695756758862253224797)
                ·
                  rfl

theorem cell20_878754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_878754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878754 prefixEnd_878754 := by exact prefixLift 878754
  have htrace : WordTrace (prefixWord ++ tailWord_878754) baseStart_878754 baseEnd_878754 := by
    simpa [prefixWord, tailWord_878754, baseEnd_878754] using wordTrace_append hprefix tailTrace_878754
  have hstable : (prefixWord ++ tailWord_878754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878754).length < 2 ^ (prefixWord ++ tailWord_878754).sum := by decide
  have hdescent : baseEnd_878754 < baseStart_878754 := by decide
  rcases family_descends (prefixWord ++ tailWord_878754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878812 : List Nat := [2, 2, 5, 2, 1, 1, 3, 1, 3]
def baseStart_878812 : Nat := 118140960795 + 878812 * 2 ^ 59
def prefixEnd_878812 : Nat := 4983230072969 + 3 ^ 40 * 878812 * 2
def baseEnd_878812 : Nat := 401113743056996335740821

theorem tailTrace_878812 : CollatzResearch.WordTrace tailWord_878812 prefixEnd_878812 401113743056996335740821 := by
  unfold tailWord_878812
  simp only [CollatzResearch.WordTrace]
  refine ⟨16026453446110843992751345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21368604594814458657001793 16026453446110843992751345)
  ·
    refine ⟨12019840084583132994563509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16026453446110843992751345 12019840084583132994563509)
    ·
      refine ⟨1126860007929668718240329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12019840084583132994563509 1126860007929668718240329)
      ·
        refine ⟨845145005947251538680247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1126860007929668718240329 845145005947251538680247)
        ·
          refine ⟨1267717508920877308020371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845145005947251538680247 1267717508920877308020371)
          ·
            refine ⟨1901576263381315962030557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267717508920877308020371 1901576263381315962030557)
            ·
              refine ⟨713091098767993485761459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901576263381315962030557 713091098767993485761459)
              ·
                refine ⟨1069636648151990228642189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713091098767993485761459 1069636648151990228642189)
                ·
                  refine ⟨401113743056996335740821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069636648151990228642189 401113743056996335740821)
                  ·
                    rfl

theorem cell20_878812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_878812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878812 prefixEnd_878812 := by exact prefixLift 878812
  have htrace : WordTrace (prefixWord ++ tailWord_878812) baseStart_878812 baseEnd_878812 := by
    simpa [prefixWord, tailWord_878812, baseEnd_878812] using wordTrace_append hprefix tailTrace_878812
  have hstable : (prefixWord ++ tailWord_878812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878812).length < 2 ^ (prefixWord ++ tailWord_878812).sum := by decide
  have hdescent : baseEnd_878812 < baseStart_878812 := by decide
  rcases family_descends (prefixWord ++ tailWord_878812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878827 : List Nat := [1, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_878827 : Nat := 118140960795 + 878827 * 2 ^ 59
def prefixEnd_878827 : Nat := 4983230072969 + 3 ^ 40 * 878827 * 2
def baseEnd_878827 : Nat := 401120589465722950240759

theorem tailTrace_878827 : CollatzResearch.WordTrace tailWord_878827 prefixEnd_878827 401120589465722950240759 := by
  unfold tailWord_878827
  simp only [CollatzResearch.WordTrace]
  refine ⟨32053453987167345547298735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21368969324778230364865823 32053453987167345547298735)
  ·
    refine ⟨48080180980751018320948103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32053453987167345547298735 48080180980751018320948103)
    ·
      refine ⟨72120271471126527481422155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48080180980751018320948103 72120271471126527481422155)
      ·
        refine ⟨108180407206689791222133233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72120271471126527481422155 108180407206689791222133233)
        ·
          refine ⟨81135305405017343416599925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108180407206689791222133233 81135305405017343416599925)
          ·
            refine ⟨7606434881720375945306243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81135305405017343416599925 7606434881720375945306243)
            ·
              refine ⟨11409652322580563917959365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7606434881720375945306243 11409652322580563917959365)
              ·
                refine ⟨2139309810483855734617381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11409652322580563917959365 2139309810483855734617381)
                ·
                  refine ⟨401120589465722950240759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2139309810483855734617381 401120589465722950240759)
                  ·
                    rfl

theorem cell20_878827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_878827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878827 prefixEnd_878827 := by exact prefixLift 878827
  have htrace : WordTrace (prefixWord ++ tailWord_878827) baseStart_878827 baseEnd_878827 := by
    simpa [prefixWord, tailWord_878827, baseEnd_878827] using wordTrace_append hprefix tailTrace_878827
  have hstable : (prefixWord ++ tailWord_878827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878827).length < 2 ^ (prefixWord ++ tailWord_878827).sum := by decide
  have hdescent : baseEnd_878827 < baseStart_878827 := by decide
  rcases family_descends (prefixWord ++ tailWord_878827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878858 : List Nat := [3, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_878858 : Nat := 118140960795 + 878858 * 2 ^ 59
def prefixEnd_878858 : Nat := 4983230072969 + 3 ^ 40 * 878858 * 2
def baseEnd_878858 : Nat := 401134738710424620207299

theorem tailTrace_878858 : CollatzResearch.WordTrace tailWord_878858 prefixEnd_878858 401134738710424620207299 := by
  unfold tailWord_878858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013646162513759460419307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21369723100036691894451485 8013646162513759460419307)
  ·
    refine ⟨12020469243770639190628961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8013646162513759460419307 12020469243770639190628961)
    ·
      refine ⟨9015351932827979392971721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12020469243770639190628961 9015351932827979392971721)
      ·
        refine ⟨6761513949620984544728791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9015351932827979392971721 6761513949620984544728791)
        ·
          refine ⟨10142270924431476817093187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6761513949620984544728791 10142270924431476817093187)
          ·
            refine ⟨15213406386647215225639781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10142270924431476817093187 15213406386647215225639781)
            ·
              refine ⟨2852513697496352854807459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15213406386647215225639781 2852513697496352854807459)
              ·
                refine ⟨4278770546244529282211189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2852513697496352854807459 4278770546244529282211189)
                ·
                  refine ⟨401134738710424620207299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4278770546244529282211189 401134738710424620207299)
                  ·
                    rfl

theorem cell20_878858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_878858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878858 prefixEnd_878858 := by exact prefixLift 878858
  have htrace : WordTrace (prefixWord ++ tailWord_878858) baseStart_878858 baseEnd_878858 := by
    simpa [prefixWord, tailWord_878858, baseEnd_878858] using wordTrace_append hprefix tailTrace_878858
  have hstable : (prefixWord ++ tailWord_878858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878858).length < 2 ^ (prefixWord ++ tailWord_878858).sum := by decide
  have hdescent : baseEnd_878858 < baseStart_878858 := by decide
  rcases family_descends (prefixWord ++ tailWord_878858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878875 : List Nat := [1, 1, 1, 1, 1, 1, 10, 1, 3]
def baseStart_878875 : Nat := 118140960795 + 878875 * 2 ^ 59
def prefixEnd_878875 : Nat := 4983230072969 + 3 ^ 40 * 878875 * 2
def baseEnd_878875 : Nat := 401142497973648116640563

theorem tailTrace_878875 : CollatzResearch.WordTrace tailWord_878875 prefixEnd_878875 401142497973648116640563 := by
  unfold tailWord_878875
  simp only [CollatzResearch.WordTrace]
  refine ⟨32055204690993449745046079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21370136460662299830030719 32055204690993449745046079)
  ·
    refine ⟨48082807036490174617569119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32055204690993449745046079 48082807036490174617569119)
    ·
      refine ⟨72124210554735261926353679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48082807036490174617569119 72124210554735261926353679)
      ·
        refine ⟨108186315832102892889530519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72124210554735261926353679 108186315832102892889530519)
        ·
          refine ⟨162279473748154339334295779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 108186315832102892889530519 162279473748154339334295779)
          ·
            refine ⟨243419210622231509001443669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 162279473748154339334295779 243419210622231509001443669)
            ·
              refine ⟨713142218619818874027667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 243419210622231509001443669 713142218619818874027667)
              ·
                refine ⟨1069713327929728311041501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713142218619818874027667 1069713327929728311041501)
                ·
                  refine ⟨401142497973648116640563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069713327929728311041501 401142497973648116640563)
                  ·
                    rfl

theorem cell20_878875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 10, 1, 3].length) (baseStart_878875 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878875 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878875 prefixEnd_878875 := by exact prefixLift 878875
  have htrace : WordTrace (prefixWord ++ tailWord_878875) baseStart_878875 baseEnd_878875 := by
    simpa [prefixWord, tailWord_878875, baseEnd_878875] using wordTrace_append hprefix tailTrace_878875
  have hstable : (prefixWord ++ tailWord_878875).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878875).length < 2 ^ (prefixWord ++ tailWord_878875).sum := by decide
  have hdescent : baseEnd_878875 < baseStart_878875 := by decide
  rcases family_descends (prefixWord ++ tailWord_878875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878944 : List Nat := [2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_878944 : Nat := 118140960795 + 878944 * 2 ^ 59
def prefixEnd_878944 : Nat := 4983230072969 + 3 ^ 40 * 878944 * 2
def baseEnd_878944 : Nat := 133724663817930181113427

theorem tailTrace_878944 : CollatzResearch.WordTrace tailWord_878944 prefixEnd_878944 133724663817930181113427 := by
  unfold tailWord_878944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16028860663871737264653943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21371814218495649686205257 16028860663871737264653943)
  ·
    refine ⟨24043290995807605896980915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16028860663871737264653943 24043290995807605896980915)
    ·
      refine ⟨36064936493711408845471373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24043290995807605896980915 36064936493711408845471373)
      ·
        refine ⟨13524351185141778317051765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36064936493711408845471373 13524351185141778317051765)
        ·
          refine ⟨1267907923607041717223603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13524351185141778317051765 1267907923607041717223603)
          ·
            refine ⟨1901861885410562575835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1267907923607041717223603 1901861885410562575835405)
            ·
              refine ⟨713198207028960965938277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1901861885410562575835405 713198207028960965938277)
              ·
                refine ⟨133724663817930181113427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713198207028960965938277 133724663817930181113427)
                ·
                  rfl

theorem cell20_878944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_878944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878944 prefixEnd_878944 := by exact prefixLift 878944
  have htrace : WordTrace (prefixWord ++ tailWord_878944) baseStart_878944 baseEnd_878944 := by
    simpa [prefixWord, tailWord_878944, baseEnd_878944] using wordTrace_append hprefix tailTrace_878944
  have hstable : (prefixWord ++ tailWord_878944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878944).length < 2 ^ (prefixWord ++ tailWord_878944).sum := by decide
  have hdescent : baseEnd_878944 < baseStart_878944 := by decide
  rcases family_descends (prefixWord ++ tailWord_878944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878954 : List Nat := [3, 1, 3, 3, 1, 2, 2, 3, 2]
def baseStart_878954 : Nat := 118140960795 + 878954 * 2 ^ 59
def prefixEnd_878954 : Nat := 4983230072969 + 3 ^ 40 * 878954 * 2
def baseEnd_878954 : Nat := 401178555726274953006907

theorem tailTrace_878954 : CollatzResearch.WordTrace tailWord_878954 prefixEnd_878954 401178555726274953006907 := by
  unfold tailWord_878954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8014521514426811559292979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21372057371804830824781277 8014521514426811559292979)
  ·
    refine ⟨12021782271640217338939469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8014521514426811559292979 12021782271640217338939469)
    ·
      refine ⟨4508168351865081502102301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12021782271640217338939469 4508168351865081502102301)
      ·
        refine ⟨1690563131949405563288363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4508168351865081502102301 1690563131949405563288363)
        ·
          refine ⟨2535844697924108344932545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690563131949405563288363 2535844697924108344932545)
          ·
            refine ⟨1901883523443081258699409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535844697924108344932545 1901883523443081258699409)
            ·
              refine ⟨1426412642582310944024557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1901883523443081258699409 1426412642582310944024557)
              ·
                refine ⟨534904740968366604009209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426412642582310944024557 534904740968366604009209)
                ·
                  refine ⟨401178555726274953006907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534904740968366604009209 401178555726274953006907)
                  ·
                    rfl

theorem cell20_878954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_878954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878954 prefixEnd_878954 := by exact prefixLift 878954
  have htrace : WordTrace (prefixWord ++ tailWord_878954) baseStart_878954 baseEnd_878954 := by
    simpa [prefixWord, tailWord_878954, baseEnd_878954] using wordTrace_append hprefix tailTrace_878954
  have hstable : (prefixWord ++ tailWord_878954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878954).length < 2 ^ (prefixWord ++ tailWord_878954).sum := by decide
  have hdescent : baseEnd_878954 < baseStart_878954 := by decide
  rcases family_descends (prefixWord ++ tailWord_878954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878955 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_878955 : Nat := 118140960795 + 878955 * 2 ^ 59
def prefixEnd_878955 : Nat := 4983230072969 + 3 ^ 40 * 878955 * 2
def baseEnd_878955 : Nat := 401179012153523393973569

theorem tailTrace_878955 : CollatzResearch.WordTrace tailWord_878955 prefixEnd_878955 401179012153523393973569 := by
  unfold tailWord_878955
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058122530703623407958319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21372081687135748938638879 32058122530703623407958319)
  ·
    refine ⟨48087183796055435111937479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32058122530703623407958319 48087183796055435111937479)
    ·
      refine ⟨72130775694083152667906219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48087183796055435111937479 72130775694083152667906219)
      ·
        refine ⟨108196163541124729001859329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72130775694083152667906219 108196163541124729001859329)
        ·
          refine ⟨81147122655843546751394497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108196163541124729001859329 81147122655843546751394497)
          ·
            refine ⟨60860341991882660063545873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81147122655843546751394497 60860341991882660063545873)
            ·
              refine ⟨45645256493911995047659405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60860341991882660063545873 45645256493911995047659405)
              ·
                refine ⟨17116971185216998142872277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45645256493911995047659405 17116971185216998142872277)
                ·
                  refine ⟨401179012153523393973569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17116971185216998142872277 401179012153523393973569)
                  ·
                    rfl

theorem cell20_878955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_878955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878955 prefixEnd_878955 := by exact prefixLift 878955
  have htrace : WordTrace (prefixWord ++ tailWord_878955) baseStart_878955 baseEnd_878955 := by
    simpa [prefixWord, tailWord_878955, baseEnd_878955] using wordTrace_append hprefix tailTrace_878955
  have hstable : (prefixWord ++ tailWord_878955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878955).length < 2 ^ (prefixWord ++ tailWord_878955).sum := by decide
  have hdescent : baseEnd_878955 < baseStart_878955 := by decide
  rcases family_descends (prefixWord ++ tailWord_878955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878965 : List Nat := [1, 3, 4, 1, 2, 2, 7]
def baseStart_878965 : Nat := 118140960795 + 878965 * 2 ^ 59
def prefixEnd_878965 : Nat := 4983230072969 + 3 ^ 40 * 878965 * 2
def baseEnd_878965 : Nat := 44575952936223089293355

theorem tailTrace_878965 : CollatzResearch.WordTrace tailWord_878965 prefixEnd_878965 44575952936223089293355 := by
  unfold tailWord_878965
  simp only [CollatzResearch.WordTrace]
  refine ⟨32058487260667395115822349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21372324840444930077214899 32058487260667395115822349)
  ·
    refine ⟨12021932722750273168433381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32058487260667395115822349 12021932722750273168433381)
    ·
      refine ⟨2254112385515676219081259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12021932722750273168433381 2254112385515676219081259)
      ·
        refine ⟨3381168578273514328621889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254112385515676219081259 3381168578273514328621889)
        ·
          refine ⟨2535876433705135746466417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3381168578273514328621889 2535876433705135746466417)
          ·
            refine ⟨1901907325278851809849813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2535876433705135746466417 1901907325278851809849813)
            ·
              refine ⟨44575952936223089293355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1901907325278851809849813 44575952936223089293355)
              ·
                rfl

theorem cell20_878965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 7].length) (baseStart_878965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878965 prefixEnd_878965 := by exact prefixLift 878965
  have htrace : WordTrace (prefixWord ++ tailWord_878965) baseStart_878965 baseEnd_878965 := by
    simpa [prefixWord, tailWord_878965, baseEnd_878965] using wordTrace_append hprefix tailTrace_878965
  have hstable : (prefixWord ++ tailWord_878965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878965).length < 2 ^ (prefixWord ++ tailWord_878965).sum := by decide
  have hdescent : baseEnd_878965 < baseStart_878965 := by decide
  rcases family_descends (prefixWord ++ tailWord_878965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878972 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 3]
def baseStart_878972 : Nat := 118140960795 + 878972 * 2 ^ 59
def prefixEnd_878972 : Nat := 4983230072969 + 3 ^ 40 * 878972 * 2
def baseEnd_878972 : Nat := 401186771416746890406833

theorem tailTrace_878972 : CollatzResearch.WordTrace tailWord_878972 prefixEnd_878972 401186771416746890406833 := by
  unfold tailWord_878972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16029371285821017655663585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21372495047761356874218113 16029371285821017655663585)
  ·
    refine ⟨12022028464365763241747689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16029371285821017655663585 12022028464365763241747689)
    ·
      refine ⟨9016521348274322431310767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12022028464365763241747689 9016521348274322431310767)
      ·
        refine ⟨13524782022411483646966151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9016521348274322431310767 13524782022411483646966151)
        ·
          refine ⟨20287173033617225470449227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13524782022411483646966151 20287173033617225470449227)
          ·
            refine ⟨30430759550425838205673841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20287173033617225470449227 30430759550425838205673841)
            ·
              refine ⟨22823069662819378654255381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30430759550425838205673841 22823069662819378654255381)
              ·
                refine ⟨1069831390444658374418221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22823069662819378654255381 1069831390444658374418221)
                ·
                  refine ⟨401186771416746890406833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069831390444658374418221 401186771416746890406833)
                  ·
                    rfl

theorem cell20_878972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_878972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878972 prefixEnd_878972 := by exact prefixLift 878972
  have htrace : WordTrace (prefixWord ++ tailWord_878972) baseStart_878972 baseEnd_878972 := by
    simpa [prefixWord, tailWord_878972, baseEnd_878972] using wordTrace_append hprefix tailTrace_878972
  have hstable : (prefixWord ++ tailWord_878972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878972).length < 2 ^ (prefixWord ++ tailWord_878972).sum := by decide
  have hdescent : baseEnd_878972 < baseStart_878972 := by decide
  rcases family_descends (prefixWord ++ tailWord_878972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_878993 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_878993 : Nat := 118140960795 + 878993 * 2 ^ 59
def prefixEnd_878993 : Nat := 4983230072969 + 3 ^ 40 * 878993 * 2
def baseEnd_878993 : Nat := 401196356388964150706747

theorem tailTrace_878993 : CollatzResearch.WordTrace tailWord_878993 prefixEnd_878993 401196356388964150706747 := by
  unfold tailWord_878993
  simp only [CollatzResearch.WordTrace]
  refine ⟨32059508504565955897841633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21373005669710637265227755 32059508504565955897841633)
  ·
    refine ⟨24044631378424466923381225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32059508504565955897841633 24044631378424466923381225)
    ·
      refine ⟨18033473533818350192535919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24044631378424466923381225 18033473533818350192535919)
      ·
        refine ⟨27050210300727525288803879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18033473533818350192535919 27050210300727525288803879)
        ·
          refine ⟨40575315451091287933205819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27050210300727525288803879 40575315451091287933205819)
          ·
            refine ⟨60862973176636931899808729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40575315451091287933205819 60862973176636931899808729)
            ·
              refine ⟨45647229882477698924856547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60862973176636931899808729 45647229882477698924856547)
              ·
                refine ⟨68470844823716548387284821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45647229882477698924856547 68470844823716548387284821)
                ·
                  refine ⟨401196356388964150706747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68470844823716548387284821 401196356388964150706747)
                  ·
                    rfl

theorem cell20_878993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_878993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_878993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_878993 prefixEnd_878993 := by exact prefixLift 878993
  have htrace : WordTrace (prefixWord ++ tailWord_878993) baseStart_878993 baseEnd_878993 := by
    simpa [prefixWord, tailWord_878993, baseEnd_878993] using wordTrace_append hprefix tailTrace_878993
  have hstable : (prefixWord ++ tailWord_878993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_878993).length < 2 ^ (prefixWord ++ tailWord_878993).sum := by decide
  have hdescent : baseEnd_878993 < baseStart_878993 := by decide
  rcases family_descends (prefixWord ++ tailWord_878993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879009 : List Nat := [1, 2, 3, 5, 1, 2, 1, 3, 2]
def baseStart_879009 : Nat := 118140960795 + 879009 * 2 ^ 59
def prefixEnd_879009 : Nat := 4983230072969 + 3 ^ 40 * 879009 * 2
def baseEnd_879009 : Nat := 401203659224939206173349

theorem tailTrace_879009 : CollatzResearch.WordTrace tailWord_879009 prefixEnd_879009 401203659224939206173349 := by
  unfold tailWord_879009
  simp only [CollatzResearch.WordTrace]
  refine ⟨32060092072507990630424081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21373394715005327086949387 32060092072507990630424081)
  ·
    refine ⟨24045069054380992972818061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32060092072507990630424081 24045069054380992972818061)
    ·
      refine ⟨9016900895392872364806773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24045069054380992972818061 9016900895392872364806773)
      ·
        refine ⟨845334458943081784200635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9016900895392872364806773 845334458943081784200635)
        ·
          refine ⟨1268001688414622676300953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845334458943081784200635 1268001688414622676300953)
          ·
            refine ⟨951001266310967007225715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268001688414622676300953 951001266310967007225715)
            ·
              refine ⟨1426501899466450510838573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951001266310967007225715 1426501899466450510838573)
              ·
                refine ⟨534938212299918941564465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1426501899466450510838573 534938212299918941564465)
                ·
                  refine ⟨401203659224939206173349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534938212299918941564465 401203659224939206173349)
                  ·
                    rfl

theorem cell20_879009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_879009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879009 prefixEnd_879009 := by exact prefixLift 879009
  have htrace : WordTrace (prefixWord ++ tailWord_879009) baseStart_879009 baseEnd_879009 := by
    simpa [prefixWord, tailWord_879009, baseEnd_879009] using wordTrace_append hprefix tailTrace_879009
  have hstable : (prefixWord ++ tailWord_879009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879009).length < 2 ^ (prefixWord ++ tailWord_879009).sum := by decide
  have hdescent : baseEnd_879009 < baseStart_879009 := by decide
  rcases family_descends (prefixWord ++ tailWord_879009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879010 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_879010 : Nat := 118140960795 + 879010 * 2 ^ 59
def prefixEnd_879010 : Nat := 4983230072969 + 3 ^ 40 * 879010 * 2
def baseEnd_879010 : Nat := 401204115652187647140011

theorem tailTrace_879010 : CollatzResearch.WordTrace tailWord_879010 prefixEnd_879010 401204115652187647140011 := by
  unfold tailWord_879010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015032136376091950302621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21373419030336245200806989 8015032136376091950302621)
  ·
    refine ⟨3005637051141034481363483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8015032136376091950302621 3005637051141034481363483)
    ·
      refine ⟨4508455576711551722045225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005637051141034481363483 4508455576711551722045225)
      ·
        refine ⟨3381341682533663791533919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4508455576711551722045225 3381341682533663791533919)
        ·
          refine ⟨5072012523800495687300879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3381341682533663791533919 5072012523800495687300879)
          ·
            refine ⟨7608018785700743530951319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5072012523800495687300879 7608018785700743530951319)
            ·
              refine ⟨11412028178551115296426979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7608018785700743530951319 11412028178551115296426979)
              ·
                refine ⟨17118042267826672944640469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11412028178551115296426979 17118042267826672944640469)
                ·
                  refine ⟨401204115652187647140011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17118042267826672944640469 401204115652187647140011)
                  ·
                    rfl

theorem cell20_879010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_879010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879010 prefixEnd_879010 := by exact prefixLift 879010
  have htrace : WordTrace (prefixWord ++ tailWord_879010) baseStart_879010 baseEnd_879010 := by
    simpa [prefixWord, tailWord_879010, baseEnd_879010] using wordTrace_append hprefix tailTrace_879010
  have hstable : (prefixWord ++ tailWord_879010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879010).length < 2 ^ (prefixWord ++ tailWord_879010).sum := by decide
  have hdescent : baseEnd_879010 < baseStart_879010 := by decide
  rcases family_descends (prefixWord ++ tailWord_879010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879034 : List Nat := [3, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_879034 : Nat := 118140960795 + 879034 * 2 ^ 59
def prefixEnd_879034 : Nat := 4983230072969 + 3 ^ 40 * 879034 * 2
def baseEnd_879034 : Nat := 401215069906150230339913

theorem tailTrace_879034 : CollatzResearch.WordTrace tailWord_879034 prefixEnd_879034 401215069906150230339913 := by
  unfold tailWord_879034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8015250974354354975021039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21374002598278279933389437 8015250974354354975021039)
  ·
    refine ⟨12022876461531532462531559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8015250974354354975021039 12022876461531532462531559)
    ·
      refine ⟨18034314692297298693797339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12022876461531532462531559 18034314692297298693797339)
      ·
        refine ⟨27051472038445948040696009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18034314692297298693797339 27051472038445948040696009)
        ·
          refine ⟨20288604028834461030522007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27051472038445948040696009 20288604028834461030522007)
          ·
            refine ⟨30432906043251691545783011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20288604028834461030522007 30432906043251691545783011)
            ·
              refine ⟨45649359064877537318674517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30432906043251691545783011 45649359064877537318674517)
              ·
                refine ⟨534953426541533640453217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 45649359064877537318674517 534953426541533640453217)
                ·
                  refine ⟨401215069906150230339913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534953426541533640453217 401215069906150230339913)
                  ·
                    rfl

theorem cell20_879034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_879034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879034 prefixEnd_879034 := by exact prefixLift 879034
  have htrace : WordTrace (prefixWord ++ tailWord_879034) baseStart_879034 baseEnd_879034 := by
    simpa [prefixWord, tailWord_879034, baseEnd_879034] using wordTrace_append hprefix tailTrace_879034
  have hstable : (prefixWord ++ tailWord_879034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879034).length < 2 ^ (prefixWord ++ tailWord_879034).sum := by decide
  have hdescent : baseEnd_879034 < baseStart_879034 := by decide
  rcases family_descends (prefixWord ++ tailWord_879034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879044 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 3]
def baseStart_879044 : Nat := 118140960795 + 879044 * 2 ^ 59
def prefixEnd_879044 : Nat := 4983230072969 + 3 ^ 40 * 879044 * 2
def baseEnd_879044 : Nat := 401219634178634640006539

theorem tailTrace_879044 : CollatzResearch.WordTrace tailWord_879044 prefixEnd_879044 401219634178634640006539 := by
  unfold tailWord_879044
  simp only [CollatzResearch.WordTrace]
  refine ⟨16030684313690595803974093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21374245751587461071965457 16030684313690595803974093)
  ·
    refine ⟨6011506617633973426490285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16030684313690595803974093 6011506617633973426490285)
    ·
      refine ⟨2254314981612740034933857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6011506617633973426490285 2254314981612740034933857)
      ·
        refine ⟨1690736236209555026200393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2254314981612740034933857 1690736236209555026200393)
        ·
          refine ⟨1268052177157166269650295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1690736236209555026200393 1268052177157166269650295)
          ·
            refine ⟨1902078265735749404475443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268052177157166269650295 1902078265735749404475443)
            ·
              refine ⟨2853117398603624106713165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902078265735749404475443 2853117398603624106713165)
              ·
                refine ⟨1069919024476359040017437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2853117398603624106713165 1069919024476359040017437)
                ·
                  refine ⟨401219634178634640006539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1069919024476359040017437 401219634178634640006539)
                  ·
                    rfl

theorem cell20_879044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_879044 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879044 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879044 prefixEnd_879044 := by exact prefixLift 879044
  have htrace : WordTrace (prefixWord ++ tailWord_879044) baseStart_879044 baseEnd_879044 := by
    simpa [prefixWord, tailWord_879044, baseEnd_879044] using wordTrace_append hprefix tailTrace_879044
  have hstable : (prefixWord ++ tailWord_879044).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879044).length < 2 ^ (prefixWord ++ tailWord_879044).sum := by decide
  have hdescent : baseEnd_879044 < baseStart_879044 := by decide
  rcases family_descends (prefixWord ++ tailWord_879044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879072 : List Nat := [2, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_879072 : Nat := 118140960795 + 879072 * 2 ^ 59
def prefixEnd_879072 : Nat := 4983230072969 + 3 ^ 40 * 879072 * 2
def baseEnd_879072 : Nat := 401232414141590987073091

theorem tailTrace_879072 : CollatzResearch.WordTrace tailWord_879072 prefixEnd_879072 401232414141590987073091 := by
  unfold tailWord_879072
  simp only [CollatzResearch.WordTrace]
  refine ⟨16031194935639876194983735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21374926580853168259978313 16031194935639876194983735)
  ·
    refine ⟨24046792403459814292475603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16031194935639876194983735 24046792403459814292475603)
    ·
      refine ⟨36070188605189721438713405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24046792403459814292475603 36070188605189721438713405)
      ·
        refine ⟨13526320726946145539517527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36070188605189721438713405 13526320726946145539517527)
        ·
          refine ⟨20289481090419218309276291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13526320726946145539517527 20289481090419218309276291)
          ·
            refine ⟨30434221635628827463914437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20289481090419218309276291 30434221635628827463914437)
            ·
              refine ⟨5706416556680405149483957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30434221635628827463914437 5706416556680405149483957)
              ·
                refine ⟨534976552188787982764121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5706416556680405149483957 534976552188787982764121)
                ·
                  refine ⟨401232414141590987073091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534976552188787982764121 401232414141590987073091)
                  ·
                    rfl

theorem cell20_879072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_879072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879072 prefixEnd_879072 := by exact prefixLift 879072
  have htrace : WordTrace (prefixWord ++ tailWord_879072) baseStart_879072 baseEnd_879072 := by
    simpa [prefixWord, tailWord_879072, baseEnd_879072] using wordTrace_append hprefix tailTrace_879072
  have hstable : (prefixWord ++ tailWord_879072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879072).length < 2 ^ (prefixWord ++ tailWord_879072).sum := by decide
  have hdescent : baseEnd_879072 < baseStart_879072 := by decide
  rcases family_descends (prefixWord ++ tailWord_879072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879085 : List Nat := [1, 5, 1, 3, 1, 3, 2, 2, 2]
def baseStart_879085 : Nat := 118140960795 + 879085 * 2 ^ 59
def prefixEnd_879085 : Nat := 4983230072969 + 3 ^ 40 * 879085 * 2
def baseEnd_879085 : Nat := 401238347695820719639705

theorem tailTrace_879085 : CollatzResearch.WordTrace tailWord_879085 prefixEnd_879085 401238347695820719639705 := by
  unfold tailWord_879085
  simp only [CollatzResearch.WordTrace]
  refine ⟨32062864020232655610190709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21375242680155103740127139 32062864020232655610190709)
  ·
    refine ⟨3005893501896811463455379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32062864020232655610190709 3005893501896811463455379)
    ·
      refine ⟨4508840252845217195183069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3005893501896811463455379 4508840252845217195183069)
      ·
        refine ⟨1690815094816956448193651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4508840252845217195183069 1690815094816956448193651)
        ·
          refine ⟨2536222642225434672290477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1690815094816956448193651 2536222642225434672290477)
          ·
            refine ⟨951083490834538002108929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2536222642225434672290477 951083490834538002108929)
            ·
              refine ⟨713312618125903501581697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951083490834538002108929 713312618125903501581697)
              ·
                refine ⟨534984463594427626186273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713312618125903501581697 534984463594427626186273)
                ·
                  refine ⟨401238347695820719639705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 534984463594427626186273 401238347695820719639705)
                  ·
                    rfl

theorem cell20_879085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_879085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879085 prefixEnd_879085 := by exact prefixLift 879085
  have htrace : WordTrace (prefixWord ++ tailWord_879085) baseStart_879085 baseEnd_879085 := by
    simpa [prefixWord, tailWord_879085, baseEnd_879085] using wordTrace_append hprefix tailTrace_879085
  have hstable : (prefixWord ++ tailWord_879085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879085).length < 2 ^ (prefixWord ++ tailWord_879085).sum := by decide
  have hdescent : baseEnd_879085 < baseStart_879085 := by decide
  rcases family_descends (prefixWord ++ tailWord_879085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879183 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_879183 : Nat := 118140960795 + 879183 * 2 ^ 59
def prefixEnd_879183 : Nat := 4983230072969 + 3 ^ 40 * 879183 * 2
def baseEnd_879183 : Nat := 401283077566167934372637

theorem tailTrace_879183 : CollatzResearch.WordTrace tailWord_879183 prefixEnd_879183 401283077566167934372637 := by
  unfold tailWord_879183
  simp only [CollatzResearch.WordTrace]
  refine ⟨32066438373877618347258203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21377625582585078898172135 32066438373877618347258203)
  ·
    refine ⟨48099657560816427520887305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32066438373877618347258203 48099657560816427520887305)
    ·
      refine ⟨36074743170612320640665479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48099657560816427520887305 36074743170612320640665479)
      ·
        refine ⟨54112114755918480960998219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36074743170612320640665479 54112114755918480960998219)
        ·
          refine ⟨81168172133877721441497329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54112114755918480960998219 81168172133877721441497329)
          ·
            refine ⟨60876129100408291081122997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 81168172133877721441497329 60876129100408291081122997)
            ·
              refine ⟨5707137103163277288855281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60876129100408291081122997 5707137103163277288855281)
              ·
                refine ⟨4280352827372457966641461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5707137103163277288855281 4280352827372457966641461)
                ·
                  refine ⟨401283077566167934372637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4280352827372457966641461 401283077566167934372637)
                  ·
                    rfl

theorem cell20_879183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_879183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879183 prefixEnd_879183 := by exact prefixLift 879183
  have htrace : WordTrace (prefixWord ++ tailWord_879183) baseStart_879183 baseEnd_879183 := by
    simpa [prefixWord, tailWord_879183, baseEnd_879183] using wordTrace_append hprefix tailTrace_879183
  have hstable : (prefixWord ++ tailWord_879183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879183).length < 2 ^ (prefixWord ++ tailWord_879183).sum := by decide
  have hdescent : baseEnd_879183 < baseStart_879183 := by decide
  rcases family_descends (prefixWord ++ tailWord_879183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879203 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 2]
def baseStart_879203 : Nat := 118140960795 + 879203 * 2 ^ 59
def prefixEnd_879203 : Nat := 4983230072969 + 3 ^ 40 * 879203 * 2
def baseEnd_879203 : Nat := 401292206111136753705889

theorem tailTrace_879203 : CollatzResearch.WordTrace tailWord_879203 prefixEnd_879203 401292206111136753705889 := by
  unfold tailWord_879203
  simp only [CollatzResearch.WordTrace]
  refine ⟨32067167833805161762986263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21378111889203441175324175 32067167833805161762986263)
  ·
    refine ⟨48100751750707742644479395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32067167833805161762986263 48100751750707742644479395)
    ·
      refine ⟨72151127626061613966719093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48100751750707742644479395 72151127626061613966719093)
      ·
        refine ⟨6764168214943276309379915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72151127626061613966719093 6764168214943276309379915)
        ·
          refine ⟨10146252322414914464069873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6764168214943276309379915 10146252322414914464069873)
          ·
            refine ⟨7609689241811185848052405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10146252322414914464069873 7609689241811185848052405)
            ·
              refine ⟨713408366419798673254913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7609689241811185848052405 713408366419798673254913)
              ·
                refine ⟨535056274814849004941185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713408366419798673254913 535056274814849004941185)
                ·
                  refine ⟨401292206111136753705889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535056274814849004941185 401292206111136753705889)
                  ·
                    rfl

theorem cell20_879203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2].length) (baseStart_879203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879203 prefixEnd_879203 := by exact prefixLift 879203
  have htrace : WordTrace (prefixWord ++ tailWord_879203) baseStart_879203 baseEnd_879203 := by
    simpa [prefixWord, tailWord_879203, baseEnd_879203] using wordTrace_append hprefix tailTrace_879203
  have hstable : (prefixWord ++ tailWord_879203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879203).length < 2 ^ (prefixWord ++ tailWord_879203).sum := by decide
  have hdescent : baseEnd_879203 < baseStart_879203 := by decide
  rcases family_descends (prefixWord ++ tailWord_879203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879258 : List Nat := [3, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_879258 : Nat := 118140960795 + 879258 * 2 ^ 59
def prefixEnd_879258 : Nat := 4983230072969 + 3 ^ 40 * 879258 * 2
def baseEnd_879258 : Nat := 401317309609801006872331

theorem tailTrace_879258 : CollatzResearch.WordTrace tailWord_879258 prefixEnd_879258 401317309609801006872331 := by
  unfold tailWord_879258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8017293462151476539059607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21379449232403937437492285 8017293462151476539059607)
  ·
    refine ⟨12025940193227214808589411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8017293462151476539059607 12025940193227214808589411)
    ·
      refine ⟨18038910289840822212884117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12025940193227214808589411 18038910289840822212884117)
      ·
        refine ⟨845573919836288541228943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18038910289840822212884117 845573919836288541228943)
        ·
          refine ⟨1268360879754432811843415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845573919836288541228943 1268360879754432811843415)
          ·
            refine ⟨1902541319631649217765123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268360879754432811843415 1902541319631649217765123)
            ·
              refine ⟨2853811979447473826647685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902541319631649217765123 2853811979447473826647685)
              ·
                refine ⟨535089746146401342496441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2853811979447473826647685 535089746146401342496441)
                ·
                  refine ⟨401317309609801006872331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535089746146401342496441 401317309609801006872331)
                  ·
                    rfl

theorem cell20_879258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_879258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879258 prefixEnd_879258 := by exact prefixLift 879258
  have htrace : WordTrace (prefixWord ++ tailWord_879258) baseStart_879258 baseEnd_879258 := by
    simpa [prefixWord, tailWord_879258, baseEnd_879258] using wordTrace_append hprefix tailTrace_879258
  have hstable : (prefixWord ++ tailWord_879258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879258).length < 2 ^ (prefixWord ++ tailWord_879258).sum := by decide
  have hdescent : baseEnd_879258 < baseStart_879258 := by decide
  rcases family_descends (prefixWord ++ tailWord_879258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879262 : List Nat := [4, 3, 1, 1, 1, 1, 2, 3, 4]
def baseStart_879262 : Nat := 118140960795 + 879262 * 2 ^ 59
def prefixEnd_879262 : Nat := 4983230072969 + 3 ^ 40 * 879262 * 2
def baseEnd_879262 : Nat := 401319135318794770738981

theorem tailTrace_879262 : CollatzResearch.WordTrace tailWord_879262 prefixEnd_879262 401319135318794770738981 := by
  unfold tailWord_879262
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008664967573926854923005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21379546493727609892922693 4008664967573926854923005)
  ·
    refine ⟨1503249362840222570596127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4008664967573926854923005 1503249362840222570596127)
    ·
      refine ⟨2254874044260333855894191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1503249362840222570596127 2254874044260333855894191)
      ·
        refine ⟨3382311066390500783841287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2254874044260333855894191 3382311066390500783841287)
        ·
          refine ⟨5073466599585751175761931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3382311066390500783841287 5073466599585751175761931)
          ·
            refine ⟨7610199899378626763642897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5073466599585751175761931 7610199899378626763642897)
            ·
              refine ⟨5707649924533970072732173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7610199899378626763642897 5707649924533970072732173)
              ·
                refine ⟨2140368721700238777274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5707649924533970072732173 2140368721700238777274565)
                ·
                  refine ⟨401319135318794770738981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140368721700238777274565 401319135318794770738981)
                  ·
                    rfl

theorem cell20_879262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_879262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879262 prefixEnd_879262 := by exact prefixLift 879262
  have htrace : WordTrace (prefixWord ++ tailWord_879262) baseStart_879262 baseEnd_879262 := by
    simpa [prefixWord, tailWord_879262, baseEnd_879262] using wordTrace_append hprefix tailTrace_879262
  have hstable : (prefixWord ++ tailWord_879262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879262).length < 2 ^ (prefixWord ++ tailWord_879262).sum := by decide
  have hdescent : baseEnd_879262 < baseStart_879262 := by decide
  rcases family_descends (prefixWord ++ tailWord_879262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879283 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 4]
def baseStart_879283 : Nat := 118140960795 + 879283 * 2 ^ 59
def prefixEnd_879283 : Nat := 4983230072969 + 3 ^ 40 * 879283 * 2
def baseEnd_879283 : Nat := 401328720291012031038895

theorem tailTrace_879283 : CollatzResearch.WordTrace tailWord_879283 prefixEnd_879283 401328720291012031038895 := by
  unfold tailWord_879283
  simp only [CollatzResearch.WordTrace]
  refine ⟨32070085673515335425898503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380057115676890283932335 32070085673515335425898503)
  ·
    refine ⟨48105128510273003138847755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32070085673515335425898503 48105128510273003138847755)
    ·
      refine ⟨72157692765409504708271633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48105128510273003138847755 72157692765409504708271633)
      ·
        refine ⟨54118269574057128531203725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72157692765409504708271633 54118269574057128531203725)
        ·
          refine ⟨20294351090271423199201397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54118269574057128531203725 20294351090271423199201397)
          ·
            refine ⟨1902595414712945924925131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20294351090271423199201397 1902595414712945924925131)
            ·
              refine ⟨2853893122069418887387697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902595414712945924925131 2853893122069418887387697)
              ·
                refine ⟨2140419841552064165540773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2853893122069418887387697 2140419841552064165540773)
                ·
                  refine ⟨401328720291012031038895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140419841552064165540773 401328720291012031038895)
                  ·
                    rfl

theorem cell20_879283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 4].length) (baseStart_879283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879283 prefixEnd_879283 := by exact prefixLift 879283
  have htrace : WordTrace (prefixWord ++ tailWord_879283) baseStart_879283 baseEnd_879283 := by
    simpa [prefixWord, tailWord_879283, baseEnd_879283] using wordTrace_append hprefix tailTrace_879283
  have hstable : (prefixWord ++ tailWord_879283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879283).length < 2 ^ (prefixWord ++ tailWord_879283).sum := by decide
  have hdescent : baseEnd_879283 < baseStart_879283 := by decide
  rcases family_descends (prefixWord ++ tailWord_879283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879317 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 4]
def baseStart_879317 : Nat := 118140960795 + 879317 * 2 ^ 59
def prefixEnd_879317 : Nat := 4983230072969 + 3 ^ 40 * 879317 * 2
def baseEnd_879317 : Nat := 401344238817459023905423

theorem tailTrace_879317 : CollatzResearch.WordTrace tailWord_879317 prefixEnd_879317 401344238817459023905423 := by
  unfold tailWord_879317
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071325755392159232636205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380883836928106155090803 32071325755392159232636205)
  ·
    refine ⟨12026747158272059712238577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32071325755392159232636205 12026747158272059712238577)
    ·
      refine ⟨9020060368704044784178933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12026747158272059712238577 9020060368704044784178933)
      ·
        refine ⟨845630659566004198516775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9020060368704044784178933 845630659566004198516775)
        ·
          refine ⟨1268445989349006297775163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 845630659566004198516775 1268445989349006297775163)
          ·
            refine ⟨1902668984023509446662745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268445989349006297775163 1902668984023509446662745)
            ·
              refine ⟨1427001738017632084997059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902668984023509446662745 1427001738017632084997059)
              ·
                refine ⟨2140502607026448127495589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427001738017632084997059 2140502607026448127495589)
                ·
                  refine ⟨401344238817459023905423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140502607026448127495589 401344238817459023905423)
                  ·
                    rfl

theorem cell20_879317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_879317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879317 prefixEnd_879317 := by exact prefixLift 879317
  have htrace : WordTrace (prefixWord ++ tailWord_879317) baseStart_879317 baseEnd_879317 := by
    simpa [prefixWord, tailWord_879317, baseEnd_879317] using wordTrace_append hprefix tailTrace_879317
  have hstable : (prefixWord ++ tailWord_879317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879317).length < 2 ^ (prefixWord ++ tailWord_879317).sum := by decide
  have hdescent : baseEnd_879317 < baseStart_879317 := by decide
  rcases family_descends (prefixWord ++ tailWord_879317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879321 : List Nat := [1, 2, 1, 2, 3, 2, 4, 1, 4]
def baseStart_879321 : Nat := 118140960795 + 879321 * 2 ^ 59
def prefixEnd_879321 : Nat := 4983230072969 + 3 ^ 40 * 879321 * 2
def baseEnd_879321 : Nat := 401346064526452787772073

theorem tailTrace_879321 : CollatzResearch.WordTrace tailWord_879321 prefixEnd_879321 401346064526452787772073 := by
  unfold tailWord_879321
  simp only [CollatzResearch.WordTrace]
  refine ⟨32071471647377667915781817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21380981098251778610521211 32071471647377667915781817)
  ·
    refine ⟨24053603735533250936836363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32071471647377667915781817 24053603735533250936836363)
    ·
      refine ⟨36080405603299876405254545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24053603735533250936836363 36080405603299876405254545)
      ·
        refine ⟨27060304202474907303940909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36080405603299876405254545 27060304202474907303940909)
        ·
          refine ⟨10147614075928090238977841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27060304202474907303940909 10147614075928090238977841)
          ·
            refine ⟨7610710556946067679233381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10147614075928090238977841 7610710556946067679233381)
            ·
              refine ⟨1427008229427387689856259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7610710556946067679233381 1427008229427387689856259)
              ·
                refine ⟨2140512344141081534784389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1427008229427387689856259 2140512344141081534784389)
                ·
                  refine ⟨401346064526452787772073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140512344141081534784389 401346064526452787772073)
                  ·
                    rfl

theorem cell20_879321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 4].length) (baseStart_879321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879321 prefixEnd_879321 := by exact prefixLift 879321
  have htrace : WordTrace (prefixWord ++ tailWord_879321) baseStart_879321 baseEnd_879321 := by
    simpa [prefixWord, tailWord_879321, baseEnd_879321] using wordTrace_append hprefix tailTrace_879321
  have hstable : (prefixWord ++ tailWord_879321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879321).length < 2 ^ (prefixWord ++ tailWord_879321).sum := by decide
  have hdescent : baseEnd_879321 < baseStart_879321 := by decide
  rcases family_descends (prefixWord ++ tailWord_879321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879383 : List Nat := [1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_879383 : Nat := 118140960795 + 879383 * 2 ^ 59
def prefixEnd_879383 : Nat := 4983230072969 + 3 ^ 40 * 879383 * 2
def baseEnd_879383 : Nat := 133791454338618709235051

theorem tailTrace_879383 : CollatzResearch.WordTrace tailWord_879383 prefixEnd_879383 133791454338618709235051 := by
  unfold tailWord_879383
  simp only [CollatzResearch.WordTrace]
  refine ⟨32073732973153052504538803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21382488648768701669692535 32073732973153052504538803)
  ·
    refine ⟨48110599459729578756808205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32073732973153052504538803 48110599459729578756808205)
    ·
      refine ⟨18041474797398592033803077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48110599459729578756808205 18041474797398592033803077)
      ·
        refine ⟨3382776524512236006338077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18041474797398592033803077 3382776524512236006338077)
        ·
          refine ⟨1268541196692088502376779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3382776524512236006338077 1268541196692088502376779)
          ·
            refine ⟨1902811795038132753565169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1268541196692088502376779 1902811795038132753565169)
            ·
              refine ⟨1427108846278599565173877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1902811795038132753565169 1427108846278599565173877)
              ·
                refine ⟨133791454338618709235051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427108846278599565173877 133791454338618709235051)
                ·
                  rfl

theorem cell20_879383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_879383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879383 prefixEnd_879383 := by exact prefixLift 879383
  have htrace : WordTrace (prefixWord ++ tailWord_879383) baseStart_879383 baseEnd_879383 := by
    simpa [prefixWord, tailWord_879383, baseEnd_879383] using wordTrace_append hprefix tailTrace_879383
  have hstable : (prefixWord ++ tailWord_879383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879383).length < 2 ^ (prefixWord ++ tailWord_879383).sum := by decide
  have hdescent : baseEnd_879383 < baseStart_879383 := by decide
  rcases family_descends (prefixWord ++ tailWord_879383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879421 : List Nat := [1, 4, 1, 4, 3, 7]
def baseStart_879421 : Nat := 118140960795 + 879421 * 2 ^ 59
def prefixEnd_879421 : Nat := 4983230072969 + 3 ^ 40 * 879421 * 2
def baseEnd_879421 : Nat := 14866359527825810534753

theorem tailTrace_879421 : CollatzResearch.WordTrace tailWord_879421 prefixEnd_879421 14866359527825810534753 := by
  unfold tailWord_879421
  simp only [CollatzResearch.WordTrace]
  refine ⟨32075118947015384994422117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21383412631343589996281411 32075118947015384994422117)
  ·
    refine ⟨6014084802565384686454147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32075118947015384994422117 6014084802565384686454147)
    ·
      refine ⟨9021127203848077029681221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6014084802565384686454147 9021127203848077029681221)
      ·
        refine ⟨1691461350721514443065229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9021127203848077029681221 1691461350721514443065229)
        ·
          refine ⟨634298006520567916149461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1691461350721514443065229 634298006520567916149461)
          ·
            refine ⟨14866359527825810534753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 634298006520567916149461 14866359527825810534753)
            ·
              rfl

theorem cell20_879421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 7].length) (baseStart_879421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879421 prefixEnd_879421 := by exact prefixLift 879421
  have htrace : WordTrace (prefixWord ++ tailWord_879421) baseStart_879421 baseEnd_879421 := by
    simpa [prefixWord, tailWord_879421, baseEnd_879421] using wordTrace_append hprefix tailTrace_879421
  have hstable : (prefixWord ++ tailWord_879421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879421).length < 2 ^ (prefixWord ++ tailWord_879421).sum := by decide
  have hdescent : baseEnd_879421 < baseStart_879421 := by decide
  rcases family_descends (prefixWord ++ tailWord_879421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879452 : List Nat := [2, 2, 4, 2, 1, 2, 1, 2, 4]
def baseStart_879452 : Nat := 118140960795 + 879452 * 2 ^ 59
def prefixEnd_879452 : Nat := 4983230072969 + 3 ^ 40 * 879452 * 2
def baseEnd_879452 : Nat := 401405856495998554404871

theorem tailTrace_879452 : CollatzResearch.WordTrace tailWord_879452 prefixEnd_879452 401405856495998554404871 := by
  unfold tailWord_879452
  simp only [CollatzResearch.WordTrace]
  refine ⟨16038124804951538644400305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21384166406602051525867073 16038124804951538644400305)
  ·
    refine ⟨12028593603713653983300229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16038124804951538644400305 12028593603713653983300229)
    ·
      refine ⟨2255361300696310121868793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12028593603713653983300229 2255361300696310121868793)
      ·
        refine ⟨1691520975522232591401595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2255361300696310121868793 1691520975522232591401595)
        ·
          refine ⟨2537281463283348887102393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691520975522232591401595 2537281463283348887102393)
          ·
            refine ⟨1902961097462511665326795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537281463283348887102393 1902961097462511665326795)
            ·
              refine ⟨2854441646193767497990193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1902961097462511665326795 2854441646193767497990193)
              ·
                refine ⟨2140831234645325623492645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2854441646193767497990193 2140831234645325623492645)
                ·
                  refine ⟨401405856495998554404871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2140831234645325623492645 401405856495998554404871)
                  ·
                    rfl

theorem cell20_879452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 2, 4].length) (baseStart_879452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879452 prefixEnd_879452 := by exact prefixLift 879452
  have htrace : WordTrace (prefixWord ++ tailWord_879452) baseStart_879452 baseEnd_879452 := by
    simpa [prefixWord, tailWord_879452, baseEnd_879452] using wordTrace_append hprefix tailTrace_879452
  have hstable : (prefixWord ++ tailWord_879452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879452).length < 2 ^ (prefixWord ++ tailWord_879452).sum := by decide
  have hdescent : baseEnd_879452 < baseStart_879452 := by decide
  rcases family_descends (prefixWord ++ tailWord_879452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879459 : List Nat := [1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_879459 : Nat := 118140960795 + 879459 * 2 ^ 59
def prefixEnd_879459 : Nat := 4983230072969 + 3 ^ 40 * 879459 * 2
def baseEnd_879459 : Nat := 133803017162245880390503

theorem tailTrace_879459 : CollatzResearch.WordTrace tailWord_879459 prefixEnd_879459 133803017162245880390503 := by
  unfold tailWord_879459
  simp only [CollatzResearch.WordTrace]
  refine ⟨32076504920877717484305431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21384336613918478322870287 32076504920877717484305431)
  ·
    refine ⟨48114757381316576226458147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32076504920877717484305431 48114757381316576226458147)
    ·
      refine ⟨72172136071974864339687221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48114757381316576226458147 72172136071974864339687221)
      ·
        refine ⟨6766137756747643531845677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72172136071974864339687221 6766137756747643531845677)
        ·
          refine ⟨2537301658780366324442129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6766137756747643531845677 2537301658780366324442129)
          ·
            refine ⟨1902976244085274743331597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537301658780366324442129 1902976244085274743331597)
            ·
              refine ⟨713616091531978028749349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1902976244085274743331597 713616091531978028749349)
              ·
                refine ⟨133803017162245880390503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713616091531978028749349 133803017162245880390503)
                ·
                  rfl

theorem cell20_879459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_879459 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879459 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879459 prefixEnd_879459 := by exact prefixLift 879459
  have htrace : WordTrace (prefixWord ++ tailWord_879459) baseStart_879459 baseEnd_879459 := by
    simpa [prefixWord, tailWord_879459, baseEnd_879459] using wordTrace_append hprefix tailTrace_879459
  have hstable : (prefixWord ++ tailWord_879459).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879459).length < 2 ^ (prefixWord ++ tailWord_879459).sum := by decide
  have hdescent : baseEnd_879459 < baseStart_879459 := by decide
  rcases family_descends (prefixWord ++ tailWord_879459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879510 : List Nat := [5, 3, 1, 1, 1, 3, 2, 4]
def baseStart_879510 : Nat := 118140960795 + 879510 * 2 ^ 59
def prefixEnd_879510 : Nat := 4983230072969 + 3 ^ 40 * 879510 * 2
def baseEnd_879510 : Nat := 133810776425469376823767

theorem tailTrace_879510 : CollatzResearch.WordTrace tailWord_879510 prefixEnd_879510 133810776425469376823767 := by
  unfold tailWord_879510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004897815230809574650749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21385576695795302129607989 2004897815230809574650749)
  ·
    refine ⟨751836680711553590494031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2004897815230809574650749 751836680711553590494031)
    ·
      refine ⟨1127755021067330385741047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 751836680711553590494031 1127755021067330385741047)
      ·
        refine ⟨1691632531600995578611571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1127755021067330385741047 1691632531600995578611571)
        ·
          refine ⟨2537448797401493367917357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1691632531600995578611571 2537448797401493367917357)
          ·
            refine ⟨951543299025560012969009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2537448797401493367917357 951543299025560012969009)
            ·
              refine ⟨713657474269170009726757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951543299025560012969009 713657474269170009726757)
              ·
                refine ⟨133810776425469376823767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713657474269170009726757 133810776425469376823767)
                ·
                  rfl

theorem cell20_879510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_879510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879510 prefixEnd_879510 := by exact prefixLift 879510
  have htrace : WordTrace (prefixWord ++ tailWord_879510) baseStart_879510 baseEnd_879510 := by
    simpa [prefixWord, tailWord_879510, baseEnd_879510] using wordTrace_append hprefix tailTrace_879510
  have hstable : (prefixWord ++ tailWord_879510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879510).length < 2 ^ (prefixWord ++ tailWord_879510).sum := by decide
  have hdescent : baseEnd_879510 < baseStart_879510 := by decide
  rcases family_descends (prefixWord ++ tailWord_879510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879514 : List Nat := [3, 1, 1, 4, 3, 2, 2, 4]
def baseStart_879514 : Nat := 118140960795 + 879514 * 2 ^ 59
def prefixEnd_879514 : Nat := 4983230072969 + 3 ^ 40 * 879514 * 2
def baseEnd_879514 : Nat := 133811384995133964779317

theorem tailTrace_879514 : CollatzResearch.WordTrace tailWord_879514 prefixEnd_879514 133811384995133964779317 := by
  unfold tailWord_879514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8019627733919615469389399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21385673957118974585038397 8019627733919615469389399)
  ·
    refine ⟨12029441600879423204084099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8019627733919615469389399 12029441600879423204084099)
    ·
      refine ⟨18044162401319134806126149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12029441600879423204084099 18044162401319134806126149)
      ·
        refine ⟨3383280450247337776148653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18044162401319134806126149 3383280450247337776148653)
        ·
          refine ⟨1268730168842751666055745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3383280450247337776148653 1268730168842751666055745)
          ·
            refine ⟨951547626632063749541809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1268730168842751666055745 951547626632063749541809)
            ·
              refine ⟨713660719974047812156357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951547626632063749541809 713660719974047812156357)
              ·
                refine ⟨133811384995133964779317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713660719974047812156357 133811384995133964779317)
                ·
                  rfl

theorem cell20_879514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_879514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879514 prefixEnd_879514 := by exact prefixLift 879514
  have htrace : WordTrace (prefixWord ++ tailWord_879514) baseStart_879514 baseEnd_879514 := by
    simpa [prefixWord, tailWord_879514, baseEnd_879514] using wordTrace_append hprefix tailTrace_879514
  have hstable : (prefixWord ++ tailWord_879514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879514).length < 2 ^ (prefixWord ++ tailWord_879514).sum := by decide
  have hdescent : baseEnd_879514 < baseStart_879514 := by decide
  rcases family_descends (prefixWord ++ tailWord_879514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879545 : List Nat := [1, 2, 1, 4, 2, 3, 3, 2, 2]
def baseStart_879545 : Nat := 118140960795 + 879545 * 2 ^ 59
def prefixEnd_879545 : Nat := 4983230072969 + 3 ^ 40 * 879545 * 2
def baseEnd_879545 : Nat := 401448304230103564304491

theorem tailTrace_879545 : CollatzResearch.WordTrace tailWord_879545 prefixEnd_879545 401448304230103564304491 := by
  unfold tailWord_879545
  simp only [CollatzResearch.WordTrace]
  refine ⟨32079641598566154171936089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21386427732377436114624059 32079641598566154171936089)
  ·
    refine ⟨24059731198924615628952067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32079641598566154171936089 24059731198924615628952067)
    ·
      refine ⟨36089596798386923443428101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24059731198924615628952067 36089596798386923443428101)
      ·
        refine ⟨6766799399697548145642769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36089596798386923443428101 6766799399697548145642769)
        ·
          refine ⟨5075099549773161109232077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6766799399697548145642769 5075099549773161109232077)
          ·
            refine ⟨1903162331164935415962029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5075099549773161109232077 1903162331164935415962029)
            ·
              refine ⟨713685874186850780985761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903162331164935415962029 713685874186850780985761)
              ·
                refine ⟨535264405640138085739321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713685874186850780985761 535264405640138085739321)
                ·
                  refine ⟨401448304230103564304491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535264405640138085739321 401448304230103564304491)
                  ·
                    rfl

theorem cell20_879545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_879545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879545 prefixEnd_879545 := by exact prefixLift 879545
  have htrace : WordTrace (prefixWord ++ tailWord_879545) baseStart_879545 baseEnd_879545 := by
    simpa [prefixWord, tailWord_879545, baseEnd_879545] using wordTrace_append hprefix tailTrace_879545
  have hstable : (prefixWord ++ tailWord_879545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879545).length < 2 ^ (prefixWord ++ tailWord_879545).sum := by decide
  have hdescent : baseEnd_879545 < baseStart_879545 := by decide
  rcases family_descends (prefixWord ++ tailWord_879545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879608 : List Nat := [2, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_879608 : Nat := 118140960795 + 879608 * 2 ^ 59
def prefixEnd_879608 : Nat := 4983230072969 + 3 ^ 40 * 879608 * 2
def baseEnd_879608 : Nat := 401477059146755345204233

theorem tailTrace_879608 : CollatzResearch.WordTrace tailWord_879608 prefixEnd_879608 401477059146755345204233 := by
  unfold tailWord_879608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16040969698668957965739739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21387959598225277287652985 16040969698668957965739739)
  ·
    refine ⟨24061454548003436948609609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16040969698668957965739739 24061454548003436948609609)
    ·
      refine ⟨18046090911002577711457207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24061454548003436948609609 18046090911002577711457207)
      ·
        refine ⟨27069136366503866567185811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18046090911002577711457207 27069136366503866567185811)
        ·
          refine ⟨40603704549755799850778717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27069136366503866567185811 40603704549755799850778717)
          ·
            refine ⟨15226389206158424944042019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40603704549755799850778717 15226389206158424944042019)
            ·
              refine ⟨22839583809237637416063029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15226389206158424944042019 22839583809237637416063029)
              ·
                refine ⟨2141210982116028507755909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22839583809237637416063029 2141210982116028507755909)
                ·
                  refine ⟨401477059146755345204233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141210982116028507755909 401477059146755345204233)
                  ·
                    rfl

theorem cell20_879608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_879608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879608 prefixEnd_879608 := by exact prefixLift 879608
  have htrace : WordTrace (prefixWord ++ tailWord_879608) baseStart_879608 baseEnd_879608 := by
    simpa [prefixWord, tailWord_879608, baseEnd_879608] using wordTrace_append hprefix tailTrace_879608
  have hstable : (prefixWord ++ tailWord_879608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879608).length < 2 ^ (prefixWord ++ tailWord_879608).sum := by decide
  have hdescent : baseEnd_879608 < baseStart_879608 := by decide
  rcases family_descends (prefixWord ++ tailWord_879608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879642 : List Nat := [3, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_879642 : Nat := 118140960795 + 879642 * 2 ^ 59
def prefixEnd_879642 : Nat := 4983230072969 + 3 ^ 40 * 879642 * 2
def baseEnd_879642 : Nat := 401492577673202338070761

theorem tailTrace_879642 : CollatzResearch.WordTrace tailWord_879642 prefixEnd_879642 401492577673202338070761 := by
  unfold tailWord_879642
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020794869803684934554295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21388786319476493158811453 8020794869803684934554295)
  ·
    refine ⟨12031192304705527401831443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8020794869803684934554295 12031192304705527401831443)
    ·
      refine ⟨18046788457058291102747165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031192304705527401831443 18046788457058291102747165)
      ·
        refine ⟨6767545671396859163530187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18046788457058291102747165 6767545671396859163530187)
        ·
          refine ⟨10151318507095288745295281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6767545671396859163530187 10151318507095288745295281)
          ·
            refine ⟨7613488880321466558971461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10151318507095288745295281 7613488880321466558971461)
            ·
              refine ⟨1427529165060274979807149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7613488880321466558971461 1427529165060274979807149)
              ·
                refine ⟨535323436897603117427681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1427529165060274979807149 535323436897603117427681)
                ·
                  refine ⟨401492577673202338070761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535323436897603117427681 401492577673202338070761)
                  ·
                    rfl

theorem cell20_879642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_879642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879642 prefixEnd_879642 := by exact prefixLift 879642
  have htrace : WordTrace (prefixWord ++ tailWord_879642) baseStart_879642 baseEnd_879642 := by
    simpa [prefixWord, tailWord_879642, baseEnd_879642] using wordTrace_append hprefix tailTrace_879642
  have hstable : (prefixWord ++ tailWord_879642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879642).length < 2 ^ (prefixWord ++ tailWord_879642).sum := by decide
  have hdescent : baseEnd_879642 < baseStart_879642 := by decide
  rcases family_descends (prefixWord ++ tailWord_879642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879653 : List Nat := [1, 3, 1, 2, 2, 2, 9]
def baseStart_879653 : Nat := 118140960795 + 879653 * 2 ^ 59
def prefixEnd_879653 : Nat := 4983230072969 + 3 ^ 40 * 879653 * 2
def baseEnd_879653 : Nat := 44610844263659465411561

theorem tailTrace_879653 : CollatzResearch.WordTrace tailWord_879653 prefixEnd_879653 44610844263659465411561 := by
  unfold tailWord_879653
  simp only [CollatzResearch.WordTrace]
  refine ⟨32083580682174888616867613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21389053788116592411245075 32083580682174888616867613)
  ·
    refine ⟨12031342755815583231325355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32083580682174888616867613 12031342755815583231325355)
    ·
      refine ⟨18047014133723374846988033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12031342755815583231325355 18047014133723374846988033)
      ·
        refine ⟨13535260600292531135241025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18047014133723374846988033 13535260600292531135241025)
        ·
          refine ⟨10151445450219398351430769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13535260600292531135241025 10151445450219398351430769)
          ·
            refine ⟨7613584087664548763573077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10151445450219398351430769 7613584087664548763573077)
            ·
              refine ⟨44610844263659465411561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7613584087664548763573077 44610844263659465411561)
              ·
                rfl

theorem cell20_879653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_879653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879653 prefixEnd_879653 := by exact prefixLift 879653
  have htrace : WordTrace (prefixWord ++ tailWord_879653) baseStart_879653 baseEnd_879653 := by
    simpa [prefixWord, tailWord_879653, baseEnd_879653] using wordTrace_append hprefix tailTrace_879653
  have hstable : (prefixWord ++ tailWord_879653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879653).length < 2 ^ (prefixWord ++ tailWord_879653).sum := by decide
  have hdescent : baseEnd_879653 < baseStart_879653 := by decide
  rcases family_descends (prefixWord ++ tailWord_879653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879673 : List Nat := [1, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_879673 : Nat := 118140960795 + 879673 * 2 ^ 59
def prefixEnd_879673 : Nat := 4983230072969 + 3 ^ 40 * 879673 * 2
def baseEnd_879673 : Nat := 401506726917904008037301

theorem tailTrace_879673 : CollatzResearch.WordTrace tailWord_879673 prefixEnd_879673 401506726917904008037301 := by
  unfold tailWord_879673
  simp only [CollatzResearch.WordTrace]
  refine ⟨32084310142102432032595673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21389540094734954688397115 32084310142102432032595673)
  ·
    refine ⟨24063232606576824024446755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32084310142102432032595673 24063232606576824024446755)
    ·
      refine ⟨36094848909865236036670133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24063232606576824024446755 36094848909865236036670133)
      ·
        refine ⟨3383892085299865878437825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36094848909865236036670133 3383892085299865878437825)
        ·
          refine ⟨2537919063974899408828369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3383892085299865878437825 2537919063974899408828369)
          ·
            refine ⟨1903439297981174556621277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2537919063974899408828369 1903439297981174556621277)
            ·
              refine ⟨713789736742940458732979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903439297981174556621277 713789736742940458732979)
              ·
                refine ⟨1070684605114410688099469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713789736742940458732979 1070684605114410688099469)
                ·
                  refine ⟨401506726917904008037301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070684605114410688099469 401506726917904008037301)
                  ·
                    rfl

theorem cell20_879673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_879673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879673 prefixEnd_879673 := by exact prefixLift 879673
  have htrace : WordTrace (prefixWord ++ tailWord_879673) baseStart_879673 baseEnd_879673 := by
    simpa [prefixWord, tailWord_879673, baseEnd_879673] using wordTrace_append hprefix tailTrace_879673
  have hstable : (prefixWord ++ tailWord_879673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879673).length < 2 ^ (prefixWord ++ tailWord_879673).sum := by decide
  have hdescent : baseEnd_879673 < baseStart_879673 := by decide
  rcases family_descends (prefixWord ++ tailWord_879673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879687 : List Nat := [1, 1, 4, 1, 3, 4, 2, 4]
def baseStart_879687 : Nat := 118140960795 + 879687 * 2 ^ 59
def prefixEnd_879687 : Nat := 4983230072969 + 3 ^ 40 * 879687 * 2
def baseEnd_879687 : Nat := 133837705633127393856859

theorem tailTrace_879687 : CollatzResearch.WordTrace tailWord_879687 prefixEnd_879687 133837705633127393856859 := by
  unfold tailWord_879687
  simp only [CollatzResearch.WordTrace]
  refine ⟨32084820764051712423605315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21389880509367808282403543 32084820764051712423605315)
  ·
    refine ⟨48127231146077568635407973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32084820764051712423605315 48127231146077568635407973)
    ·
      refine ⟨9023855839889544119138995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48127231146077568635407973 9023855839889544119138995)
      ·
        refine ⟨13535783759834316178708493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9023855839889544119138995 13535783759834316178708493)
        ·
          refine ⟨5075918909937868567015685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13535783759834316178708493 5075918909937868567015685)
          ·
            refine ⟨951734795613350356315441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5075918909937868567015685 951734795613350356315441)
            ·
              refine ⟨713801096710012767236581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 951734795613350356315441 713801096710012767236581)
              ·
                refine ⟨133837705633127393856859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 713801096710012767236581 133837705633127393856859)
                ·
                  rfl

theorem cell20_879687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 4].length) (baseStart_879687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879687 prefixEnd_879687 := by exact prefixLift 879687
  have htrace : WordTrace (prefixWord ++ tailWord_879687) baseStart_879687 baseEnd_879687 := by
    simpa [prefixWord, tailWord_879687, baseEnd_879687] using wordTrace_append hprefix tailTrace_879687
  have hstable : (prefixWord ++ tailWord_879687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879687).length < 2 ^ (prefixWord ++ tailWord_879687).sum := by decide
  have hdescent : baseEnd_879687 < baseStart_879687 := by decide
  rcases family_descends (prefixWord ++ tailWord_879687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879714 : List Nat := [3, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_879714 : Nat := 118140960795 + 879714 * 2 ^ 59
def prefixEnd_879714 : Nat := 4983230072969 + 3 ^ 40 * 879714 * 2
def baseEnd_879714 : Nat := 401525440435090087670467

theorem tailTrace_879714 : CollatzResearch.WordTrace tailWord_879714 prefixEnd_879714 401525440435090087670467 := by
  unfold tailWord_879714
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021451383738474008709549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21390537023302597356558797 8021451383738474008709549)
  ·
    refine ⟨3008044268901927753266081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8021451383738474008709549 3008044268901927753266081)
    ·
      refine ⟨2256033201676445814949561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3008044268901927753266081 2256033201676445814949561)
      ·
        refine ⟨1692024901257334361212171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2256033201676445814949561 1692024901257334361212171)
        ·
          refine ⟨2538037351886001541818257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692024901257334361212171 2538037351886001541818257)
          ·
            refine ⟨1903528013914501156363693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538037351886001541818257 1903528013914501156363693)
            ·
              refine ⟨713823005217937933636385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1903528013914501156363693 713823005217937933636385)
              ·
                refine ⟨535367253913453450227289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 713823005217937933636385 535367253913453450227289)
                ·
                  refine ⟨401525440435090087670467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535367253913453450227289 401525440435090087670467)
                  ·
                    rfl

theorem cell20_879714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_879714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879714 prefixEnd_879714 := by exact prefixLift 879714
  have htrace : WordTrace (prefixWord ++ tailWord_879714) baseStart_879714 baseEnd_879714 := by
    simpa [prefixWord, tailWord_879714, baseEnd_879714] using wordTrace_append hprefix tailTrace_879714
  have hstable : (prefixWord ++ tailWord_879714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879714).length < 2 ^ (prefixWord ++ tailWord_879714).sum := by decide
  have hdescent : baseEnd_879714 < baseStart_879714 := by decide
  rcases family_descends (prefixWord ++ tailWord_879714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879715 : List Nat := [1, 1, 1, 5, 1, 1, 1, 6, 3]
def baseStart_879715 : Nat := 118140960795 + 879715 * 2 ^ 59
def prefixEnd_879715 : Nat := 4983230072969 + 3 ^ 40 * 879715 * 2
def baseEnd_879715 : Nat := 401525896862338528637129

theorem tailTrace_879715 : CollatzResearch.WordTrace tailWord_879715 prefixEnd_879715 401525896862338528637129 := by
  unfold tailWord_879715
  simp only [CollatzResearch.WordTrace]
  refine ⟨32085842007950273205624599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21390561338633515470416399 32085842007950273205624599)
  ·
    refine ⟨48128763011925409808436899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32085842007950273205624599 48128763011925409808436899)
    ·
      refine ⟨72193144517888114712655349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48128763011925409808436899 72193144517888114712655349)
      ·
        refine ⟨6768107298552010754311439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 72193144517888114712655349 6768107298552010754311439)
        ·
          refine ⟨10152160947828016131467159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768107298552010754311439 10152160947828016131467159)
          ·
            refine ⟨15228241421742024197200739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10152160947828016131467159 15228241421742024197200739)
            ·
              refine ⟨22842362132613036295801109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15228241421742024197200739 22842362132613036295801109)
              ·
                refine ⟨1070735724966236076365677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22842362132613036295801109 1070735724966236076365677)
                ·
                  refine ⟨401525896862338528637129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070735724966236076365677 401525896862338528637129)
                  ·
                    rfl

theorem cell20_879715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3].length) (baseStart_879715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879715 prefixEnd_879715 := by exact prefixLift 879715
  have htrace : WordTrace (prefixWord ++ tailWord_879715) baseStart_879715 baseEnd_879715 := by
    simpa [prefixWord, tailWord_879715, baseEnd_879715] using wordTrace_append hprefix tailTrace_879715
  have hstable : (prefixWord ++ tailWord_879715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879715).length < 2 ^ (prefixWord ++ tailWord_879715).sum := by decide
  have hdescent : baseEnd_879715 < baseStart_879715 := by decide
  rcases family_descends (prefixWord ++ tailWord_879715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879767 : List Nat := [1, 1, 3, 3, 3, 9]
def baseStart_879767 : Nat := 118140960795 + 879767 * 2 ^ 59
def prefixEnd_879767 : Nat := 4983230072969 + 3 ^ 40 * 879767 * 2
def baseEnd_879767 : Nat := 14872208558491016996429

theorem tailTrace_879767 : CollatzResearch.WordTrace tailWord_879767 prefixEnd_879767 14872208558491016996429 := by
  unfold tailWord_879767
  simp only [CollatzResearch.WordTrace]
  refine ⟨32087738603761886086517555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21391825735841257391011703 32087738603761886086517555)
  ·
    refine ⟨48131607905642829129776333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32087738603761886086517555 48131607905642829129776333)
    ·
      refine ⟨18049352964616060923666125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48131607905642829129776333 18049352964616060923666125)
      ·
        refine ⟨6768507361731022846374797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18049352964616060923666125 6768507361731022846374797)
        ·
          refine ⟨2538190260649133567390549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6768507361731022846374797 2538190260649133567390549)
          ·
            refine ⟨14872208558491016996429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2538190260649133567390549 14872208558491016996429)
            ·
              rfl

theorem cell20_879767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 9].length) (baseStart_879767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879767 prefixEnd_879767 := by exact prefixLift 879767
  have htrace : WordTrace (prefixWord ++ tailWord_879767) baseStart_879767 baseEnd_879767 := by
    simpa [prefixWord, tailWord_879767, baseEnd_879767] using wordTrace_append hprefix tailTrace_879767
  have hstable : (prefixWord ++ tailWord_879767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879767).length < 2 ^ (prefixWord ++ tailWord_879767).sum := by decide
  have hdescent : baseEnd_879767 < baseStart_879767 := by decide
  rcases family_descends (prefixWord ++ tailWord_879767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879770 : List Nat := [3, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_879770 : Nat := 118140960795 + 879770 * 2 ^ 59
def prefixEnd_879770 : Nat := 4983230072969 + 3 ^ 40 * 879770 * 2
def baseEnd_879770 : Nat := 401551000361002781803571

theorem tailTrace_879770 : CollatzResearch.WordTrace tailWord_879770 prefixEnd_879770 401551000361002781803571 := by
  unfold tailWord_879770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8021962005687754399719191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21391898681834011732584509 8021962005687754399719191)
  ·
    refine ⟨12032943008531631599578787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8021962005687754399719191 12032943008531631599578787)
    ·
      refine ⟨18049414512797447399368181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12032943008531631599578787 18049414512797447399368181)
      ·
        refine ⟨1692132610574760693690767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18049414512797447399368181 1692132610574760693690767)
        ·
          refine ⟨2538198915862141040536151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692132610574760693690767 2538198915862141040536151)
          ·
            refine ⟨3807298373793211560804227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538198915862141040536151 3807298373793211560804227)
            ·
              refine ⟨5710947560689817341206341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3807298373793211560804227 5710947560689817341206341)
              ·
                refine ⟨1070802667629340751476189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5710947560689817341206341 1070802667629340751476189)
                ·
                  refine ⟨401551000361002781803571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070802667629340751476189 401551000361002781803571)
                  ·
                    rfl

theorem cell20_879770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_879770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879770 prefixEnd_879770 := by exact prefixLift 879770
  have htrace : WordTrace (prefixWord ++ tailWord_879770) baseStart_879770 baseEnd_879770 := by
    simpa [prefixWord, tailWord_879770, baseEnd_879770] using wordTrace_append hprefix tailTrace_879770
  have hstable : (prefixWord ++ tailWord_879770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879770).length < 2 ^ (prefixWord ++ tailWord_879770).sum := by decide
  have hdescent : baseEnd_879770 < baseStart_879770 := by decide
  rcases family_descends (prefixWord ++ tailWord_879770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879791 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 3]
def baseStart_879791 : Nat := 118140960795 + 879791 * 2 ^ 59
def prefixEnd_879791 : Nat := 4983230072969 + 3 ^ 40 * 879791 * 2
def baseEnd_879791 : Nat := 401560585333220042103485

theorem tailTrace_879791 : CollatzResearch.WordTrace tailWord_879791 prefixEnd_879791 401560585333220042103485 := by
  unfold tailWord_879791
  simp only [CollatzResearch.WordTrace]
  refine ⟨32088613955674938185391227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21392409303783292123594151 32088613955674938185391227)
  ·
    refine ⟨48132920933512407278086841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32088613955674938185391227 48132920933512407278086841)
    ·
      refine ⟨36099690700134305458565131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48132920933512407278086841 36099690700134305458565131)
      ·
        refine ⟨54149536050201458187847697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36099690700134305458565131 54149536050201458187847697)
        ·
          refine ⟨40612152037651093640885773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54149536050201458187847697 40612152037651093640885773)
          ·
            refine ⟨15229557014119160115332165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40612152037651093640885773 15229557014119160115332165)
            ·
              refine ⟨2855541940147342521624781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15229557014119160115332165 2855541940147342521624781)
              ·
                refine ⟨1070828227555253445609293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2855541940147342521624781 1070828227555253445609293)
                ·
                  refine ⟨401560585333220042103485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070828227555253445609293 401560585333220042103485)
                  ·
                    rfl

theorem cell20_879791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 3].length) (baseStart_879791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879791 prefixEnd_879791 := by exact prefixLift 879791
  have htrace : WordTrace (prefixWord ++ tailWord_879791) baseStart_879791 baseEnd_879791 := by
    simpa [prefixWord, tailWord_879791, baseEnd_879791] using wordTrace_append hprefix tailTrace_879791
  have hstable : (prefixWord ++ tailWord_879791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879791).length < 2 ^ (prefixWord ++ tailWord_879791).sum := by decide
  have hdescent : baseEnd_879791 < baseStart_879791 := by decide
  rcases family_descends (prefixWord ++ tailWord_879791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879805 : List Nat := [1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_879805 : Nat := 118140960795 + 879805 * 2 ^ 59
def prefixEnd_879805 : Nat := 4983230072969 + 3 ^ 40 * 879805 * 2
def baseEnd_879805 : Nat := 133855658438232738545587

theorem tailTrace_879805 : CollatzResearch.WordTrace tailWord_879805 prefixEnd_879805 133855658438232738545587 := by
  unfold tailWord_879805
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089124577624218576400869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21392749718416145717600579 32089124577624218576400869)
  ·
    refine ⟨6016710858304540983075163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32089124577624218576400869 6016710858304540983075163)
    ·
      refine ⟨9025066287456811474612745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016710858304540983075163 9025066287456811474612745)
      ·
        refine ⟨6768799715592608605959559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9025066287456811474612745 6768799715592608605959559)
        ·
          refine ⟨10153199573388912908939339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6768799715592608605959559 10153199573388912908939339)
          ·
            refine ⟨15229799360083369363409009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10153199573388912908939339 15229799360083369363409009)
            ·
              refine ⟨11422349520062527022556757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15229799360083369363409009 11422349520062527022556757)
              ·
                refine ⟨133855658438232738545587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11422349520062527022556757 133855658438232738545587)
                ·
                  rfl

theorem cell20_879805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_879805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879805 prefixEnd_879805 := by exact prefixLift 879805
  have htrace : WordTrace (prefixWord ++ tailWord_879805) baseStart_879805 baseEnd_879805 := by
    simpa [prefixWord, tailWord_879805, baseEnd_879805] using wordTrace_append hprefix tailTrace_879805
  have hstable : (prefixWord ++ tailWord_879805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879805).length < 2 ^ (prefixWord ++ tailWord_879805).sum := by decide
  have hdescent : baseEnd_879805 < baseStart_879805 := by decide
  rcases family_descends (prefixWord ++ tailWord_879805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879821 : List Nat := [1, 6, 2, 2, 1, 2, 1, 2, 3]
def baseStart_879821 : Nat := 118140960795 + 879821 * 2 ^ 59
def prefixEnd_879821 : Nat := 4983230072969 + 3 ^ 40 * 879821 * 2
def baseEnd_879821 : Nat := 401574278150673271103363

theorem tailTrace_879821 : CollatzResearch.WordTrace tailWord_879821 prefixEnd_879821 401574278150673271103363 := by
  unfold tailWord_879821
  simp only [CollatzResearch.WordTrace]
  refine ⟨32089708145566253308983317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21393138763710835539322211 32089708145566253308983317)
  ·
    refine ⟨1504205069323418123858593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32089708145566253308983317 1504205069323418123858593)
    ·
      refine ⟨1128153801992563592893945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1504205069323418123858593 1128153801992563592893945)
      ·
        refine ⟨846115351494422694670459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1128153801992563592893945 846115351494422694670459)
        ·
          refine ⟨1269173027241634042005689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846115351494422694670459 1269173027241634042005689)
          ·
            refine ⟨951879770431225531504267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269173027241634042005689 951879770431225531504267)
            ·
              refine ⟨1427819655646838297256401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 951879770431225531504267 1427819655646838297256401)
              ·
                refine ⟨1070864741735128722942301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1427819655646838297256401 1070864741735128722942301)
                ·
                  refine ⟨401574278150673271103363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070864741735128722942301 401574278150673271103363)
                  ·
                    rfl

theorem cell20_879821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_879821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879821 prefixEnd_879821 := by exact prefixLift 879821
  have htrace : WordTrace (prefixWord ++ tailWord_879821) baseStart_879821 baseEnd_879821 := by
    simpa [prefixWord, tailWord_879821, baseEnd_879821] using wordTrace_append hprefix tailTrace_879821
  have hstable : (prefixWord ++ tailWord_879821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879821).length < 2 ^ (prefixWord ++ tailWord_879821).sum := by decide
  have hdescent : baseEnd_879821 < baseStart_879821 := by decide
  rcases family_descends (prefixWord ++ tailWord_879821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879822 : List Nat := [4, 1, 1, 1, 5, 1, 7]
def baseStart_879822 : Nat := 118140960795 + 879822 * 2 ^ 59
def prefixEnd_879822 : Nat := 4983230072969 + 3 ^ 40 * 879822 * 2
def baseEnd_879822 : Nat := 44619414953102412452225

theorem tailTrace_879822 : CollatzResearch.WordTrace tailWord_879822 prefixEnd_879822 44619414953102412452225 := by
  unfold tailWord_879822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011218077320328809971215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21393163079041753653179813 4011218077320328809971215)
  ·
    refine ⟨6016827115980493214956823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4011218077320328809971215 6016827115980493214956823)
    ·
      refine ⟨9025240673970739822435235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6016827115980493214956823 9025240673970739822435235)
      ·
        refine ⟨13537861010956109733652853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9025240673970739822435235 13537861010956109733652853)
        ·
          refine ⟨1269174469777135287529955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13537861010956109733652853 1269174469777135287529955)
          ·
            refine ⟨1903761704665702931294933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269174469777135287529955 1903761704665702931294933)
            ·
              refine ⟨44619414953102412452225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1903761704665702931294933 44619414953102412452225)
              ·
                rfl

theorem cell20_879822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 7].length) (baseStart_879822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879822 prefixEnd_879822 := by exact prefixLift 879822
  have htrace : WordTrace (prefixWord ++ tailWord_879822) baseStart_879822 baseEnd_879822 := by
    simpa [prefixWord, tailWord_879822, baseEnd_879822] using wordTrace_append hprefix tailTrace_879822
  have hstable : (prefixWord ++ tailWord_879822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879822).length < 2 ^ (prefixWord ++ tailWord_879822).sum := by decide
  have hdescent : baseEnd_879822 < baseStart_879822 := by decide
  rcases family_descends (prefixWord ++ tailWord_879822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879853 : List Nat := [1, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_879853 : Nat := 118140960795 + 879853 * 2 ^ 59
def prefixEnd_879853 : Nat := 4983230072969 + 3 ^ 40 * 879853 * 2
def baseEnd_879853 : Nat := 401588883822623382036565

theorem tailTrace_879853 : CollatzResearch.WordTrace tailWord_879853 prefixEnd_879853 401588883822623382036565 := by
  unfold tailWord_879853
  simp only [CollatzResearch.WordTrace]
  refine ⟨32090875281450322774148213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21393916854300215182765475 32090875281450322774148213)
  ·
    refine ⟨3008519557635967760076395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32090875281450322774148213 3008519557635967760076395)
    ·
      refine ⟨4512779336453951640114593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3008519557635967760076395 4512779336453951640114593)
      ·
        refine ⟨3384584502340463730085945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4512779336453951640114593 3384584502340463730085945)
        ·
          refine ⟨2538438376755347797564459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3384584502340463730085945 2538438376755347797564459)
          ·
            refine ⟨3807657565133021696346689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538438376755347797564459 3807657565133021696346689)
            ·
              refine ⟨2855743173849766272260017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3807657565133021696346689 2855743173849766272260017)
              ·
                refine ⟨2141807380387324704195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2855743173849766272260017 2141807380387324704195013)
                ·
                  refine ⟨401588883822623382036565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2141807380387324704195013 401588883822623382036565)
                  ·
                    rfl

theorem cell20_879853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_879853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879853 prefixEnd_879853 := by exact prefixLift 879853
  have htrace : WordTrace (prefixWord ++ tailWord_879853) baseStart_879853 baseEnd_879853 := by
    simpa [prefixWord, tailWord_879853, baseEnd_879853] using wordTrace_append hprefix tailTrace_879853
  have hstable : (prefixWord ++ tailWord_879853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879853).length < 2 ^ (prefixWord ++ tailWord_879853).sum := by decide
  have hdescent : baseEnd_879853 < baseStart_879853 := by decide
  rcases family_descends (prefixWord ++ tailWord_879853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879898 : List Nat := [3, 1, 1, 3, 3, 2, 2, 5]
def baseStart_879898 : Nat := 118140960795 + 879898 * 2 ^ 59
def prefixEnd_879898 : Nat := 4983230072969 + 3 ^ 40 * 879898 * 2
def baseEnd_879898 : Nat := 133869807682934408512127

theorem tailTrace_879898 : CollatzResearch.WordTrace tailWord_879898 prefixEnd_879898 133869807682934408512127 := by
  unfold tailWord_879898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023129141571823864884087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21395011044191530306357565 8023129141571823864884087)
  ·
    refine ⟨12034693712357735797326131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8023129141571823864884087 12034693712357735797326131)
    ·
      refine ⟨18052040568536603695989197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12034693712357735797326131 18052040568536603695989197)
      ·
        refine ⟨6769515213201226385995949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18052040568536603695989197 6769515213201226385995949)
        ·
          refine ⟨2538568204950459894748481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6769515213201226385995949 2538568204950459894748481)
          ·
            refine ⟨1903926153712844921061361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2538568204950459894748481 1903926153712844921061361)
            ·
              refine ⟨1427944615284633690796021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1903926153712844921061361 1427944615284633690796021)
              ·
                refine ⟨133869807682934408512127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1427944615284633690796021 133869807682934408512127)
                ·
                  rfl

theorem cell20_879898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 5].length) (baseStart_879898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879898 prefixEnd_879898 := by exact prefixLift 879898
  have htrace : WordTrace (prefixWord ++ tailWord_879898) baseStart_879898 baseEnd_879898 := by
    simpa [prefixWord, tailWord_879898, baseEnd_879898] using wordTrace_append hprefix tailTrace_879898
  have hstable : (prefixWord ++ tailWord_879898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879898).length < 2 ^ (prefixWord ++ tailWord_879898).sum := by decide
  have hdescent : baseEnd_879898 < baseStart_879898 := by decide
  rcases family_descends (prefixWord ++ tailWord_879898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879901 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 3]
def baseStart_879901 : Nat := 118140960795 + 879901 * 2 ^ 59
def prefixEnd_879901 : Nat := 4983230072969 + 3 ^ 40 * 879901 * 2
def baseEnd_879901 : Nat := 401610792330548548436369

theorem tailTrace_879901 : CollatzResearch.WordTrace tailWord_879901 prefixEnd_879901 401610792330548548436369 := by
  unfold tailWord_879901
  simp only [CollatzResearch.WordTrace]
  refine ⟨32092625985276426971895557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21395083990184284647930371 32092625985276426971895557)
  ·
    refine ⟨6017367372239330057230417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32092625985276426971895557 6017367372239330057230417)
    ·
      refine ⟨4513025529179497542922813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6017367372239330057230417 4513025529179497542922813)
      ·
        refine ⟨1692384573442311578596055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4513025529179497542922813 1692384573442311578596055)
        ·
          refine ⟨2538576860163467367894083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1692384573442311578596055 2538576860163467367894083)
          ·
            refine ⟨3807865290245201051841125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2538576860163467367894083 3807865290245201051841125)
            ·
              refine ⟨713974741920975197220211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3807865290245201051841125 713974741920975197220211)
              ·
                refine ⟨1070962112881462795830317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 713974741920975197220211 1070962112881462795830317)
                ·
                  refine ⟨401610792330548548436369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1070962112881462795830317 401610792330548548436369)
                  ·
                    rfl

theorem cell20_879901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_879901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879901 prefixEnd_879901 := by exact prefixLift 879901
  have htrace : WordTrace (prefixWord ++ tailWord_879901) baseStart_879901 baseEnd_879901 := by
    simpa [prefixWord, tailWord_879901, baseEnd_879901] using wordTrace_append hprefix tailTrace_879901
  have hstable : (prefixWord ++ tailWord_879901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879901).length < 2 ^ (prefixWord ++ tailWord_879901).sum := by decide
  have hdescent : baseEnd_879901 < baseStart_879901 := by decide
  rcases family_descends (prefixWord ++ tailWord_879901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879943 : List Nat := [1, 1, 4, 1, 2, 3, 1, 4, 3]
def baseStart_879943 : Nat := 118140960795 + 879943 * 2 ^ 59
def prefixEnd_879943 : Nat := 4983230072969 + 3 ^ 40 * 879943 * 2
def baseEnd_879943 : Nat := 401629962274983069036197

theorem tailTrace_879943 : CollatzResearch.WordTrace tailWord_879943 prefixEnd_879943 401629962274983069036197 := by
  unfold tailWord_879943
  simp only [CollatzResearch.WordTrace]
  refine ⟨32094157851124268144924483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21396105234082845429949655 32094157851124268144924483)
  ·
    refine ⟨48141236776686402217386725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32094157851124268144924483 48141236776686402217386725)
    ·
      refine ⟨9026481895628700415760011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48141236776686402217386725 9026481895628700415760011)
      ·
        refine ⟨13539722843443050623640017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9026481895628700415760011 13539722843443050623640017)
        ·
          refine ⟨10154792132582287967730013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13539722843443050623640017 10154792132582287967730013)
          ·
            refine ⟨3808047049718357987898755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10154792132582287967730013 3808047049718357987898755)
            ·
              refine ⟨5712070574577536981848133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3808047049718357987898755 5712070574577536981848133)
              ·
                refine ⟨1071013232733288184096525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5712070574577536981848133 1071013232733288184096525)
                ·
                  refine ⟨401629962274983069036197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071013232733288184096525 401629962274983069036197)
                  ·
                    rfl

theorem cell20_879943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 4, 3].length) (baseStart_879943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879943 prefixEnd_879943 := by exact prefixLift 879943
  have htrace : WordTrace (prefixWord ++ tailWord_879943) baseStart_879943 baseEnd_879943 := by
    simpa [prefixWord, tailWord_879943, baseEnd_879943] using wordTrace_append hprefix tailTrace_879943
  have hstable : (prefixWord ++ tailWord_879943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879943).length < 2 ^ (prefixWord ++ tailWord_879943).sum := by decide
  have hdescent : baseEnd_879943 < baseStart_879943 := by decide
  rcases family_descends (prefixWord ++ tailWord_879943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879949 : List Nat := [1, 6, 1, 3, 2, 1, 1, 5]
def baseStart_879949 : Nat := 118140960795 + 879949 * 2 ^ 59
def prefixEnd_879949 : Nat := 4983230072969 + 3 ^ 40 * 879949 * 2
def baseEnd_879949 : Nat := 133877566946157904945391

theorem tailTrace_879949 : CollatzResearch.WordTrace tailWord_879949 prefixEnd_879949 133877566946157904945391 := by
  unfold tailWord_879949
  simp only [CollatzResearch.WordTrace]
  refine ⟨32094376689102531169642901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21396251126068354113095267 32094376689102531169642901)
  ·
    refine ⟨1504423907301681148577011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32094376689102531169642901 1504423907301681148577011)
    ·
      refine ⟨2256635860952521722865517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1504423907301681148577011 2256635860952521722865517)
      ·
        refine ⟨846238447857195646074569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2256635860952521722865517 846238447857195646074569)
        ·
          refine ⟨634678835892896734555927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846238447857195646074569 634678835892896734555927)
          ·
            refine ⟨952018253839345101833891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634678835892896734555927 952018253839345101833891)
            ·
              refine ⟨1428027380759017652750837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952018253839345101833891 1428027380759017652750837)
              ·
                refine ⟨133877566946157904945391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1428027380759017652750837 133877566946157904945391)
                ·
                  rfl

theorem cell20_879949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 5].length) (baseStart_879949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879949 prefixEnd_879949 := by exact prefixLift 879949
  have htrace : WordTrace (prefixWord ++ tailWord_879949) baseStart_879949 baseEnd_879949 := by
    simpa [prefixWord, tailWord_879949, baseEnd_879949] using wordTrace_append hprefix tailTrace_879949
  have hstable : (prefixWord ++ tailWord_879949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879949).length < 2 ^ (prefixWord ++ tailWord_879949).sum := by decide
  have hdescent : baseEnd_879949 < baseStart_879949 := by decide
  rcases family_descends (prefixWord ++ tailWord_879949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_879950 : List Nat := [4, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_879950 : Nat := 118140960795 + 879950 * 2 ^ 59
def prefixEnd_879950 : Nat := 4983230072969 + 3 ^ 40 * 879950 * 2
def baseEnd_879950 : Nat := 401633157265722155802835

theorem tailTrace_879950 : CollatzResearch.WordTrace tailWord_879950 prefixEnd_879950 401633157265722155802835 := by
  unfold tailWord_879950
  simp only [CollatzResearch.WordTrace]
  refine ⟨4011801645262363542553663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21396275441399272226952869 4011801645262363542553663)
  ·
    refine ⟨6017702467893545313830495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4011801645262363542553663 6017702467893545313830495)
    ·
      refine ⟨9026553701840317970745743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6017702467893545313830495 9026553701840317970745743)
      ·
        refine ⟨13539830552760476956118615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9026553701840317970745743 13539830552760476956118615)
        ·
          refine ⟨20309745829140715434177923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13539830552760476956118615 20309745829140715434177923)
          ·
            refine ⟨30464618743711073151266885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20309745829140715434177923 30464618743711073151266885)
            ·
              refine ⟨5712116014445826215862541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30464618743711073151266885 5712116014445826215862541)
              ·
                refine ⟨2142043505417184830948453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5712116014445826215862541 2142043505417184830948453)
                ·
                  refine ⟨401633157265722155802835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142043505417184830948453 401633157265722155802835)
                  ·
                    rfl

theorem cell20_879950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_879950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_879950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_879950 prefixEnd_879950 := by exact prefixLift 879950
  have htrace : WordTrace (prefixWord ++ tailWord_879950) baseStart_879950 baseEnd_879950 := by
    simpa [prefixWord, tailWord_879950, baseEnd_879950] using wordTrace_append hprefix tailTrace_879950
  have hstable : (prefixWord ++ tailWord_879950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_879950).length < 2 ^ (prefixWord ++ tailWord_879950).sum := by decide
  have hdescent : baseEnd_879950 < baseStart_879950 := by decide
  rcases family_descends (prefixWord ++ tailWord_879950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880005 : List Nat := [1, 3, 1, 1, 3, 1, 4, 4, 2]
def baseStart_880005 : Nat := 118140960795 + 880005 * 2 ^ 59
def prefixEnd_880005 : Nat := 4983230072969 + 3 ^ 40 * 880005 * 2
def baseEnd_880005 : Nat := 401658260764386408969277

theorem tailTrace_880005 : CollatzResearch.WordTrace tailWord_880005 prefixEnd_880005 401658260764386408969277 := by
  unfold tailWord_880005
  simp only [CollatzResearch.WordTrace]
  refine ⟨32096419176899652733681469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21397612784599768489120979 32096419176899652733681469)
  ·
    refine ⟨12036157191337369775130551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32096419176899652733681469 12036157191337369775130551)
    ·
      refine ⟨18054235787006054662695827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036157191337369775130551 18054235787006054662695827)
      ·
        refine ⟨27081353680509081994043741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18054235787006054662695827 27081353680509081994043741)
        ·
          refine ⟨10155507630190905747766403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27081353680509081994043741 10155507630190905747766403)
          ·
            refine ⟨15233261445286358621649605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10155507630190905747766403 15233261445286358621649605)
            ·
              refine ⟨2856236520991192241559301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15233261445286358621649605 2856236520991192241559301)
              ·
                refine ⟨535544347685848545292369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2856236520991192241559301 535544347685848545292369)
                ·
                  refine ⟨401658260764386408969277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535544347685848545292369 401658260764386408969277)
                  ·
                    rfl

theorem cell20_880005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_880005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880005 prefixEnd_880005 := by exact prefixLift 880005
  have htrace : WordTrace (prefixWord ++ tailWord_880005) baseStart_880005 baseEnd_880005 := by
    simpa [prefixWord, tailWord_880005, baseEnd_880005] using wordTrace_append hprefix tailTrace_880005
  have hstable : (prefixWord ++ tailWord_880005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880005).length < 2 ^ (prefixWord ++ tailWord_880005).sum := by decide
  have hdescent : baseEnd_880005 < baseStart_880005 := by decide
  rcases family_descends (prefixWord ++ tailWord_880005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880026 : List Nat := [3, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_880026 : Nat := 118140960795 + 880026 * 2 ^ 59
def prefixEnd_880026 : Nat := 4983230072969 + 3 ^ 40 * 880026 * 2
def baseEnd_880026 : Nat := 401667845736603669269191

theorem tailTrace_880026 : CollatzResearch.WordTrace tailWord_880026 prefixEnd_880026 401667845736603669269191 := by
  unfold tailWord_880026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024296277455893330048983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21398123406549048880130621 8024296277455893330048983)
  ·
    refine ⟨12036444416183839995073475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024296277455893330048983 12036444416183839995073475)
    ·
      refine ⟨18054666624275759992610213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12036444416183839995073475 18054666624275759992610213)
      ·
        refine ⟨3385249992051704998614415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18054666624275759992610213 3385249992051704998614415)
        ·
          refine ⟨5077874988077557497921623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385249992051704998614415 5077874988077557497921623)
          ·
            refine ⟨7616812482116336246882435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5077874988077557497921623 7616812482116336246882435)
            ·
              refine ⟨11425218723174504370323653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7616812482116336246882435 11425218723174504370323653)
              ·
                refine ⟨2142228510595219569435685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11425218723174504370323653 2142228510595219569435685)
                ·
                  refine ⟨401667845736603669269191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142228510595219569435685 401667845736603669269191)
                  ·
                    rfl

theorem cell20_880026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_880026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880026 prefixEnd_880026 := by exact prefixLift 880026
  have htrace : WordTrace (prefixWord ++ tailWord_880026) baseStart_880026 baseEnd_880026 := by
    simpa [prefixWord, tailWord_880026, baseEnd_880026] using wordTrace_append hprefix tailTrace_880026
  have hstable : (prefixWord ++ tailWord_880026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880026).length < 2 ^ (prefixWord ++ tailWord_880026).sum := by decide
  have hdescent : baseEnd_880026 < baseStart_880026 := by decide
  rcases family_descends (prefixWord ++ tailWord_880026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880029 : List Nat := [1, 4, 2, 1, 3, 3, 2, 4]
def baseStart_880029 : Nat := 118140960795 + 880029 * 2 ^ 59
def prefixEnd_880029 : Nat := 4983230072969 + 3 ^ 40 * 880029 * 2
def baseEnd_880029 : Nat := 133889738339449664056393

theorem tailTrace_880029 : CollatzResearch.WordTrace tailWord_880029 prefixEnd_880029 133889738339449664056393 := by
  unfold tailWord_880029
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097294528812704832555141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21398196352541803221703427 32097294528812704832555141)
  ·
    refine ⟨6018242724152382156104089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32097294528812704832555141 6018242724152382156104089)
    ·
      refine ⟨4513682043114286617078067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6018242724152382156104089 4513682043114286617078067)
      ·
        refine ⟨6770523064671429925617101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4513682043114286617078067 6770523064671429925617101)
        ·
          refine ⟨2538946149251786222106413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6770523064671429925617101 2538946149251786222106413)
          ·
            refine ⟨952104805969419833289905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2538946149251786222106413 952104805969419833289905)
            ·
              refine ⟨714078604477064874967429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952104805969419833289905 714078604477064874967429)
              ·
                refine ⟨133889738339449664056393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714078604477064874967429 133889738339449664056393)
                ·
                  rfl

theorem cell20_880029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 4].length) (baseStart_880029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880029 prefixEnd_880029 := by exact prefixLift 880029
  have htrace : WordTrace (prefixWord ++ tailWord_880029) baseStart_880029 baseEnd_880029 := by
    simpa [prefixWord, tailWord_880029, baseEnd_880029] using wordTrace_append hprefix tailTrace_880029
  have hstable : (prefixWord ++ tailWord_880029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880029).length < 2 ^ (prefixWord ++ tailWord_880029).sum := by decide
  have hdescent : baseEnd_880029 < baseStart_880029 := by decide
  rcases family_descends (prefixWord ++ tailWord_880029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880047 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_880047 : Nat := 118140960795 + 880047 * 2 ^ 59
def prefixEnd_880047 : Nat := 4983230072969 + 3 ^ 40 * 880047 * 2
def baseEnd_880047 : Nat := 401677430708820929569105

theorem tailTrace_880047 : CollatzResearch.WordTrace tailWord_880047 prefixEnd_880047 401677430708820929569105 := by
  unfold tailWord_880047
  simp only [CollatzResearch.WordTrace]
  refine ⟨32097951042747493906710395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21398634028498329271140263 32097951042747493906710395)
  ·
    refine ⟨48146926564121240860065593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32097951042747493906710395 48146926564121240860065593)
    ·
      refine ⟨36110194923090930645049195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48146926564121240860065593 36110194923090930645049195)
      ·
        refine ⟨54165292384636395967573793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36110194923090930645049195 54165292384636395967573793)
        ·
          refine ⟨40623969288477296975680345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 54165292384636395967573793 40623969288477296975680345)
          ·
            refine ⟨30467976966357972731760259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40623969288477296975680345 30467976966357972731760259)
            ·
              refine ⟨45701965449536959097640389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30467976966357972731760259 45701965449536959097640389)
              ·
                refine ⟨8569118521788179830807573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45701965449536959097640389 8569118521788179830807573)
                ·
                  refine ⟨401677430708820929569105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8569118521788179830807573 401677430708820929569105)
                  ·
                    rfl

theorem cell20_880047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_880047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880047 prefixEnd_880047 := by exact prefixLift 880047
  have htrace : WordTrace (prefixWord ++ tailWord_880047) baseStart_880047 baseEnd_880047 := by
    simpa [prefixWord, tailWord_880047, baseEnd_880047] using wordTrace_append hprefix tailTrace_880047
  have hstable : (prefixWord ++ tailWord_880047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880047).length < 2 ^ (prefixWord ++ tailWord_880047).sum := by decide
  have hdescent : baseEnd_880047 < baseStart_880047 := by decide
  rcases family_descends (prefixWord ++ tailWord_880047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880060 : List Nat := [2, 2, 2, 4, 2, 2, 1, 1, 4]
def baseStart_880060 : Nat := 118140960795 + 880060 * 2 ^ 59
def prefixEnd_880060 : Nat := 4983230072969 + 3 ^ 40 * 880060 * 2
def baseEnd_880060 : Nat := 401683364263050662135719

theorem tailTrace_880060 : CollatzResearch.WordTrace tailWord_880060 prefixEnd_880060 401683364263050662135719 := by
  unfold tailWord_880060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049212595850198563466817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21398950127800264751289089 16049212595850198563466817)
  ·
    refine ⟨12036909446887648922600113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16049212595850198563466817 12036909446887648922600113)
    ·
      refine ⟨9027682085165736691950085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12036909446887648922600113 9027682085165736691950085)
      ·
        refine ⟨1692690390968575629740641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9027682085165736691950085 1692690390968575629740641)
        ·
          refine ⟨1269517793226431722305481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1692690390968575629740641 1269517793226431722305481)
          ·
            refine ⟨952138344919823791729111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1269517793226431722305481 952138344919823791729111)
            ·
              refine ⟨1428207517379735687593667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952138344919823791729111 1428207517379735687593667)
              ·
                refine ⟨2142311276069603531390501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428207517379735687593667 2142311276069603531390501)
                ·
                  refine ⟨401683364263050662135719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142311276069603531390501 401683364263050662135719)
                  ·
                    rfl

theorem cell20_880060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_880060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880060 prefixEnd_880060 := by exact prefixLift 880060
  have htrace : WordTrace (prefixWord ++ tailWord_880060) baseStart_880060 baseEnd_880060 := by
    simpa [prefixWord, tailWord_880060, baseEnd_880060] using wordTrace_append hprefix tailTrace_880060
  have hstable : (prefixWord ++ tailWord_880060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880060).length < 2 ^ (prefixWord ++ tailWord_880060).sum := by decide
  have hdescent : baseEnd_880060 < baseStart_880060 := by decide
  rcases family_descends (prefixWord ++ tailWord_880060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880064 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 4]
def baseStart_880064 : Nat := 118140960795 + 880064 * 2 ^ 59
def prefixEnd_880064 : Nat := 4983230072969 + 3 ^ 40 * 880064 * 2
def baseEnd_880064 : Nat := 401685189972044426002369

theorem tailTrace_880064 : CollatzResearch.WordTrace tailWord_880064 prefixEnd_880064 401685189972044426002369 := by
  unfold tailWord_880064
  simp only [CollatzResearch.WordTrace]
  refine ⟨16049285541842952905039623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21399047389123937206719497 16049285541842952905039623)
  ·
    refine ⟨24073928312764429357559435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16049285541842952905039623 24073928312764429357559435)
    ·
      refine ⟨36110892469146644036339153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24073928312764429357559435 36110892469146644036339153)
      ·
        refine ⟨27083169351859983027254365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36110892469146644036339153 27083169351859983027254365)
        ·
          refine ⟨10156188506947493635220387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27083169351859983027254365 10156188506947493635220387)
          ·
            refine ⟨15234282760421240452830581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10156188506947493635220387 15234282760421240452830581)
            ·
              refine ⟨1428214008789491292452867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15234282760421240452830581 1428214008789491292452867)
              ·
                refine ⟨2142321013184236938679301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428214008789491292452867 2142321013184236938679301)
                ·
                  refine ⟨401685189972044426002369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142321013184236938679301 401685189972044426002369)
                  ·
                    rfl

theorem cell20_880064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4].length) (baseStart_880064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880064 prefixEnd_880064 := by exact prefixLift 880064
  have htrace : WordTrace (prefixWord ++ tailWord_880064) baseStart_880064 baseEnd_880064 := by
    simpa [prefixWord, tailWord_880064, baseEnd_880064] using wordTrace_append hprefix tailTrace_880064
  have hstable : (prefixWord ++ tailWord_880064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880064).length < 2 ^ (prefixWord ++ tailWord_880064).sum := by decide
  have hdescent : baseEnd_880064 < baseStart_880064 := by decide
  rcases family_descends (prefixWord ++ tailWord_880064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880071 : List Nat := [1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_880071 : Nat := 118140960795 + 880071 * 2 ^ 59
def prefixEnd_880071 : Nat := 4983230072969 + 3 ^ 40 * 880071 * 2
def baseEnd_880071 : Nat := 133896128320927837589669

theorem tailTrace_880071 : CollatzResearch.WordTrace tailWord_880071 prefixEnd_880071 133896128320927837589669 := by
  unfold tailWord_880071
  simp only [CollatzResearch.WordTrace]
  refine ⟨32098826394660546005584067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21399217596440364003722711 32098826394660546005584067)
  ·
    refine ⟨48148239591990819008376101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32098826394660546005584067 48148239591990819008376101)
    ·
      refine ⟨9027794923498278564070519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48148239591990819008376101 9027794923498278564070519)
      ·
        refine ⟨13541692385247417846105779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027794923498278564070519 13541692385247417846105779)
        ·
          refine ⟨20312538577871126769158669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13541692385247417846105779 20312538577871126769158669)
          ·
            refine ⟨7617201966701672538434501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20312538577871126769158669 7617201966701672538434501)
            ·
              refine ⟨1428225368756563600956469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7617201966701672538434501 1428225368756563600956469)
              ·
                refine ⟨133896128320927837589669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1428225368756563600956469 133896128320927837589669)
                ·
                  rfl

theorem cell20_880071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_880071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880071 prefixEnd_880071 := by exact prefixLift 880071
  have htrace : WordTrace (prefixWord ++ tailWord_880071) baseStart_880071 baseEnd_880071 := by
    simpa [prefixWord, tailWord_880071, baseEnd_880071] using wordTrace_append hprefix tailTrace_880071
  have hstable : (prefixWord ++ tailWord_880071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880071).length < 2 ^ (prefixWord ++ tailWord_880071).sum := by decide
  have hdescent : baseEnd_880071 < baseStart_880071 := by decide
  rcases family_descends (prefixWord ++ tailWord_880071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880074 : List Nat := [3, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_880074 : Nat := 118140960795 + 880074 * 2 ^ 59
def prefixEnd_880074 : Nat := 4983230072969 + 3 ^ 40 * 880074 * 2
def baseEnd_880074 : Nat := 401689754244528835668995

theorem tailTrace_880074 : CollatzResearch.WordTrace tailWord_880074 prefixEnd_880074 401689754244528835668995 := by
  unfold tailWord_880074
  simp only [CollatzResearch.WordTrace]
  refine ⟨8024733953412419379485819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21399290542433118345295517 8024733953412419379485819)
  ·
    refine ⟨12037100930118629069228729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8024733953412419379485819 12037100930118629069228729)
    ·
      refine ⟨9027825697588971801921547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12037100930118629069228729 9027825697588971801921547)
      ·
        refine ⟨13541738546383457702882321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9027825697588971801921547 13541738546383457702882321)
        ·
          refine ⟨10156303909787593277161741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13541738546383457702882321 10156303909787593277161741)
          ·
            refine ⟨3808613966170347478935653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10156303909787593277161741 3808613966170347478935653)
            ·
              refine ⟨714115118656940152300435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3808613966170347478935653 714115118656940152300435)
              ·
                refine ⟨1071172677985410228450653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714115118656940152300435 1071172677985410228450653)
                ·
                  refine ⟨401689754244528835668995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071172677985410228450653 401689754244528835668995)
                  ·
                    rfl

theorem cell20_880074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_880074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880074 prefixEnd_880074 := by exact prefixLift 880074
  have htrace : WordTrace (prefixWord ++ tailWord_880074) baseStart_880074 baseEnd_880074 := by
    simpa [prefixWord, tailWord_880074, baseEnd_880074] using wordTrace_append hprefix tailTrace_880074
  have hstable : (prefixWord ++ tailWord_880074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880074).length < 2 ^ (prefixWord ++ tailWord_880074).sum := by decide
  have hdescent : baseEnd_880074 < baseStart_880074 := by decide
  rcases family_descends (prefixWord ++ tailWord_880074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880109 : List Nat := [1, 5, 1, 3, 10]
def baseStart_880109 : Nat := 118140960795 + 880109 * 2 ^ 59
def prefixEnd_880109 : Nat := 4983230072969 + 3 ^ 40 * 880109 * 2
def baseEnd_880109 : Nat := 4959329990101534191385

theorem tailTrace_880109 : CollatzResearch.WordTrace tailWord_880109 prefixEnd_880109 4959329990101534191385 := by
  unfold tailWord_880109
  simp only [CollatzResearch.WordTrace]
  refine ⟨32100212368522878495467381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21400141579015252330311587 32100212368522878495467381)
  ·
    refine ⟨3009394909549019858950067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32100212368522878495467381 3009394909549019858950067)
    ·
      refine ⟨4514092364323529788425101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3009394909549019858950067 4514092364323529788425101)
      ·
        refine ⟨1692784636621323670659413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4514092364323529788425101 1692784636621323670659413)
        ·
          refine ⟨4959329990101534191385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1692784636621323670659413 4959329990101534191385)
          ·
            rfl

theorem cell20_880109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 10].length) (baseStart_880109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880109 prefixEnd_880109 := by exact prefixLift 880109
  have htrace : WordTrace (prefixWord ++ tailWord_880109) baseStart_880109 baseEnd_880109 := by
    simpa [prefixWord, tailWord_880109, baseEnd_880109] using wordTrace_append hprefix tailTrace_880109
  have hstable : (prefixWord ++ tailWord_880109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880109).length < 2 ^ (prefixWord ++ tailWord_880109).sum := by decide
  have hdescent : baseEnd_880109 < baseStart_880109 := by decide
  rcases family_descends (prefixWord ++ tailWord_880109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880154 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_880154 : Nat := 118140960795 + 880154 * 2 ^ 59
def prefixEnd_880154 : Nat := 4983230072969 + 3 ^ 40 * 880154 * 2
def baseEnd_880154 : Nat := 401726268424404113002001

theorem tailTrace_880154 : CollatzResearch.WordTrace tailWord_880154 prefixEnd_880154 401726268424404113002001 := by
  unfold tailWord_880154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025463413339962795213879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21401235768906567453903677 8025463413339962795213879)
  ·
    refine ⟨12038195120009944192820819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8025463413339962795213879 12038195120009944192820819)
    ·
      refine ⟨18057292680014916289231229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12038195120009944192820819 18057292680014916289231229)
      ·
        refine ⟨6771484755005593608461711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18057292680014916289231229 6771484755005593608461711)
        ·
          refine ⟨10157227132508390412692567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6771484755005593608461711 10157227132508390412692567)
          ·
            refine ⟨15235840698762585619038851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10157227132508390412692567 15235840698762585619038851)
            ·
              refine ⟨22853761048143878428558277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15235840698762585619038851 22853761048143878428558277)
              ·
                refine ⟨4285080196526977205354677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22853761048143878428558277 4285080196526977205354677)
                ·
                  refine ⟨401726268424404113002001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4285080196526977205354677 401726268424404113002001)
                  ·
                    rfl

theorem cell20_880154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_880154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880154 prefixEnd_880154 := by exact prefixLift 880154
  have htrace : WordTrace (prefixWord ++ tailWord_880154) baseStart_880154 baseEnd_880154 := by
    simpa [prefixWord, tailWord_880154, baseEnd_880154] using wordTrace_append hprefix tailTrace_880154
  have hstable : (prefixWord ++ tailWord_880154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880154).length < 2 ^ (prefixWord ++ tailWord_880154).sum := by decide
  have hdescent : baseEnd_880154 < baseStart_880154 := by decide
  rcases family_descends (prefixWord ++ tailWord_880154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880174 : List Nat := [4, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_880174 : Nat := 118140960795 + 880174 * 2 ^ 59
def prefixEnd_880174 : Nat := 4983230072969 + 3 ^ 40 * 880174 * 2
def baseEnd_880174 : Nat := 401735396969372932335253

theorem tailTrace_880174 : CollatzResearch.WordTrace tailWord_880174 prefixEnd_880174 401735396969372932335253 := by
  unfold tailWord_880174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4012822889160924324572947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21401722075524929731055717 4012822889160924324572947)
  ·
    refine ⟨6019234333741386486859421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4012822889160924324572947 6019234333741386486859421)
    ·
      refine ⟨2257212875153019932572283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6019234333741386486859421 2257212875153019932572283)
      ·
        refine ⟨3385819312729529898858425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257212875153019932572283 3385819312729529898858425)
        ·
          refine ⟨2539364484547147424143819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3385819312729529898858425 2539364484547147424143819)
          ·
            refine ⟨3809046726820721136215729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539364484547147424143819 3809046726820721136215729)
            ·
              refine ⟨2856785045115540852161797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3809046726820721136215729 2856785045115540852161797)
              ·
                refine ⟨535647195959163909780337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2856785045115540852161797 535647195959163909780337)
                ·
                  refine ⟨401735396969372932335253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535647195959163909780337 401735396969372932335253)
                  ·
                    rfl

theorem cell20_880174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_880174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880174 prefixEnd_880174 := by exact prefixLift 880174
  have htrace : WordTrace (prefixWord ++ tailWord_880174) baseStart_880174 baseEnd_880174 := by
    simpa [prefixWord, tailWord_880174, baseEnd_880174] using wordTrace_append hprefix tailTrace_880174
  have hstable : (prefixWord ++ tailWord_880174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880174).length < 2 ^ (prefixWord ++ tailWord_880174).sum := by decide
  have hdescent : baseEnd_880174 < baseStart_880174 := by decide
  rcases family_descends (prefixWord ++ tailWord_880174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880282 : List Nat := [3, 1, 1, 15]
def baseStart_880282 : Nat := 118140960795 + 880282 * 2 ^ 59
def prefixEnd_880282 : Nat := 4983230072969 + 3 ^ 40 * 880282 * 2
def baseEnd_880282 : Nat := 1653434942848578422777

theorem tailTrace_880282 : CollatzResearch.WordTrace tailWord_880282 prefixEnd_880282 1653434942848578422777 := by
  unfold tailWord_880282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8026630549224032260378775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21404348131264086027676733 8026630549224032260378775)
  ·
    refine ⟨12039945823836048390568163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8026630549224032260378775 12039945823836048390568163)
    ·
      refine ⟨18059918735754072585852245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12039945823836048390568163 18059918735754072585852245)
      ·
        refine ⟨1653434942848578422777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 18059918735754072585852245 1653434942848578422777)
        ·
          rfl

theorem cell20_880282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 15].length) (baseStart_880282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880282 prefixEnd_880282 := by exact prefixLift 880282
  have htrace : WordTrace (prefixWord ++ tailWord_880282) baseStart_880282 baseEnd_880282 := by
    simpa [prefixWord, tailWord_880282, baseEnd_880282] using wordTrace_append hprefix tailTrace_880282
  have hstable : (prefixWord ++ tailWord_880282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880282).length < 2 ^ (prefixWord ++ tailWord_880282).sum := by decide
  have hdescent : baseEnd_880282 < baseStart_880282 := by decide
  rcases family_descends (prefixWord ++ tailWord_880282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880284 : List Nat := [2, 2, 3, 2, 4, 1, 2, 2, 2]
def baseStart_880284 : Nat := 118140960795 + 880284 * 2 ^ 59
def prefixEnd_880284 : Nat := 4983230072969 + 3 ^ 40 * 880284 * 2
def baseEnd_880284 : Nat := 401785603966701438668137

theorem tailTrace_880284 : CollatzResearch.WordTrace tailWord_880284 prefixEnd_880284 401785603966701438668137 := by
  unfold tailWord_880284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053297571444441691543953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21404396761925922255391937 16053297571444441691543953)
  ·
    refine ⟨12039973178583331268657965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16053297571444441691543953 12039973178583331268657965)
    ·
      refine ⟨4514989941968749225746737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12039973178583331268657965 4514989941968749225746737)
      ·
        refine ⟨3386242456476561919310053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4514989941968749225746737 3386242456476561919310053)
        ·
          refine ⟨634920460589355359870635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3386242456476561919310053 634920460589355359870635)
          ·
            refine ⟨952380690884033039805953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 634920460589355359870635 952380690884033039805953)
            ·
              refine ⟨714285518163024779854465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 952380690884033039805953 714285518163024779854465)
              ·
                refine ⟨535714138622268584890849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714285518163024779854465 535714138622268584890849)
                ·
                  refine ⟨401785603966701438668137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535714138622268584890849 401785603966701438668137)
                  ·
                    rfl

theorem cell20_880284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_880284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880284 prefixEnd_880284 := by exact prefixLift 880284
  have htrace : WordTrace (prefixWord ++ tailWord_880284) baseStart_880284 baseEnd_880284 := by
    simpa [prefixWord, tailWord_880284, baseEnd_880284] using wordTrace_append hprefix tailTrace_880284
  have hstable : (prefixWord ++ tailWord_880284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880284).length < 2 ^ (prefixWord ++ tailWord_880284).sum := by decide
  have hdescent : baseEnd_880284 < baseStart_880284 := by decide
  rcases family_descends (prefixWord ++ tailWord_880284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880288 : List Nat := [2, 1, 1, 4, 3, 1, 4, 2, 2]
def baseStart_880288 : Nat := 118140960795 + 880288 * 2 ^ 59
def prefixEnd_880288 : Nat := 4983230072969 + 3 ^ 40 * 880288 * 2
def baseEnd_880288 : Nat := 401787429675695202534787

theorem tailTrace_880288 : CollatzResearch.WordTrace tailWord_880288 prefixEnd_880288 401787429675695202534787 := by
  unfold tailWord_880288
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053370517437196033116759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21404494023249594710822345 16053370517437196033116759)
  ·
    refine ⟨24080055776155794049675139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16053370517437196033116759 24080055776155794049675139)
    ·
      refine ⟨36120083664233691074512709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24080055776155794049675139 36120083664233691074512709)
      ·
        refine ⟨6772515687043817076471133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36120083664233691074512709 6772515687043817076471133)
        ·
          refine ⟨2539693382641431403676675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6772515687043817076471133 2539693382641431403676675)
          ·
            refine ⟨3809540073962147105515013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539693382641431403676675 3809540073962147105515013)
            ·
              refine ⟨714288763867902582284065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3809540073962147105515013 714288763867902582284065)
              ·
                refine ⟨535716572900926936713049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714288763867902582284065 535716572900926936713049)
                ·
                  refine ⟨401787429675695202534787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535716572900926936713049 401787429675695202534787)
                  ·
                    rfl

theorem cell20_880288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 4, 2, 2].length) (baseStart_880288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880288 prefixEnd_880288 := by exact prefixLift 880288
  have htrace : WordTrace (prefixWord ++ tailWord_880288) baseStart_880288 baseEnd_880288 := by
    simpa [prefixWord, tailWord_880288, baseEnd_880288] using wordTrace_append hprefix tailTrace_880288
  have hstable : (prefixWord ++ tailWord_880288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880288).length < 2 ^ (prefixWord ++ tailWord_880288).sum := by decide
  have hdescent : baseEnd_880288 < baseStart_880288 := by decide
  rcases family_descends (prefixWord ++ tailWord_880288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880309 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 4]
def baseStart_880309 : Nat := 118140960795 + 880309 * 2 ^ 59
def prefixEnd_880309 : Nat := 4983230072969 + 3 ^ 40 * 880309 * 2
def baseEnd_880309 : Nat := 401797014647912462834701

theorem tailTrace_880309 : CollatzResearch.WordTrace tailWord_880309 prefixEnd_880309 401797014647912462834701 := by
  unfold tailWord_880309
  simp only [CollatzResearch.WordTrace]
  refine ⟨32107506967798312652747981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21405004645198875101831987 32107506967798312652747981)
  ·
    refine ⟨12040315112924367244780493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32107506967798312652747981 12040315112924367244780493)
    ·
      refine ⟨4515118167346637716792685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12040315112924367244780493 4515118167346637716792685)
      ·
        refine ⟨1693169312754989143797257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4515118167346637716792685 1693169312754989143797257)
        ·
          refine ⟨1269876984566241857847943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1693169312754989143797257 1269876984566241857847943)
          ·
            refine ⟨1904815476849362786771915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1269876984566241857847943 1904815476849362786771915)
            ·
              refine ⟨2857223215274044180157873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1904815476849362786771915 2857223215274044180157873)
              ·
                refine ⟨2142917411455533135118405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2857223215274044180157873 2142917411455533135118405)
                ·
                  refine ⟨401797014647912462834701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2142917411455533135118405 401797014647912462834701)
                  ·
                    rfl

theorem cell20_880309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_880309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880309 prefixEnd_880309 := by exact prefixLift 880309
  have htrace : WordTrace (prefixWord ++ tailWord_880309) baseStart_880309 baseEnd_880309 := by
    simpa [prefixWord, tailWord_880309, baseEnd_880309] using wordTrace_append hprefix tailTrace_880309
  have hstable : (prefixWord ++ tailWord_880309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880309).length < 2 ^ (prefixWord ++ tailWord_880309).sum := by decide
  have hdescent : baseEnd_880309 < baseStart_880309 := by decide
  rcases family_descends (prefixWord ++ tailWord_880309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880313 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_880313 : Nat := 118140960795 + 880313 * 2 ^ 59
def prefixEnd_880313 : Nat := 4983230072969 + 3 ^ 40 * 880313 * 2
def baseEnd_880313 : Nat := 401798840356906226701351

theorem tailTrace_880313 : CollatzResearch.WordTrace tailWord_880313 prefixEnd_880313 401798840356906226701351 := by
  unfold tailWord_880313
  simp only [CollatzResearch.WordTrace]
  refine ⟨32107652859783821335893593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21405101906522547557262395 32107652859783821335893593)
  ·
    refine ⟨24080739644837866001920195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32107652859783821335893593 24080739644837866001920195)
    ·
      refine ⟨36121109467256799002880293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24080739644837866001920195 36121109467256799002880293)
      ·
        refine ⟨6772708025110649813040055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36121109467256799002880293 6772708025110649813040055)
        ·
          refine ⟨10159062037665974719560083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6772708025110649813040055 10159062037665974719560083)
          ·
            refine ⟨15238593056498962079340125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159062037665974719560083 15238593056498962079340125)
            ·
              refine ⟨5714472396187110779752547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15238593056498962079340125 5714472396187110779752547)
              ·
                refine ⟨8571708594280666169628821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5714472396187110779752547 8571708594280666169628821)
                ·
                  refine ⟨401798840356906226701351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8571708594280666169628821 401798840356906226701351)
                  ·
                    rfl

theorem cell20_880313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_880313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880313 prefixEnd_880313 := by exact prefixLift 880313
  have htrace : WordTrace (prefixWord ++ tailWord_880313) baseStart_880313 baseEnd_880313 := by
    simpa [prefixWord, tailWord_880313, baseEnd_880313] using wordTrace_append hprefix tailTrace_880313
  have hstable : (prefixWord ++ tailWord_880313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880313).length < 2 ^ (prefixWord ++ tailWord_880313).sum := by decide
  have hdescent : baseEnd_880313 < baseStart_880313 := by decide
  rcases family_descends (prefixWord ++ tailWord_880313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880316 : List Nat := [2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_880316 : Nat := 118140960795 + 880316 * 2 ^ 59
def prefixEnd_880316 : Nat := 4983230072969 + 3 ^ 40 * 880316 * 2
def baseEnd_880316 : Nat := 133933403212883849867113

theorem tailTrace_880316 : CollatzResearch.WordTrace tailWord_880316 prefixEnd_880316 133933403212883849867113 := by
  unfold tailWord_880316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16053881139386476424126401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21405174852515301898835201 16053881139386476424126401)
  ·
    refine ⟨12040410854539857318094801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16053881139386476424126401 12040410854539857318094801)
    ·
      refine ⟨9030308140904892988571101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12040410854539857318094801 9030308140904892988571101)
      ·
        refine ⟨3386365552839334870714163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9030308140904892988571101 3386365552839334870714163)
        ·
          refine ⟨5079548329259002306071245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3386365552839334870714163 5079548329259002306071245)
          ·
            refine ⟨1904830623472125864776717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5079548329259002306071245 1904830623472125864776717)
            ·
              refine ⟨714311483802047199291269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1904830623472125864776717 714311483802047199291269)
              ·
                refine ⟨133933403212883849867113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714311483802047199291269 133933403212883849867113)
                ·
                  rfl

theorem cell20_880316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_880316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880316 prefixEnd_880316 := by exact prefixLift 880316
  have htrace : WordTrace (prefixWord ++ tailWord_880316) baseStart_880316 baseEnd_880316 := by
    simpa [prefixWord, tailWord_880316, baseEnd_880316] using wordTrace_append hprefix tailTrace_880316
  have hstable : (prefixWord ++ tailWord_880316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880316).length < 2 ^ (prefixWord ++ tailWord_880316).sum := by decide
  have hdescent : baseEnd_880316 < baseStart_880316 := by decide
  rcases family_descends (prefixWord ++ tailWord_880316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880340 : List Nat := [2, 4, 1, 3, 1, 1, 3, 2, 3]
def baseStart_880340 : Nat := 118140960795 + 880340 * 2 ^ 59
def prefixEnd_880340 : Nat := 4983230072969 + 3 ^ 40 * 880340 * 2
def baseEnd_880340 : Nat := 401811163892614132801241

theorem tailTrace_880340 : CollatzResearch.WordTrace tailWord_880340 prefixEnd_880340 401811163892614132801241 := by
  unfold tailWord_880340
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054318815343002473563237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21405758420457336631417649 16054318815343002473563237)
  ·
    refine ⟨3010184777876812963793107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16054318815343002473563237 3010184777876812963793107)
    ·
      refine ⟨4515277166815219445689661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010184777876812963793107 4515277166815219445689661)
      ·
        refine ⟨1693228937555707292133623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4515277166815219445689661 1693228937555707292133623)
        ·
          refine ⟨2539843406333560938200435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693228937555707292133623 2539843406333560938200435)
          ·
            refine ⟨3809765109500341407300653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2539843406333560938200435 3809765109500341407300653)
            ·
              refine ⟨1428661916062628027737745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3809765109500341407300653 1428661916062628027737745)
              ·
                refine ⟨1071496437046971020803309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1428661916062628027737745 1071496437046971020803309)
                ·
                  refine ⟨401811163892614132801241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071496437046971020803309 401811163892614132801241)
                  ·
                    rfl

theorem cell20_880340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_880340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880340 prefixEnd_880340 := by exact prefixLift 880340
  have htrace : WordTrace (prefixWord ++ tailWord_880340) baseStart_880340 baseEnd_880340 := by
    simpa [prefixWord, tailWord_880340, baseEnd_880340] using wordTrace_append hprefix tailTrace_880340
  have hstable : (prefixWord ++ tailWord_880340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880340).length < 2 ^ (prefixWord ++ tailWord_880340).sum := by decide
  have hdescent : baseEnd_880340 < baseStart_880340 := by decide
  rcases family_descends (prefixWord ++ tailWord_880340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880344 : List Nat := [2, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_880344 : Nat := 118140960795 + 880344 * 2 ^ 59
def prefixEnd_880344 : Nat := 4983230072969 + 3 ^ 40 * 880344 * 2
def baseEnd_880344 : Nat := 401812989601607896667891

theorem tailTrace_880344 : CollatzResearch.WordTrace tailWord_880344 prefixEnd_880344 401812989601607896667891 := by
  unfold tailWord_880344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16054391761335756815136043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21405855681781009086848057 16054391761335756815136043)
  ·
    refine ⟨24081587642003635222704065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16054391761335756815136043 24081587642003635222704065)
    ·
      refine ⟨18061190731502726417028049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24081587642003635222704065 18061190731502726417028049)
      ·
        refine ⟨13545893048627044812771037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18061190731502726417028049 13545893048627044812771037)
        ·
          refine ⟨5079709893235141804789139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13545893048627044812771037 5079709893235141804789139)
          ·
            refine ⟨7619564839852712707183709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5079709893235141804789139 7619564839852712707183709)
            ·
              refine ⟨2857336814944767265193891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7619564839852712707183709 2857336814944767265193891)
              ·
                refine ⟨4286005222417150897790837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2857336814944767265193891 4286005222417150897790837)
                ·
                  refine ⟨401812989601607896667891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4286005222417150897790837 401812989601607896667891)
                  ·
                    rfl

theorem cell20_880344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_880344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880344 prefixEnd_880344 := by exact prefixLift 880344
  have htrace : WordTrace (prefixWord ++ tailWord_880344) baseStart_880344 baseEnd_880344 := by
    simpa [prefixWord, tailWord_880344, baseEnd_880344] using wordTrace_append hprefix tailTrace_880344
  have hstable : (prefixWord ++ tailWord_880344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880344).length < 2 ^ (prefixWord ++ tailWord_880344).sum := by decide
  have hdescent : baseEnd_880344 < baseStart_880344 := by decide
  rcases family_descends (prefixWord ++ tailWord_880344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880375 : List Nat := [1, 1, 3, 1, 1, 1, 8, 4]
def baseStart_880375 : Nat := 118140960795 + 880375 * 2 ^ 59
def prefixEnd_880375 : Nat := 4983230072969 + 3 ^ 40 * 880375 * 2
def baseEnd_880375 : Nat := 133942379615436522211477

theorem tailTrace_880375 : CollatzResearch.WordTrace tailWord_880375 prefixEnd_880375 133942379615436522211477 := by
  unfold tailWord_880375
  simp only [CollatzResearch.WordTrace]
  refine ⟨32109914185559205924650579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21406609457039470616433719 32109914185559205924650579)
  ·
    refine ⟨48164871278338808886975869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32109914185559205924650579 48164871278338808886975869)
    ·
      refine ⟨18061826729377053332615951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48164871278338808886975869 18061826729377053332615951)
      ·
        refine ⟨27092740094065579998923927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18061826729377053332615951 27092740094065579998923927)
        ·
          refine ⟨40639110141098369998385891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27092740094065579998923927 40639110141098369998385891)
          ·
            refine ⟨60958665211647554997578837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40639110141098369998385891 60958665211647554997578837)
            ·
              refine ⟨714359357948994785127877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 60958665211647554997578837 714359357948994785127877)
              ·
                refine ⟨133942379615436522211477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714359357948994785127877 133942379615436522211477)
                ·
                  rfl

theorem cell20_880375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 4].length) (baseStart_880375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880375 prefixEnd_880375 := by exact prefixLift 880375
  have htrace : WordTrace (prefixWord ++ tailWord_880375) baseStart_880375 baseEnd_880375 := by
    simpa [prefixWord, tailWord_880375, baseEnd_880375] using wordTrace_append hprefix tailTrace_880375
  have hstable : (prefixWord ++ tailWord_880375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880375).length < 2 ^ (prefixWord ++ tailWord_880375).sum := by decide
  have hdescent : baseEnd_880375 < baseStart_880375 := by decide
  rcases family_descends (prefixWord ++ tailWord_880375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880385 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 2]
def baseStart_880385 : Nat := 118140960795 + 880385 * 2 ^ 59
def prefixEnd_880385 : Nat := 4983230072969 + 3 ^ 40 * 880385 * 2
def baseEnd_880385 : Nat := 401831703118793976301057

theorem tailTrace_880385 : CollatzResearch.WordTrace tailWord_880385 prefixEnd_880385 401831703118793976301057 := by
  unfold tailWord_880385
  simp only [CollatzResearch.WordTrace]
  refine ⟨32110278915522977632514609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21406852610348651755009739 32110278915522977632514609)
  ·
    refine ⟨24082709186642233224385957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32110278915522977632514609 24082709186642233224385957)
    ·
      refine ⟨4515507972495418729572367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24082709186642233224385957 4515507972495418729572367)
      ·
        refine ⟨6773261958743128094358551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515507972495418729572367 6773261958743128094358551)
        ·
          refine ⟨10159892938114692141537827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6773261958743128094358551 10159892938114692141537827)
          ·
            refine ⟨15239839407172038212306741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10159892938114692141537827 15239839407172038212306741)
            ·
              refine ⟨1428734944422378582403757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15239839407172038212306741 1428734944422378582403757)
              ·
                refine ⟨535775604158391968401409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1428734944422378582403757 535775604158391968401409)
                ·
                  refine ⟨401831703118793976301057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535775604158391968401409 401831703118793976301057)
                  ·
                    rfl

theorem cell20_880385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2].length) (baseStart_880385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880385 prefixEnd_880385 := by exact prefixLift 880385
  have htrace : WordTrace (prefixWord ++ tailWord_880385) baseStart_880385 baseEnd_880385 := by
    simpa [prefixWord, tailWord_880385, baseEnd_880385] using wordTrace_append hprefix tailTrace_880385
  have hstable : (prefixWord ++ tailWord_880385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880385).length < 2 ^ (prefixWord ++ tailWord_880385).sum := by decide
  have hdescent : baseEnd_880385 < baseStart_880385 := by decide
  rcases family_descends (prefixWord ++ tailWord_880385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880396 : List Nat := [2, 2, 1, 2, 2, 1, 10]
def baseStart_880396 : Nat := 118140960795 + 880396 * 2 ^ 59
def prefixEnd_880396 : Nat := 4983230072969 + 3 ^ 40 * 880396 * 2
def baseEnd_880396 : Nat := 44648524868725202992705

theorem tailTrace_880396 : CollatzResearch.WordTrace tailWord_880396 prefixEnd_880396 44648524868725202992705 := by
  unfold tailWord_880396
  simp only [CollatzResearch.WordTrace]
  refine ⟨16055340059241563255582521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21407120078988751007443361 16055340059241563255582521)
  ·
    refine ⟨12041505044431172441686891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16055340059241563255582521 12041505044431172441686891)
    ·
      refine ⟨18062257566646758662530337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12041505044431172441686891 18062257566646758662530337)
      ·
        refine ⟨13546693174985068996897753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18062257566646758662530337 13546693174985068996897753)
        ·
          refine ⟨10160019881238801747673315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13546693174985068996897753 10160019881238801747673315)
          ·
            refine ⟨15240029821858202621509973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10160019881238801747673315 15240029821858202621509973)
            ·
              refine ⟨44648524868725202992705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15240029821858202621509973 44648524868725202992705)
              ·
                rfl

theorem cell20_880396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 10].length) (baseStart_880396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880396 prefixEnd_880396 := by exact prefixLift 880396
  have htrace : WordTrace (prefixWord ++ tailWord_880396) baseStart_880396 baseEnd_880396 := by
    simpa [prefixWord, tailWord_880396, baseEnd_880396] using wordTrace_append hprefix tailTrace_880396
  have hstable : (prefixWord ++ tailWord_880396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880396).length < 2 ^ (prefixWord ++ tailWord_880396).sum := by decide
  have hdescent : baseEnd_880396 < baseStart_880396 := by decide
  rcases family_descends (prefixWord ++ tailWord_880396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880402 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 4]
def baseStart_880402 : Nat := 118140960795 + 880402 * 2 ^ 59
def prefixEnd_880402 : Nat := 4983230072969 + 3 ^ 40 * 880402 * 2
def baseEnd_880402 : Nat := 401839462382017472734321

theorem tailTrace_880402 : CollatzResearch.WordTrace tailWord_880402 prefixEnd_880402 401839462382017472734321 := by
  unfold tailWord_880402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8027724739115347383970865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21407265970974259690588973 8027724739115347383970865)
  ·
    refine ⟨6020793554336510537978149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8027724739115347383970865 6020793554336510537978149)
    ·
      refine ⟨1128898791438095725870903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6020793554336510537978149 1128898791438095725870903)
      ·
        refine ⟨1693348187157143588806355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1128898791438095725870903 1693348187157143588806355)
        ·
          refine ⟨2540022280735715383209533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1693348187157143588806355 2540022280735715383209533)
          ·
            refine ⟨952508355275893268703575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540022280735715383209533 952508355275893268703575)
            ·
              refine ⟨1428762532913839903055363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952508355275893268703575 1428762532913839903055363)
              ·
                refine ⟨2143143799370759854583045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1428762532913839903055363 2143143799370759854583045)
                ·
                  refine ⟨401839462382017472734321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143143799370759854583045 401839462382017472734321)
                  ·
                    rfl

theorem cell20_880402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_880402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880402 prefixEnd_880402 := by exact prefixLift 880402
  have htrace : WordTrace (prefixWord ++ tailWord_880402) baseStart_880402 baseEnd_880402 := by
    simpa [prefixWord, tailWord_880402, baseEnd_880402] using wordTrace_append hprefix tailTrace_880402
  have hstable : (prefixWord ++ tailWord_880402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880402).length < 2 ^ (prefixWord ++ tailWord_880402).sum := by decide
  have hdescent : baseEnd_880402 < baseStart_880402 := by decide
  rcases family_descends (prefixWord ++ tailWord_880402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880468 : List Nat := [2, 4, 1, 1, 3, 3, 1, 5]
def baseStart_880468 : Nat := 118140960795 + 880468 * 2 ^ 59
def prefixEnd_880468 : Nat := 4983230072969 + 3 ^ 40 * 880468 * 2
def baseEnd_880468 : Nat := 133956528860138192178017

theorem tailTrace_880468 : CollatzResearch.WordTrace tailWord_880468 prefixEnd_880468 133956528860138192178017 := by
  unfold tailWord_880468
  simp only [CollatzResearch.WordTrace]
  refine ⟨16056653087111141403893029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21408870782814855205190705 16056653087111141403893029)
  ·
    refine ⟨3010622453833339013229943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16056653087111141403893029 3010622453833339013229943)
    ·
      refine ⟨4515933680750008519844915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3010622453833339013229943 4515933680750008519844915)
      ·
        refine ⟨6773900521125012779767373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4515933680750008519844915 6773900521125012779767373)
        ·
          refine ⟨2540212695421879792412765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6773900521125012779767373 2540212695421879792412765)
          ·
            refine ⟨952579760783204922154787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540212695421879792412765 952579760783204922154787)
            ·
              refine ⟨1428869641174807383232181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952579760783204922154787 1428869641174807383232181)
              ·
                refine ⟨133956528860138192178017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1428869641174807383232181 133956528860138192178017)
                ·
                  rfl

theorem cell20_880468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 5].length) (baseStart_880468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880468 prefixEnd_880468 := by exact prefixLift 880468
  have htrace : WordTrace (prefixWord ++ tailWord_880468) baseStart_880468 baseEnd_880468 := by
    simpa [prefixWord, tailWord_880468, baseEnd_880468] using wordTrace_append hprefix tailTrace_880468
  have hstable : (prefixWord ++ tailWord_880468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880468).length < 2 ^ (prefixWord ++ tailWord_880468).sum := by decide
  have hdescent : baseEnd_880468 < baseStart_880468 := by decide
  rcases family_descends (prefixWord ++ tailWord_880468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880482 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 6]
def baseStart_880482 : Nat := 118140960795 + 880482 * 2 ^ 59
def prefixEnd_880482 : Nat := 4983230072969 + 3 ^ 40 * 880482 * 2
def baseEnd_880482 : Nat := 401875976561892750067327

theorem tailTrace_880482 : CollatzResearch.WordTrace tailWord_880482 prefixEnd_880482 401875976561892750067327 := by
  unfold tailWord_880482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028454199042890799698925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21409211197447708799197133 8028454199042890799698925)
  ·
    refine ⟨3010670324641084049887097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8028454199042890799698925 3010670324641084049887097)
    ·
      refine ⟨2258002743480813037415323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3010670324641084049887097 2258002743480813037415323)
      ·
        refine ⟨3387004115221219556122985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258002743480813037415323 3387004115221219556122985)
        ·
          refine ⟨2540253086415914667092239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3387004115221219556122985 2540253086415914667092239)
          ·
            refine ⟨3810379629623872000638359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2540253086415914667092239 3810379629623872000638359)
            ·
              refine ⟨5715569444435808000957539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3810379629623872000638359 5715569444435808000957539)
              ·
                refine ⟨8573354166653712001436309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5715569444435808000957539 8573354166653712001436309)
                ·
                  refine ⟨401875976561892750067327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8573354166653712001436309 401875976561892750067327)
                  ·
                    rfl

theorem cell20_880482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_880482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880482 prefixEnd_880482 := by exact prefixLift 880482
  have htrace : WordTrace (prefixWord ++ tailWord_880482) baseStart_880482 baseEnd_880482 := by
    simpa [prefixWord, tailWord_880482, baseEnd_880482] using wordTrace_append hprefix tailTrace_880482
  have hstable : (prefixWord ++ tailWord_880482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880482).length < 2 ^ (prefixWord ++ tailWord_880482).sum := by decide
  have hdescent : baseEnd_880482 < baseStart_880482 := by decide
  rcases family_descends (prefixWord ++ tailWord_880482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880565 : List Nat := [1, 3, 3, 2, 1, 4, 6]
def baseStart_880565 : Nat := 118140960795 + 880565 * 2 ^ 59
def prefixEnd_880565 : Nat := 4983230072969 + 3 ^ 40 * 880565 * 2
def baseEnd_880565 : Nat := 44657095558168150033369

theorem tailTrace_880565 : CollatzResearch.WordTrace tailWord_880565 prefixEnd_880565 44657095558168150033369 := by
  unfold tailWord_880565
  simp only [CollatzResearch.WordTrace]
  refine ⟨32116844054870868374067149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411229369913912249378099 32116844054870868374067149)
  ·
    refine ⟨12043816520576575640275181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32116844054870868374067149 12043816520576575640275181)
    ·
      refine ⟨4516431195216215865103193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12043816520576575640275181 4516431195216215865103193)
      ·
        refine ⟨3387323396412161898827395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4516431195216215865103193 3387323396412161898827395)
        ·
          refine ⟨5080985094618242848241093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387323396412161898827395 5080985094618242848241093)
          ·
            refine ⟨952684705240920534045205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5080985094618242848241093 952684705240920534045205)
            ·
              refine ⟨44657095558168150033369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 952684705240920534045205 44657095558168150033369)
              ·
                rfl

theorem cell20_880565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 6].length) (baseStart_880565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880565 prefixEnd_880565 := by exact prefixLift 880565
  have htrace : WordTrace (prefixWord ++ tailWord_880565) baseStart_880565 baseEnd_880565 := by
    simpa [prefixWord, tailWord_880565, baseEnd_880565] using wordTrace_append hprefix tailTrace_880565
  have hstable : (prefixWord ++ tailWord_880565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880565).length < 2 ^ (prefixWord ++ tailWord_880565).sum := by decide
  have hdescent : baseEnd_880565 < baseStart_880565 := by decide
  rcases family_descends (prefixWord ++ tailWord_880565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880575 : List Nat := [1, 1, 2, 2, 2, 1, 7, 2, 2]
def baseStart_880575 : Nat := 118140960795 + 880575 * 2 ^ 59
def prefixEnd_880575 : Nat := 4983230072969 + 3 ^ 40 * 880575 * 2
def baseEnd_880575 : Nat := 401918424295997759966947

theorem tailTrace_880575 : CollatzResearch.WordTrace tailWord_880575 prefixEnd_880575 401918424295997759966947 := by
  unfold tailWord_880575
  simp only [CollatzResearch.WordTrace]
  refine ⟨32117208784834640081931179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411472523223093387954119 32117208784834640081931179)
  ·
    refine ⟨48175813177251960122896769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32117208784834640081931179 48175813177251960122896769)
    ·
      refine ⟨36131859882938970092172577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48175813177251960122896769 36131859882938970092172577)
      ·
        refine ⟨27098894912204227569129433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36131859882938970092172577 27098894912204227569129433)
        ·
          refine ⟨20324171184153170676847075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27098894912204227569129433 20324171184153170676847075)
          ·
            refine ⟨30486256776229756015270613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324171184153170676847075 30486256776229756015270613)
            ·
              refine ⟨714521643192884906607905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 30486256776229756015270613 714521643192884906607905)
              ·
                refine ⟨535891232394663679955929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714521643192884906607905 535891232394663679955929)
                ·
                  refine ⟨401918424295997759966947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535891232394663679955929 401918424295997759966947)
                  ·
                    rfl

theorem cell20_880575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2].length) (baseStart_880575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880575 prefixEnd_880575 := by exact prefixLift 880575
  have htrace : WordTrace (prefixWord ++ tailWord_880575) baseStart_880575 baseEnd_880575 := by
    simpa [prefixWord, tailWord_880575, baseEnd_880575] using wordTrace_append hprefix tailTrace_880575
  have hstable : (prefixWord ++ tailWord_880575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880575).length < 2 ^ (prefixWord ++ tailWord_880575).sum := by decide
  have hdescent : baseEnd_880575 < baseStart_880575 := by decide
  rcases family_descends (prefixWord ++ tailWord_880575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880586 : List Nat := [3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_880586 : Nat := 118140960795 + 880586 * 2 ^ 59
def prefixEnd_880586 : Nat := 4983230072969 + 3 ^ 40 * 880586 * 2
def baseEnd_880586 : Nat := 133974481665243536866745

theorem tailTrace_880586 : CollatzResearch.WordTrace tailWord_880586 prefixEnd_880586 133974481665243536866745 := by
  unfold tailWord_880586
  simp only [CollatzResearch.WordTrace]
  refine ⟨8029402496948697240145403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21411739991863192640387741 8029402496948697240145403)
  ·
    refine ⟨12044103745423045860218105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8029402496948697240145403 12044103745423045860218105)
    ·
      refine ⟨9033077809067284395163579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12044103745423045860218105 9033077809067284395163579)
      ·
        refine ⟨13549616713600926592745369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9033077809067284395163579 13549616713600926592745369)
        ·
          refine ⟨10162212535200694944559027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13549616713600926592745369 10162212535200694944559027)
          ·
            refine ⟨15243318802801042416838541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10162212535200694944559027 15243318802801042416838541)
            ·
              refine ⟨5716244551050390906314453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15243318802801042416838541 5716244551050390906314453)
              ·
                refine ⟨133974481665243536866745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5716244551050390906314453 133974481665243536866745)
                ·
                  rfl

theorem cell20_880586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_880586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880586 prefixEnd_880586 := by exact prefixLift 880586
  have htrace : WordTrace (prefixWord ++ tailWord_880586) baseStart_880586 baseEnd_880586 := by
    simpa [prefixWord, tailWord_880586, baseEnd_880586] using wordTrace_append hprefix tailTrace_880586
  have hstable : (prefixWord ++ tailWord_880586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880586).length < 2 ^ (prefixWord ++ tailWord_880586).sum := by decide
  have hdescent : baseEnd_880586 < baseStart_880586 := by decide
  rcases family_descends (prefixWord ++ tailWord_880586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880593 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_880593 : Nat := 118140960795 + 880593 * 2 ^ 59
def prefixEnd_880593 : Nat := 4983230072969 + 3 ^ 40 * 880593 * 2
def baseEnd_880593 : Nat := 401926639986469697366873

theorem tailTrace_880593 : CollatzResearch.WordTrace tailWord_880593 prefixEnd_880593 401926639986469697366873 := by
  unfold tailWord_880593
  simp only [CollatzResearch.WordTrace]
  refine ⟨32117865298769429156086433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21411910199179619437390955 32117865298769429156086433)
  ·
    refine ⟨24088398974077071867064825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32117865298769429156086433 24088398974077071867064825)
    ·
      refine ⟨18066299230557803900298619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24088398974077071867064825 18066299230557803900298619)
      ·
        refine ⟨27099448845836705850447929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18066299230557803900298619 27099448845836705850447929)
        ·
          refine ⟨20324586634377529387835947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27099448845836705850447929 20324586634377529387835947)
          ·
            refine ⟨30486879951566294081753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20324586634377529387835947 30486879951566294081753921)
            ·
              refine ⟨22865159963674720561315441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30486879951566294081753921 22865159963674720561315441)
              ·
                refine ⟨17148869972756040420986581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22865159963674720561315441 17148869972756040420986581)
                ·
                  refine ⟨401926639986469697366873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17148869972756040420986581 401926639986469697366873)
                  ·
                    rfl

theorem cell20_880593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_880593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880593 prefixEnd_880593 := by exact prefixLift 880593
  have htrace : WordTrace (prefixWord ++ tailWord_880593) baseStart_880593 baseEnd_880593 := by
    simpa [prefixWord, tailWord_880593, baseEnd_880593] using wordTrace_append hprefix tailTrace_880593
  have hstable : (prefixWord ++ tailWord_880593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880593).length < 2 ^ (prefixWord ++ tailWord_880593).sum := by decide
  have hdescent : baseEnd_880593 < baseStart_880593 := by decide
  rcases family_descends (prefixWord ++ tailWord_880593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880630 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_880630 : Nat := 118140960795 + 880630 * 2 ^ 59
def prefixEnd_880630 : Nat := 4983230072969 + 3 ^ 40 * 880630 * 2
def baseEnd_880630 : Nat := 401943527794662013133389

theorem tailTrace_880630 : CollatzResearch.WordTrace tailWord_880630 prefixEnd_880630 401943527794662013133389 := by
  unfold tailWord_880630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007450924977211529698959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21412809866423589650122229 2007450924977211529698959)
  ·
    refine ⟨3011176387465817294548439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007450924977211529698959 3011176387465817294548439)
    ·
      refine ⟨4516764581198725941822659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011176387465817294548439 4516764581198725941822659)
      ·
        refine ⟨6775146871798088912733989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4516764581198725941822659 6775146871798088912733989)
        ·
          refine ⟨1270340038462141671137623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6775146871798088912733989 1270340038462141671137623)
          ·
            refine ⟨1905510057693212506706435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270340038462141671137623 1905510057693212506706435)
            ·
              refine ⟨2858265086539818760059653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1905510057693212506706435 2858265086539818760059653)
              ·
                refine ⟨535924703726216017511185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2858265086539818760059653 535924703726216017511185)
                ·
                  refine ⟨401943527794662013133389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 535924703726216017511185 401943527794662013133389)
                  ·
                    rfl

theorem cell20_880630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_880630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880630 prefixEnd_880630 := by exact prefixLift 880630
  have htrace : WordTrace (prefixWord ++ tailWord_880630) baseStart_880630 baseEnd_880630 := by
    simpa [prefixWord, tailWord_880630, baseEnd_880630] using wordTrace_append hprefix tailTrace_880630
  have hstable : (prefixWord ++ tailWord_880630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880630).length < 2 ^ (prefixWord ++ tailWord_880630).sum := by decide
  have hdescent : baseEnd_880630 < baseStart_880630 := by decide
  rcases family_descends (prefixWord ++ tailWord_880630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880648 : List Nat := [2, 1, 3, 2, 1, 2, 1, 5, 3]
def baseStart_880648 : Nat := 118140960795 + 880648 * 2 ^ 59
def prefixEnd_880648 : Nat := 4983230072969 + 3 ^ 40 * 880648 * 2
def baseEnd_880648 : Nat := 401951743485133950533315

theorem tailTrace_880648 : CollatzResearch.WordTrace tailWord_880648 prefixEnd_880648 401951743485133950533315 := by
  unfold tailWord_880648
  simp only [CollatzResearch.WordTrace]
  refine ⟨16059935656785086774669299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21413247542380115699559065 16059935656785086774669299)
  ·
    refine ⟨24089903485177630162003949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16059935656785086774669299 24089903485177630162003949)
    ·
      refine ⟨9033713806941611310751481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24089903485177630162003949 9033713806941611310751481)
      ·
        refine ⟨6775285355206208483063611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9033713806941611310751481 6775285355206208483063611)
        ·
          refine ⟨10162928032809312724595417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6775285355206208483063611 10162928032809312724595417)
          ·
            refine ⟨7622196024606984543446563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10162928032809312724595417 7622196024606984543446563)
            ·
              refine ⟨11433294036910476815169845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7622196024606984543446563 11433294036910476815169845)
              ·
                refine ⟨1071871315960357201422173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11433294036910476815169845 1071871315960357201422173)
                ·
                  refine ⟨401951743485133950533315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071871315960357201422173 401951743485133950533315)
                  ·
                    rfl

theorem cell20_880648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 5, 3].length) (baseStart_880648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880648 prefixEnd_880648 := by exact prefixLift 880648
  have htrace : WordTrace (prefixWord ++ tailWord_880648) baseStart_880648 baseEnd_880648 := by
    simpa [prefixWord, tailWord_880648, baseEnd_880648] using wordTrace_append hprefix tailTrace_880648
  have hstable : (prefixWord ++ tailWord_880648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880648).length < 2 ^ (prefixWord ++ tailWord_880648).sum := by decide
  have hdescent : baseEnd_880648 < baseStart_880648 := by decide
  rcases family_descends (prefixWord ++ tailWord_880648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880682 : List Nat := [3, 1, 4, 1, 2, 3, 1, 2, 3]
def baseStart_880682 : Nat := 118140960795 + 880682 * 2 ^ 59
def prefixEnd_880682 : Nat := 4983230072969 + 3 ^ 40 * 880682 * 2
def baseEnd_880682 : Nat := 401967262011580943399843

theorem tailTrace_880682 : CollatzResearch.WordTrace tailWord_880682 prefixEnd_880682 401967262011580943399843 := by
  unfold tailWord_880682
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030277848861749339019075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21414074263631331570717533 8030277848861749339019075)
  ·
    refine ⟨12045416773292624008528613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8030277848861749339019075 12045416773292624008528613)
    ·
      refine ⟨2258515644992367001599115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12045416773292624008528613 2258515644992367001599115)
      ·
        refine ⟨3387773467488550502398673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258515644992367001599115 3387773467488550502398673)
        ·
          refine ⟨2540830100616412876799005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3387773467488550502398673 2540830100616412876799005)
          ·
            refine ⟨952811287731154828799627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2540830100616412876799005 952811287731154828799627)
            ·
              refine ⟨1429216931596732243199441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952811287731154828799627 1429216931596732243199441)
              ·
                refine ⟨1071912698697549182399581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1429216931596732243199441 1071912698697549182399581)
                ·
                  refine ⟨401967262011580943399843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1071912698697549182399581 401967262011580943399843)
                  ·
                    rfl

theorem cell20_880682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_880682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880682 prefixEnd_880682 := by exact prefixLift 880682
  have htrace : WordTrace (prefixWord ++ tailWord_880682) baseStart_880682 baseEnd_880682 := by
    simpa [prefixWord, tailWord_880682, baseEnd_880682] using wordTrace_append hprefix tailTrace_880682
  have hstable : (prefixWord ++ tailWord_880682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880682).length < 2 ^ (prefixWord ++ tailWord_880682).sum := by decide
  have hdescent : baseEnd_880682 < baseStart_880682 := by decide
  rcases family_descends (prefixWord ++ tailWord_880682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880693 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 4]
def baseStart_880693 : Nat := 118140960795 + 880693 * 2 ^ 59
def prefixEnd_880693 : Nat := 4983230072969 + 3 ^ 40 * 880693 * 2
def baseEnd_880693 : Nat := 401972282711313794033131

theorem tailTrace_880693 : CollatzResearch.WordTrace tailWord_880693 prefixEnd_880693 401972282711313794033131 := by
  unfold tailWord_880693
  simp only [CollatzResearch.WordTrace]
  refine ⟨32121512598407146234726733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21414341732271430823151155 32121512598407146234726733)
  ·
    refine ⟨12045567224402679838022525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32121512598407146234726733 12045567224402679838022525)
    ·
      refine ⟨4517087709151004939258447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12045567224402679838022525 4517087709151004939258447)
      ·
        refine ⟨6775631563726507408887671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4517087709151004939258447 6775631563726507408887671)
        ·
          refine ⟨10163447345589761113331507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6775631563726507408887671 10163447345589761113331507)
          ·
            refine ⟨15245171018384641669997261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10163447345589761113331507 15245171018384641669997261)
            ·
              refine ⟨5716939131894240626248973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15245171018384641669997261 5716939131894240626248973)
              ·
                refine ⟨2143852174460340234843365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5716939131894240626248973 2143852174460340234843365)
                ·
                  refine ⟨401972282711313794033131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143852174460340234843365 401972282711313794033131)
                  ·
                    rfl

theorem cell20_880693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_880693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880693 prefixEnd_880693 := by exact prefixLift 880693
  have htrace : WordTrace (prefixWord ++ tailWord_880693) baseStart_880693 baseEnd_880693 := by
    simpa [prefixWord, tailWord_880693, baseEnd_880693] using wordTrace_append hprefix tailTrace_880693
  have hstable : (prefixWord ++ tailWord_880693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880693).length < 2 ^ (prefixWord ++ tailWord_880693).sum := by decide
  have hdescent : baseEnd_880693 < baseStart_880693 := by decide
  rcases family_descends (prefixWord ++ tailWord_880693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880700 : List Nat := [2, 2, 2, 2, 2, 1, 2, 7]
def baseStart_880700 : Nat := 118140960795 + 880700 * 2 ^ 59
def prefixEnd_880700 : Nat := 4983230072969 + 3 ^ 40 * 880700 * 2
def baseEnd_880700 : Nat := 133991825900684293599923

theorem tailTrace_880700 : CollatzResearch.WordTrace tailWord_880700 prefixEnd_880700 133991825900684293599923 := by
  unfold tailWord_880700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16060883954690893215115777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21414511939587857620154369 16060883954690893215115777)
  ·
    refine ⟨12045662966018169911336833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16060883954690893215115777 12045662966018169911336833)
    ·
      refine ⟨9034247224513627433502625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12045662966018169911336833 9034247224513627433502625)
      ·
        refine ⟨6775685418385220575126969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9034247224513627433502625 6775685418385220575126969)
        ·
          refine ⟨5081764063788915431345227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6775685418385220575126969 5081764063788915431345227)
          ·
            refine ⟨7622646095683373147017841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081764063788915431345227 7622646095683373147017841)
            ·
              refine ⟨5716984571762529860263381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7622646095683373147017841 5716984571762529860263381)
              ·
                refine ⟨133991825900684293599923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5716984571762529860263381 133991825900684293599923)
                ·
                  rfl

theorem cell20_880700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_880700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880700 prefixEnd_880700 := by exact prefixLift 880700
  have htrace : WordTrace (prefixWord ++ tailWord_880700) baseStart_880700 baseEnd_880700 := by
    simpa [prefixWord, tailWord_880700, baseEnd_880700] using wordTrace_append hprefix tailTrace_880700
  have hstable : (prefixWord ++ tailWord_880700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880700).length < 2 ^ (prefixWord ++ tailWord_880700).sum := by decide
  have hdescent : baseEnd_880700 < baseStart_880700 := by decide
  rcases family_descends (prefixWord ++ tailWord_880700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880717 : List Nat := [1, 6, 1, 1, 1, 1, 3, 6]
def baseStart_880717 : Nat := 118140960795 + 880717 * 2 ^ 59
def prefixEnd_880717 : Nat := 4983230072969 + 3 ^ 40 * 880717 * 2
def baseEnd_880717 : Nat := 133994412321758792411011

theorem tailTrace_880717 : CollatzResearch.WordTrace tailWord_880717 prefixEnd_880717 133994412321758792411011 := by
  unfold tailWord_880717
  simp only [CollatzResearch.WordTrace]
  refine ⟨32122387950320198333600405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21414925300213465555733603 32122387950320198333600405)
  ·
    refine ⟨1505736935171259296887519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 32122387950320198333600405 1505736935171259296887519)
    ·
      refine ⟨2258605402756888945331279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1505736935171259296887519 2258605402756888945331279)
      ·
        refine ⟨3387908104135333417996919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2258605402756888945331279 3387908104135333417996919)
        ·
          refine ⟨5081862156203000126995379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3387908104135333417996919 5081862156203000126995379)
          ·
            refine ⟨7622793234304500190493069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5081862156203000126995379 7622793234304500190493069)
            ·
              refine ⟨2858547462864187571434901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7622793234304500190493069 2858547462864187571434901)
              ·
                refine ⟨133994412321758792411011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2858547462864187571434901 133994412321758792411011)
                ·
                  rfl

theorem cell20_880717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 6].length) (baseStart_880717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880717 prefixEnd_880717 := by exact prefixLift 880717
  have htrace : WordTrace (prefixWord ++ tailWord_880717) baseStart_880717 baseEnd_880717 := by
    simpa [prefixWord, tailWord_880717, baseEnd_880717] using wordTrace_append hprefix tailTrace_880717
  have hstable : (prefixWord ++ tailWord_880717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880717).length < 2 ^ (prefixWord ++ tailWord_880717).sum := by decide
  have hdescent : baseEnd_880717 < baseStart_880717 := by decide
  rcases family_descends (prefixWord ++ tailWord_880717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880745 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 5]
def baseStart_880745 : Nat := 118140960795 + 880745 * 2 ^ 59
def prefixEnd_880745 : Nat := 4983230072969 + 3 ^ 40 * 880745 * 2
def baseEnd_880745 : Nat := 401996016928232724299585

theorem tailTrace_880745 : CollatzResearch.WordTrace tailWord_880745 prefixEnd_880745 401996016928232724299585 := by
  unfold tailWord_880745
  simp only [CollatzResearch.WordTrace]
  refine ⟨32123409194218759115619689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21415606129479172743746459 32123409194218759115619689)
  ·
    refine ⟨24092556895664069336714767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32123409194218759115619689 24092556895664069336714767)
    ·
      refine ⟨36138835343496104005072151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24092556895664069336714767 36138835343496104005072151)
      ·
        refine ⟨54208253015244156007608227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36138835343496104005072151 54208253015244156007608227)
        ·
          refine ⟨81312379522866234011412341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54208253015244156007608227 81312379522866234011412341)
          ·
            refine ⟨7623035580268709438569907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 81312379522866234011412341 7623035580268709438569907)
            ·
              refine ⟨11434553370403064157854861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7623035580268709438569907 11434553370403064157854861)
              ·
                refine ⟨4287957513901149059195573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11434553370403064157854861 4287957513901149059195573)
                ·
                  refine ⟨401996016928232724299585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4287957513901149059195573 401996016928232724299585)
                  ·
                    rfl

theorem cell20_880745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_880745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880745 prefixEnd_880745 := by exact prefixLift 880745
  have htrace : WordTrace (prefixWord ++ tailWord_880745) baseStart_880745 baseEnd_880745 := by
    simpa [prefixWord, tailWord_880745, baseEnd_880745] using wordTrace_append hprefix tailTrace_880745
  have hstable : (prefixWord ++ tailWord_880745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880745).length < 2 ^ (prefixWord ++ tailWord_880745).sum := by decide
  have hdescent : baseEnd_880745 < baseStart_880745 := by decide
  rcases family_descends (prefixWord ++ tailWord_880745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880748 : List Nat := [2, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_880748 : Nat := 118140960795 + 880748 * 2 ^ 59
def prefixEnd_880748 : Nat := 4983230072969 + 3 ^ 40 * 880748 * 2
def baseEnd_880748 : Nat := 401997386209978047199573

theorem tailTrace_880748 : CollatzResearch.WordTrace tailWord_880748 prefixEnd_880748 401997386209978047199573 := by
  unfold tailWord_880748
  simp only [CollatzResearch.WordTrace]
  refine ⟨16061759306603945313989449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21415679075471927085319265 16061759306603945313989449)
  ·
    refine ⟨12046319479952958985492087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16061759306603945313989449 12046319479952958985492087)
    ·
      refine ⟨18069479219929438478238131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12046319479952958985492087 18069479219929438478238131)
      ·
        refine ⟨27104218829894157717357197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18069479219929438478238131 27104218829894157717357197)
        ·
          refine ⟨10164082061210309144008949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27104218829894157717357197 10164082061210309144008949)
          ·
            refine ⟨952882693238466482250839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10164082061210309144008949 952882693238466482250839)
            ·
              refine ⟨1429324039857699723376259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 952882693238466482250839 1429324039857699723376259)
              ·
                refine ⟨2143986059786549585064389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429324039857699723376259 2143986059786549585064389)
                ·
                  refine ⟨401997386209978047199573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2143986059786549585064389 401997386209978047199573)
                  ·
                    rfl

theorem cell20_880748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_880748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880748 prefixEnd_880748 := by exact prefixLift 880748
  have htrace : WordTrace (prefixWord ++ tailWord_880748) baseStart_880748 baseEnd_880748 := by
    simpa [prefixWord, tailWord_880748, baseEnd_880748] using wordTrace_append hprefix tailTrace_880748
  have hstable : (prefixWord ++ tailWord_880748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880748).length < 2 ^ (prefixWord ++ tailWord_880748).sum := by decide
  have hdescent : baseEnd_880748 < baseStart_880748 := by decide
  rcases family_descends (prefixWord ++ tailWord_880748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880758 : List Nat := [5, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_880758 : Nat := 118140960795 + 880758 * 2 ^ 59
def prefixEnd_880758 : Nat := 4983230072969 + 3 ^ 40 * 880758 * 2
def baseEnd_880758 : Nat := 402001950482462456866199

theorem tailTrace_880758 : CollatzResearch.WordTrace tailWord_880758 prefixEnd_880758 402001950482462456866199 := by
  unfold tailWord_880758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2007742708948228895990183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21415922228781108223895285 2007742708948228895990183)
  ·
    refine ⟨3011614063422343343985275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2007742708948228895990183 3011614063422343343985275)
    ·
      refine ⟨4517421095133515015977913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3011614063422343343985275 4517421095133515015977913)
      ·
        refine ⟨3388065821350136261983435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4517421095133515015977913 3388065821350136261983435)
        ·
          refine ⟨5082098732025204392975153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3388065821350136261983435 5082098732025204392975153)
          ·
            refine ⟨3811574049018903294731365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082098732025204392975153 3811574049018903294731365)
            ·
              refine ⟨714670134191044367762131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3811574049018903294731365 714670134191044367762131)
              ·
                refine ⟨1072005201286566551643197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714670134191044367762131 1072005201286566551643197)
                ·
                  refine ⟨402001950482462456866199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072005201286566551643197 402001950482462456866199)
                  ·
                    rfl

theorem cell20_880758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_880758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880758 prefixEnd_880758 := by exact prefixLift 880758
  have htrace : WordTrace (prefixWord ++ tailWord_880758) baseStart_880758 baseEnd_880758 := by
    simpa [prefixWord, tailWord_880758, baseEnd_880758] using wordTrace_append hprefix tailTrace_880758
  have hstable : (prefixWord ++ tailWord_880758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880758).length < 2 ^ (prefixWord ++ tailWord_880758).sum := by decide
  have hdescent : baseEnd_880758 < baseStart_880758 := by decide
  rcases family_descends (prefixWord ++ tailWord_880758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880800 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_880800 : Nat := 118140960795 + 880800 * 2 ^ 59
def prefixEnd_880800 : Nat := 4983230072969 + 3 ^ 40 * 880800 * 2
def baseEnd_880800 : Nat := 402021120426896977466027

theorem tailTrace_880800 : CollatzResearch.WordTrace tailWord_880800 prefixEnd_880800 402021120426896977466027 := by
  unfold tailWord_880800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16062707604509751754435927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21416943472679669005914569 16062707604509751754435927)
  ·
    refine ⟨24094061406764627631653891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16062707604509751754435927 24094061406764627631653891)
    ·
      refine ⟨36141092110146941447480837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24094061406764627631653891 36141092110146941447480837)
      ·
        refine ⟨6776454770652551521402657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36141092110146941447480837 6776454770652551521402657)
        ·
          refine ⟨5082341077989413641051993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6776454770652551521402657 5082341077989413641051993)
          ·
            refine ⟨3811755808492060230788995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5082341077989413641051993 3811755808492060230788995)
            ·
              refine ⟨5717633712738090346183493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3811755808492060230788995 5717633712738090346183493)
              ·
                refine ⟨1072056321138391939909405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5717633712738090346183493 1072056321138391939909405)
                ·
                  refine ⟨402021120426896977466027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072056321138391939909405 402021120426896977466027)
                  ·
                    rfl

theorem cell20_880800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_880800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880800 prefixEnd_880800 := by exact prefixLift 880800
  have htrace : WordTrace (prefixWord ++ tailWord_880800) baseStart_880800 baseEnd_880800 := by
    simpa [prefixWord, tailWord_880800, baseEnd_880800] using wordTrace_append hprefix tailTrace_880800
  have hstable : (prefixWord ++ tailWord_880800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880800).length < 2 ^ (prefixWord ++ tailWord_880800).sum := by decide
  have hdescent : baseEnd_880800 < baseStart_880800 := by decide
  rcases family_descends (prefixWord ++ tailWord_880800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880890 : List Nat := [3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_880890 : Nat := 118140960795 + 880890 * 2 ^ 59
def prefixEnd_880890 : Nat := 4983230072969 + 3 ^ 40 * 880890 * 2
def baseEnd_880890 : Nat := 134020732959752221488553

theorem tailTrace_880890 : CollatzResearch.WordTrace tailWord_880890 prefixEnd_880890 134020732959752221488553 := by
  unfold tailWord_880890
  simp only [CollatzResearch.WordTrace]
  refine ⟨8032174444673362219912031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21419131852462299253098749 8032174444673362219912031)
  ·
    refine ⟨12048261667010043329868047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8032174444673362219912031 12048261667010043329868047)
    ·
      refine ⟨18072392500515064994802071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12048261667010043329868047 18072392500515064994802071)
      ·
        refine ⟨27108588750772597492203107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18072392500515064994802071 27108588750772597492203107)
        ·
          refine ⟨40662883126158896238304661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27108588750772597492203107 40662883126158896238304661)
          ·
            refine ⟨1906072646538698261170531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40662883126158896238304661 1906072646538698261170531)
            ·
              refine ⟨2859108969808047391755797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906072646538698261170531 2859108969808047391755797)
              ·
                refine ⟨134020732959752221488553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2859108969808047391755797 134020732959752221488553)
                ·
                  rfl

theorem cell20_880890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_880890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880890 prefixEnd_880890 := by exact prefixLift 880890
  have htrace : WordTrace (prefixWord ++ tailWord_880890) baseStart_880890 baseEnd_880890 := by
    simpa [prefixWord, tailWord_880890, baseEnd_880890] using wordTrace_append hprefix tailTrace_880890
  have hstable : (prefixWord ++ tailWord_880890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880890).length < 2 ^ (prefixWord ++ tailWord_880890).sum := by decide
  have hdescent : baseEnd_880890 < baseStart_880890 := by decide
  rcases family_descends (prefixWord ++ tailWord_880890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880897 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 7]
def baseStart_880897 : Nat := 118140960795 + 880897 * 2 ^ 59
def prefixEnd_880897 : Nat := 4983230072969 + 3 ^ 40 * 880897 * 2
def baseEnd_880897 : Nat := 402065393869995751232297

theorem tailTrace_880897 : CollatzResearch.WordTrace tailWord_880897 prefixEnd_880897 402065393869995751232297 := by
  unfold tailWord_880897
  simp only [CollatzResearch.WordTrace]
  refine ⟨32128953089668089075152945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21419302059778726050101963 32128953089668089075152945)
  ·
    refine ⟨24096714817251066806364709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32128953089668089075152945 24096714817251066806364709)
    ·
      refine ⟨4518134028234575026193383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24096714817251066806364709 4518134028234575026193383)
      ·
        refine ⟨6777201042351862539290075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4518134028234575026193383 6777201042351862539290075)
        ·
          refine ⟨10165801563527793808935113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777201042351862539290075 10165801563527793808935113)
          ·
            refine ⟨7624351172645845356701335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10165801563527793808935113 7624351172645845356701335)
            ·
              refine ⟨11436526758968768035052003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7624351172645845356701335 11436526758968768035052003)
              ·
                refine ⟨17154790138453152052578005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11436526758968768035052003 17154790138453152052578005)
                ·
                  refine ⟨402065393869995751232297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17154790138453152052578005 402065393869995751232297)
                  ·
                    rfl

theorem cell20_880897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_880897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880897 prefixEnd_880897 := by exact prefixLift 880897
  have htrace : WordTrace (prefixWord ++ tailWord_880897) baseStart_880897 baseEnd_880897 := by
    simpa [prefixWord, tailWord_880897, baseEnd_880897] using wordTrace_append hprefix tailTrace_880897
  have hstable : (prefixWord ++ tailWord_880897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880897).length < 2 ^ (prefixWord ++ tailWord_880897).sum := by decide
  have hdescent : baseEnd_880897 < baseStart_880897 := by decide
  rcases family_descends (prefixWord ++ tailWord_880897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880928 : List Nat := [2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_880928 : Nat := 118140960795 + 880928 * 2 ^ 59
def prefixEnd_880928 : Nat := 4983230072969 + 3 ^ 40 * 880928 * 2
def baseEnd_880928 : Nat := 134026514371565807066279

theorem tailTrace_880928 : CollatzResearch.WordTrace tailWord_880928 prefixEnd_880928 134026514371565807066279 := by
  unfold tailWord_880928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065041876277890684765719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21420055835037187579687625 16065041876277890684765719)
  ·
    refine ⟨24097562814416836027148579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16065041876277890684765719 24097562814416836027148579)
    ·
      refine ⟨36146344221625254040722869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24097562814416836027148579 36146344221625254040722869)
      ·
        refine ⟨3388719770777367566317769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36146344221625254040722869 3388719770777367566317769)
        ·
          refine ⟨2541539828083025674738327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3388719770777367566317769 2541539828083025674738327)
          ·
            refine ⟨3812309742124538512107491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2541539828083025674738327 3812309742124538512107491)
            ·
              refine ⟨5718464613186807768161237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3812309742124538512107491 5718464613186807768161237)
              ·
                refine ⟨134026514371565807066279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5718464613186807768161237 134026514371565807066279)
                ·
                  rfl

theorem cell20_880928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_880928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880928 prefixEnd_880928 := by exact prefixLift 880928
  have htrace : WordTrace (prefixWord ++ tailWord_880928) baseStart_880928 baseEnd_880928 := by
    simpa [prefixWord, tailWord_880928, baseEnd_880928] using wordTrace_append hprefix tailTrace_880928
  have hstable : (prefixWord ++ tailWord_880928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880928).length < 2 ^ (prefixWord ++ tailWord_880928).sum := by decide
  have hdescent : baseEnd_880928 < baseStart_880928 := by decide
  rcases family_descends (prefixWord ++ tailWord_880928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880976 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_880976 : Nat := 118140960795 + 880976 * 2 ^ 59
def prefixEnd_880976 : Nat := 4983230072969 + 3 ^ 40 * 880976 * 2
def baseEnd_880976 : Nat := 402101451622622587598641

theorem tailTrace_880976 : CollatzResearch.WordTrace tailWord_880976 prefixEnd_880976 402101451622622587598641 := by
  unfold tailWord_880976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16065917228190942783639391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21421222970921257044852521 16065917228190942783639391)
  ·
    refine ⟨24098875842286414175459087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16065917228190942783639391 24098875842286414175459087)
    ·
      refine ⟨36148313763429621263188631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24098875842286414175459087 36148313763429621263188631)
      ·
        refine ⟨54222470645144431894782947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36148313763429621263188631 54222470645144431894782947)
        ·
          refine ⟨81333705967716647842174421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54222470645144431894782947 81333705967716647842174421)
          ·
            refine ⟨1906258733618358933800963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 81333705967716647842174421 1906258733618358933800963)
            ·
              refine ⟨2859388100427538400701445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906258733618358933800963 2859388100427538400701445)
              ·
                refine ⟨536135268830163450131521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2859388100427538400701445 536135268830163450131521)
                ·
                  refine ⟨402101451622622587598641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536135268830163450131521 402101451622622587598641)
                  ·
                    rfl

theorem cell20_880976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_880976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880976 prefixEnd_880976 := by exact prefixLift 880976
  have htrace : WordTrace (prefixWord ++ tailWord_880976) baseStart_880976 baseEnd_880976 := by
    simpa [prefixWord, tailWord_880976, baseEnd_880976] using wordTrace_append hprefix tailTrace_880976
  have hstable : (prefixWord ++ tailWord_880976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880976).length < 2 ^ (prefixWord ++ tailWord_880976).sum := by decide
  have hdescent : baseEnd_880976 < baseStart_880976 := by decide
  rcases family_descends (prefixWord ++ tailWord_880976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_880997 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 4]
def baseStart_880997 : Nat := 118140960795 + 880997 * 2 ^ 59
def prefixEnd_880997 : Nat := 4983230072969 + 3 ^ 40 * 880997 * 2
def baseEnd_880997 : Nat := 402111036594839847898555

theorem tailTrace_880997 : CollatzResearch.WordTrace tailWord_880997 prefixEnd_880997 402111036594839847898555 := by
  unfold tailWord_880997
  simp only [CollatzResearch.WordTrace]
  refine ⟨32132600389305806153793245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21421733592870537435862163 32132600389305806153793245)
  ·
    refine ⟨12049725145989677307672467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32132600389305806153793245 12049725145989677307672467)
    ·
      refine ⟨18074587718984515961508701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12049725145989677307672467 18074587718984515961508701)
      ·
        refine ⟨6777970394619193485565763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18074587718984515961508701 6777970394619193485565763)
        ·
          refine ⟨10166955591928790228348645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6777970394619193485565763 10166955591928790228348645)
          ·
            refine ⟨1906304173486648167815371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10166955591928790228348645 1906304173486648167815371)
            ·
              refine ⟨2859456260229972251723057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1906304173486648167815371 2859456260229972251723057)
              ·
                refine ⟨2144592195172479188792293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2859456260229972251723057 2144592195172479188792293)
                ·
                  refine ⟨402111036594839847898555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144592195172479188792293 402111036594839847898555)
                  ·
                    rfl

theorem cell20_880997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_880997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_880997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_880997 prefixEnd_880997 := by exact prefixLift 880997
  have htrace : WordTrace (prefixWord ++ tailWord_880997) baseStart_880997 baseEnd_880997 := by
    simpa [prefixWord, tailWord_880997, baseEnd_880997] using wordTrace_append hprefix tailTrace_880997
  have hstable : (prefixWord ++ tailWord_880997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_880997).length < 2 ^ (prefixWord ++ tailWord_880997).sum := by decide
  have hdescent : baseEnd_880997 < baseStart_880997 := by decide
  rcases family_descends (prefixWord ++ tailWord_880997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881035 : List Nat := [1, 1, 1, 1, 4, 5, 2, 1, 4]
def baseStart_881035 : Nat := 118140960795 + 881035 * 2 ^ 59
def prefixEnd_881035 : Nat := 4983230072969 + 3 ^ 40 * 881035 * 2
def baseEnd_881035 : Nat := 402128380830280604631733

theorem tailTrace_881035 : CollatzResearch.WordTrace tailWord_881035 prefixEnd_881035 402128380830280604631733 := by
  unfold tailWord_881035
  simp only [CollatzResearch.WordTrace]
  refine ⟨32133986363168138643676559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21422657575445425762451039 32133986363168138643676559)
  ·
    refine ⟨48200979544752207965514839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32133986363168138643676559 48200979544752207965514839)
    ·
      refine ⟨72301469317128311948272259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48200979544752207965514839 72301469317128311948272259)
      ·
        refine ⟨108452203975692467922408389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72301469317128311948272259 108452203975692467922408389)
        ·
          refine ⟨20334788245442337735451573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 108452203975692467922408389 20334788245442337735451573)
          ·
            refine ⟨1906386398010219162698585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20334788245442337735451573 1906386398010219162698585)
            ·
              refine ⟨1429789798507664372023939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1906386398010219162698585 1429789798507664372023939)
              ·
                refine ⟨2144684697761496558035909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1429789798507664372023939 2144684697761496558035909)
                ·
                  refine ⟨402128380830280604631733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2144684697761496558035909 402128380830280604631733)
                  ·
                    rfl

theorem cell20_881035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 2, 1, 4].length) (baseStart_881035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881035 prefixEnd_881035 := by exact prefixLift 881035
  have htrace : WordTrace (prefixWord ++ tailWord_881035) baseStart_881035 baseEnd_881035 := by
    simpa [prefixWord, tailWord_881035, baseEnd_881035] using wordTrace_append hprefix tailTrace_881035
  have hstable : (prefixWord ++ tailWord_881035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881035).length < 2 ^ (prefixWord ++ tailWord_881035).sum := by decide
  have hdescent : baseEnd_881035 < baseStart_881035 := by decide
  rcases family_descends (prefixWord ++ tailWord_881035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881059 : List Nat := [1, 1, 1, 4, 1, 6, 2, 4]
def baseStart_881059 : Nat := 118140960795 + 881059 * 2 ^ 59
def prefixEnd_881059 : Nat := 4983230072969 + 3 ^ 40 * 881059 * 2
def baseEnd_881059 : Nat := 134046445028081062610545

theorem tailTrace_881059 : CollatzResearch.WordTrace tailWord_881059 prefixEnd_881059 134046445028081062610545 := by
  unfold tailWord_881059
  simp only [CollatzResearch.WordTrace]
  refine ⟨32134861715081190742550231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21423241143387460495033487 32134861715081190742550231)
  ·
    refine ⟨48202292572621786113825347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32134861715081190742550231 48202292572621786113825347)
    ·
      refine ⟨72303438858932679170738021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48202292572621786113825347 72303438858932679170738021)
      ·
        refine ⟨13556894786049877344513379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 72303438858932679170738021 13556894786049877344513379)
        ·
          refine ⟨20335342179074816016770069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13556894786049877344513379 20335342179074816016770069)
          ·
            refine ⟨953219164644132000786097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20335342179074816016770069 953219164644132000786097)
            ·
              refine ⟨714914373483099000589573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953219164644132000786097 714914373483099000589573)
              ·
                refine ⟨134046445028081062610545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 714914373483099000589573 134046445028081062610545)
                ·
                  rfl

theorem cell20_881059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 4].length) (baseStart_881059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881059 prefixEnd_881059 := by exact prefixLift 881059
  have htrace : WordTrace (prefixWord ++ tailWord_881059) baseStart_881059 baseEnd_881059 := by
    simpa [prefixWord, tailWord_881059, baseEnd_881059] using wordTrace_append hprefix tailTrace_881059
  have hstable : (prefixWord ++ tailWord_881059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881059).length < 2 ^ (prefixWord ++ tailWord_881059).sum := by decide
  have hdescent : baseEnd_881059 < baseStart_881059 := by decide
  rcases family_descends (prefixWord ++ tailWord_881059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881100 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 3]
def baseStart_881100 : Nat := 118140960795 + 881100 * 2 ^ 59
def prefixEnd_881100 : Nat := 4983230072969 + 3 ^ 40 * 881100 * 2
def baseEnd_881100 : Nat := 402158048601429267464801

theorem tailTrace_881100 : CollatzResearch.WordTrace tailWord_881100 prefixEnd_881100 402158048601429267464801 := by
  unfold tailWord_881100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16068178553966327372396377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21424238071955103163195169 16068178553966327372396377)
  ·
    refine ⟨12051133915474745529297283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16068178553966327372396377 12051133915474745529297283)
    ·
      refine ⟨18076700873212118293945925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12051133915474745529297283 18076700873212118293945925)
      ·
        refine ⟨3389381413727272180114861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18076700873212118293945925 3389381413727272180114861)
        ·
          refine ⟨1271018030147727067543073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3389381413727272180114861 1271018030147727067543073)
          ·
            refine ⟨953263522610795300657305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271018030147727067543073 953263522610795300657305)
            ·
              refine ⟨714947641958096475492979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953263522610795300657305 714947641958096475492979)
              ·
                refine ⟨1072421462937144713239469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 714947641958096475492979 1072421462937144713239469)
                ·
                  refine ⟨402158048601429267464801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072421462937144713239469 402158048601429267464801)
                  ·
                    rfl

theorem cell20_881100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 3].length) (baseStart_881100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881100 prefixEnd_881100 := by exact prefixLift 881100
  have htrace : WordTrace (prefixWord ++ tailWord_881100) baseStart_881100 baseEnd_881100 := by
    simpa [prefixWord, tailWord_881100, baseEnd_881100] using wordTrace_append hprefix tailTrace_881100
  have hstable : (prefixWord ++ tailWord_881100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881100).length < 2 ^ (prefixWord ++ tailWord_881100).sum := by decide
  have hdescent : baseEnd_881100 < baseStart_881100 := by decide
  rcases family_descends (prefixWord ++ tailWord_881100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881141 : List Nat := [1, 3, 5, 1, 2, 2, 2, 2, 2]
def baseStart_881141 : Nat := 118140960795 + 881141 * 2 ^ 59
def prefixEnd_881141 : Nat := 4983230072969 + 3 ^ 40 * 881141 * 2
def baseEnd_881141 : Nat := 402176762118615347097967

theorem tailTrace_881141 : CollatzResearch.WordTrace tailWord_881141 prefixEnd_881141 402176762118615347097967 := by
  unfold tailWord_881141
  simp only [CollatzResearch.WordTrace]
  refine ⟨32137852500784118747035277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21425235000522745831356851 32137852500784118747035277)
  ·
    refine ⟨12051694687794044530138229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32137852500784118747035277 12051694687794044530138229)
    ·
      refine ⟨1129846376980691674700459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12051694687794044530138229 1129846376980691674700459)
      ·
        refine ⟨1694769565471037512050689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1129846376980691674700459 1694769565471037512050689)
        ·
          refine ⟨1271077174103278134038017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1694769565471037512050689 1271077174103278134038017)
          ·
            refine ⟨953307880577458600528513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1271077174103278134038017 953307880577458600528513)
            ·
              refine ⟨714980910433093950396385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953307880577458600528513 714980910433093950396385)
              ·
                refine ⟨536235682824820462797289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 714980910433093950396385 536235682824820462797289)
                ·
                  refine ⟨402176762118615347097967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536235682824820462797289 402176762118615347097967)
                  ·
                    rfl

theorem cell20_881141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 2, 2, 2].length) (baseStart_881141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881141 prefixEnd_881141 := by exact prefixLift 881141
  have htrace : WordTrace (prefixWord ++ tailWord_881141) baseStart_881141 baseEnd_881141 := by
    simpa [prefixWord, tailWord_881141, baseEnd_881141] using wordTrace_append hprefix tailTrace_881141
  have hstable : (prefixWord ++ tailWord_881141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881141).length < 2 ^ (prefixWord ++ tailWord_881141).sum := by decide
  have hdescent : baseEnd_881141 < baseStart_881141 := by decide
  rcases family_descends (prefixWord ++ tailWord_881141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881194 : List Nat := [3, 1, 4, 1, 1, 3, 7]
def baseStart_881194 : Nat := 118140960795 + 881194 * 2 ^ 59
def prefixEnd_881194 : Nat := 4983230072969 + 3 ^ 40 * 881194 * 2
def baseEnd_881194 : Nat := 44688994751420302036787

theorem tailTrace_881194 : CollatzResearch.WordTrace tailWord_881194 prefixEnd_881194 44688994751420302036787 := by
  unfold tailWord_881194
  simp only [CollatzResearch.WordTrace]
  refine ⟨8034946392398027199678659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21426523713061405865809757 8034946392398027199678659)
  ·
    refine ⟨12052419588597040799517989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8034946392398027199678659 12052419588597040799517989)
    ·
      refine ⟨2259828672861945149909623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12052419588597040799517989 2259828672861945149909623)
      ·
        refine ⟨3389743009292917724864435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2259828672861945149909623 3389743009292917724864435)
        ·
          refine ⟨5084614513939376587296653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3389743009292917724864435 5084614513939376587296653)
          ·
            refine ⟨1906730442727266220236245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5084614513939376587296653 1906730442727266220236245)
            ·
              refine ⟨44688994751420302036787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1906730442727266220236245 44688994751420302036787)
              ·
                rfl

theorem cell20_881194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 7].length) (baseStart_881194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881194 prefixEnd_881194 := by exact prefixLift 881194
  have htrace : WordTrace (prefixWord ++ tailWord_881194) baseStart_881194 baseEnd_881194 := by
    simpa [prefixWord, tailWord_881194, baseEnd_881194] using wordTrace_append hprefix tailTrace_881194
  have hstable : (prefixWord ++ tailWord_881194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881194).length < 2 ^ (prefixWord ++ tailWord_881194).sum := by decide
  have hdescent : baseEnd_881194 < baseStart_881194 := by decide
  rcases family_descends (prefixWord ++ tailWord_881194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881215 : List Nat := [1, 1, 2, 2, 3, 2, 2, 7]
def baseStart_881215 : Nat := 118140960795 + 881215 * 2 ^ 59
def prefixEnd_881215 : Nat := 4983230072969 + 3 ^ 40 * 881215 * 2
def baseEnd_881215 : Nat := 134070179244999992876999

theorem tailTrace_881215 : CollatzResearch.WordTrace tailWord_881215 prefixEnd_881215 134070179244999992876999 := by
  unfold tailWord_881215
  simp only [CollatzResearch.WordTrace]
  refine ⟨32140551502516029385229099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21427034335010686256819399 32140551502516029385229099)
  ·
    refine ⟨48210827253774044077843649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32140551502516029385229099 48210827253774044077843649)
    ·
      refine ⟨36158120440330533058382737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48210827253774044077843649 36158120440330533058382737)
      ·
        refine ⟨27118590330247899793787053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36158120440330533058382737 27118590330247899793787053)
        ·
          refine ⟨10169471373842962422670145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27118590330247899793787053 10169471373842962422670145)
          ·
            refine ⟨7627103530382221817002609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10169471373842962422670145 7627103530382221817002609)
            ·
              refine ⟨5720327647786666362751957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7627103530382221817002609 5720327647786666362751957)
              ·
                refine ⟨134070179244999992876999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5720327647786666362751957 134070179244999992876999)
                ·
                  rfl

theorem cell20_881215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 7].length) (baseStart_881215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881215 prefixEnd_881215 := by exact prefixLift 881215
  have htrace : WordTrace (prefixWord ++ tailWord_881215) baseStart_881215 baseEnd_881215 := by
    simpa [prefixWord, tailWord_881215, baseEnd_881215] using wordTrace_append hprefix tailTrace_881215
  have hstable : (prefixWord ++ tailWord_881215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881215).length < 2 ^ (prefixWord ++ tailWord_881215).sum := by decide
  have hdescent : baseEnd_881215 < baseStart_881215 := by decide
  rcases family_descends (prefixWord ++ tailWord_881215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881263 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 2]
def baseStart_881263 : Nat := 118140960795 + 881263 * 2 ^ 59
def prefixEnd_881263 : Nat := 4983230072969 + 3 ^ 40 * 881263 * 2
def baseEnd_881263 : Nat := 402232446242925145030801

theorem tailTrace_881263 : CollatzResearch.WordTrace tailWord_881263 prefixEnd_881263 402232446242925145030801 := by
  unfold tailWord_881263
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142302206342133582976443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428201470894755721984295 32142302206342133582976443)
  ·
    refine ⟨48213453309513200374464665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32142302206342133582976443 48213453309513200374464665)
    ·
      refine ⟨36160089982134900280848499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48213453309513200374464665 36160089982134900280848499)
      ·
        refine ⟨54240134973202350421272749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36160089982134900280848499 54240134973202350421272749)
        ·
          refine ⟨20340050614950881407977281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 54240134973202350421272749 20340050614950881407977281)
          ·
            refine ⟨15255037961213161055982961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20340050614950881407977281 15255037961213161055982961)
            ·
              refine ⟨11441278470909870791987221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15255037961213161055982961 11441278470909870791987221)
              ·
                refine ⟨536309928323900193374401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11441278470909870791987221 536309928323900193374401)
                ·
                  refine ⟨402232446242925145030801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536309928323900193374401 402232446242925145030801)
                  ·
                    rfl

theorem cell20_881263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2].length) (baseStart_881263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881263 prefixEnd_881263 := by exact prefixLift 881263
  have htrace : WordTrace (prefixWord ++ tailWord_881263) baseStart_881263 baseEnd_881263 := by
    simpa [prefixWord, tailWord_881263, baseEnd_881263] using wordTrace_append hprefix tailTrace_881263
  have hstable : (prefixWord ++ tailWord_881263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881263).length < 2 ^ (prefixWord ++ tailWord_881263).sum := by decide
  have hdescent : baseEnd_881263 < baseStart_881263 := by decide
  rcases family_descends (prefixWord ++ tailWord_881263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881269 : List Nat := [1, 3, 4, 2, 3, 1, 2, 1, 3]
def baseStart_881269 : Nat := 118140960795 + 881269 * 2 ^ 59
def prefixEnd_881269 : Nat := 4983230072969 + 3 ^ 40 * 881269 * 2
def baseEnd_881269 : Nat := 402235184806415790830777

theorem tailTrace_881269 : CollatzResearch.WordTrace tailWord_881269 prefixEnd_881269 402235184806415790830777 := by
  unfold tailWord_881269
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142521044320396607694861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428347362880264405129907 32142521044320396607694861)
  ·
    refine ⟨12053445391620148727885573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32142521044320396607694861 12053445391620148727885573)
    ·
      refine ⟨2260021010928777886478545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12053445391620148727885573 2260021010928777886478545)
      ·
        refine ⟨1695015758196583414858909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2260021010928777886478545 1695015758196583414858909)
        ·
          refine ⟨635630909323718780572091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1695015758196583414858909 635630909323718780572091)
          ·
            refine ⟨953446363985578170858137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635630909323718780572091 953446363985578170858137)
            ·
              refine ⟨715084772989183628143603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953446363985578170858137 715084772989183628143603)
              ·
                refine ⟨1072627159483775442215405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715084772989183628143603 1072627159483775442215405)
                ·
                  refine ⟨402235184806415790830777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072627159483775442215405 402235184806415790830777)
                  ·
                    rfl

theorem cell20_881269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_881269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881269 prefixEnd_881269 := by exact prefixLift 881269
  have htrace : WordTrace (prefixWord ++ tailWord_881269) baseStart_881269 baseEnd_881269 := by
    simpa [prefixWord, tailWord_881269, baseEnd_881269] using wordTrace_append hprefix tailTrace_881269
  have hstable : (prefixWord ++ tailWord_881269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881269).length < 2 ^ (prefixWord ++ tailWord_881269).sum := by decide
  have hdescent : baseEnd_881269 < baseStart_881269 := by decide
  rcases family_descends (prefixWord ++ tailWord_881269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881273 : List Nat := [1, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_881273 : Nat := 118140960795 + 881273 * 2 ^ 59
def prefixEnd_881273 : Nat := 4983230072969 + 3 ^ 40 * 881273 * 2
def baseEnd_881273 : Nat := 402237010515409554697427

theorem tailTrace_881273 : CollatzResearch.WordTrace tailWord_881273 prefixEnd_881273 402237010515409554697427 := by
  unfold tailWord_881273
  simp only [CollatzResearch.WordTrace]
  refine ⟨32142666936305905290840473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21428444624203936860560315 32142666936305905290840473)
  ·
    refine ⟨24107000202229428968130355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32142666936305905290840473 24107000202229428968130355)
    ·
      refine ⟨36160500303344143452195533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24107000202229428968130355 36160500303344143452195533)
      ·
        refine ⟨13560187613754053794573325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36160500303344143452195533 13560187613754053794573325)
        ·
          refine ⟨5085070355157770172964997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13560187613754053794573325 5085070355157770172964997)
          ·
            refine ⟨953450691592081907430937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5085070355157770172964997 953450691592081907430937)
            ·
              refine ⟨715088018694061430573203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 953450691592081907430937 715088018694061430573203)
              ·
                refine ⟨1072632028041092145859805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715088018694061430573203 1072632028041092145859805)
                ·
                  refine ⟨402237010515409554697427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072632028041092145859805 402237010515409554697427)
                  ·
                    rfl

theorem cell20_881273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_881273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881273 prefixEnd_881273 := by exact prefixLift 881273
  have htrace : WordTrace (prefixWord ++ tailWord_881273) baseStart_881273 baseEnd_881273 := by
    simpa [prefixWord, tailWord_881273, baseEnd_881273] using wordTrace_append hprefix tailTrace_881273
  have hstable : (prefixWord ++ tailWord_881273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881273).length < 2 ^ (prefixWord ++ tailWord_881273).sum := by decide
  have hdescent : baseEnd_881273 < baseStart_881273 := by decide
  rcases family_descends (prefixWord ++ tailWord_881273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881325 : List Nat := [1, 5, 2, 1, 1, 4, 1, 5]
def baseStart_881325 : Nat := 118140960795 + 881325 * 2 ^ 59
def prefixEnd_881325 : Nat := 4983230072969 + 3 ^ 40 * 881325 * 2
def baseEnd_881325 : Nat := 134086914910776161654627

theorem tailTrace_881325 : CollatzResearch.WordTrace tailWord_881325 prefixEnd_881325 134086914910776161654627 := by
  unfold tailWord_881325
  simp only [CollatzResearch.WordTrace]
  refine ⟨32144563532117518171733429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21429709021411678781155619 32144563532117518171733429)
  ·
    refine ⟨3013552831136017328600009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32144563532117518171733429 3013552831136017328600009)
    ·
      refine ⟨2260164623352012996450007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3013552831136017328600009 2260164623352012996450007)
      ·
        refine ⟨3390246935028019494675011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260164623352012996450007 3390246935028019494675011)
        ·
          refine ⟨5085370402542029242012517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390246935028019494675011 5085370402542029242012517)
          ·
            refine ⟨953506950476630482877347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5085370402542029242012517 953506950476630482877347)
            ·
              refine ⟨1430260425714945724316021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953506950476630482877347 1430260425714945724316021)
              ·
                refine ⟨134086914910776161654627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1430260425714945724316021 134086914910776161654627)
                ·
                  rfl

theorem cell20_881325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 5].length) (baseStart_881325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881325 prefixEnd_881325 := by exact prefixLift 881325
  have htrace : WordTrace (prefixWord ++ tailWord_881325) baseStart_881325 baseEnd_881325 := by
    simpa [prefixWord, tailWord_881325, baseEnd_881325] using wordTrace_append hprefix tailTrace_881325
  have hstable : (prefixWord ++ tailWord_881325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881325).length < 2 ^ (prefixWord ++ tailWord_881325).sum := by decide
  have hdescent : baseEnd_881325 < baseStart_881325 := by decide
  rcases family_descends (prefixWord ++ tailWord_881325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881336 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_881336 : Nat := 118140960795 + 881336 * 2 ^ 59
def prefixEnd_881336 : Nat := 4983230072969 + 3 ^ 40 * 881336 * 2
def baseEnd_881336 : Nat := 402265765432061335597169

theorem tailTrace_881336 : CollatzResearch.WordTrace tailWord_881336 prefixEnd_881336 402265765432061335597169 := by
  unfold tailWord_881336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16072482367538833525191931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21429976490051778033589241 16072482367538833525191931)
  ·
    refine ⟨24108723551308250287787897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16072482367538833525191931 24108723551308250287787897)
    ·
      refine ⟨18081542663481187715840923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24108723551308250287787897 18081542663481187715840923)
      ·
        refine ⟨27122313995221781573761385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18081542663481187715840923 27122313995221781573761385)
        ·
          refine ⟨20341735496416336180321039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27122313995221781573761385 20341735496416336180321039)
          ·
            refine ⟨30512603244624504270481559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20341735496416336180321039 30512603244624504270481559)
            ·
              refine ⟨45768904866936756405722339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30512603244624504270481559 45768904866936756405722339)
              ·
                refine ⟨68653357300405134608583509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45768904866936756405722339 68653357300405134608583509)
                ·
                  refine ⟨402265765432061335597169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 68653357300405134608583509 402265765432061335597169)
                  ·
                    rfl

theorem cell20_881336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_881336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881336 prefixEnd_881336 := by exact prefixLift 881336
  have htrace : WordTrace (prefixWord ++ tailWord_881336) baseStart_881336 baseEnd_881336 := by
    simpa [prefixWord, tailWord_881336, baseEnd_881336] using wordTrace_append hprefix tailTrace_881336
  have hstable : (prefixWord ++ tailWord_881336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881336).length < 2 ^ (prefixWord ++ tailWord_881336).sum := by decide
  have hdescent : baseEnd_881336 < baseStart_881336 := by decide
  rcases family_descends (prefixWord ++ tailWord_881336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881356 : List Nat := [2, 2, 1, 5, 1, 1, 1, 5, 2]
def baseStart_881356 : Nat := 118140960795 + 881356 * 2 ^ 59
def prefixEnd_881356 : Nat := 4983230072969 + 3 ^ 40 * 881356 * 2
def baseEnd_881356 : Nat := 402274893977030154930421

theorem tailTrace_881356 : CollatzResearch.WordTrace tailWord_881356 prefixEnd_881356 402274893977030154930421 := by
  unfold tailWord_881356
  simp only [CollatzResearch.WordTrace]
  refine ⟨16072847097502605233055961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21430462796670140310741281 16072847097502605233055961)
  ·
    refine ⟨12054635323126953924791971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16072847097502605233055961 12054635323126953924791971)
    ·
      refine ⟨18081952984690430887187957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12054635323126953924791971 18081952984690430887187957)
      ·
        refine ⟨1695183092314727895673871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18081952984690430887187957 1695183092314727895673871)
        ·
          refine ⟨2542774638472091843510807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695183092314727895673871 2542774638472091843510807)
          ·
            refine ⟨3814161957708137765266211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2542774638472091843510807 3814161957708137765266211)
            ·
              refine ⟨5721242936562206647899317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814161957708137765266211 5721242936562206647899317)
              ·
                refine ⟨536366525302706873240561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5721242936562206647899317 536366525302706873240561)
                ·
                  refine ⟨402274893977030154930421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536366525302706873240561 402274893977030154930421)
                  ·
                    rfl

theorem cell20_881356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_881356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881356 prefixEnd_881356 := by exact prefixLift 881356
  have htrace : WordTrace (prefixWord ++ tailWord_881356) baseStart_881356 baseEnd_881356 := by
    simpa [prefixWord, tailWord_881356, baseEnd_881356] using wordTrace_append hprefix tailTrace_881356
  have hstable : (prefixWord ++ tailWord_881356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881356).length < 2 ^ (prefixWord ++ tailWord_881356).sum := by decide
  have hdescent : baseEnd_881356 < baseStart_881356 := by decide
  rcases family_descends (prefixWord ++ tailWord_881356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881367 : List Nat := [1, 1, 3, 2, 1, 5, 7]
def baseStart_881367 : Nat := 118140960795 + 881367 * 2 ^ 59
def prefixEnd_881367 : Nat := 4983230072969 + 3 ^ 40 * 881367 * 2
def baseEnd_881367 : Nat := 44697768297418111729301

theorem tailTrace_881367 : CollatzResearch.WordTrace tailWord_881367 prefixEnd_881367 44697768297418111729301 := by
  unfold tailWord_881367
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146095397965359344762355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21430730265310239563174903 32146095397965359344762355)
  ·
    refine ⟨48219143096948039017143533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32146095397965359344762355 48219143096948039017143533)
    ·
      refine ⟨18082178661355514631428825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48219143096948039017143533 18082178661355514631428825)
      ·
        refine ⟨13561633996016635973571619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18082178661355514631428825 13561633996016635973571619)
        ·
          refine ⟨20342450994024953960357429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13561633996016635973571619 20342450994024953960357429)
          ·
            refine ⟨1907104780689839433783509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20342450994024953960357429 1907104780689839433783509)
            ·
              refine ⟨44697768297418111729301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1907104780689839433783509 44697768297418111729301)
              ·
                rfl

theorem cell20_881367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 7].length) (baseStart_881367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881367 prefixEnd_881367 := by exact prefixLift 881367
  have htrace : WordTrace (prefixWord ++ tailWord_881367) baseStart_881367 baseEnd_881367 := by
    simpa [prefixWord, tailWord_881367, baseEnd_881367] using wordTrace_append hprefix tailTrace_881367
  have hstable : (prefixWord ++ tailWord_881367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881367).length < 2 ^ (prefixWord ++ tailWord_881367).sum := by decide
  have hdescent : baseEnd_881367 < baseStart_881367 := by decide
  rcases family_descends (prefixWord ++ tailWord_881367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881377 : List Nat := [1, 2, 3, 1, 4, 2, 2, 1, 4]
def baseStart_881377 : Nat := 118140960795 + 881377 * 2 ^ 59
def prefixEnd_881377 : Nat := 4983230072969 + 3 ^ 40 * 881377 * 2
def baseEnd_881377 : Nat := 402284478949247415230335

theorem tailTrace_881377 : CollatzResearch.WordTrace tailWord_881377 prefixEnd_881377 402284478949247415230335 := by
  unfold tailWord_881377
  simp only [CollatzResearch.WordTrace]
  refine ⟨32146460127929131052626385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21430973418619420701750923 32146460127929131052626385)
  ·
    refine ⟨24109845095946848289469789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32146460127929131052626385 24109845095946848289469789)
    ·
      refine ⟨9041191910980068108551171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24109845095946848289469789 9041191910980068108551171)
      ·
        refine ⟨13561787866470102162826757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041191910980068108551171 13561787866470102162826757)
        ·
          refine ⟨2542835224963144155530017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13561787866470102162826757 2542835224963144155530017)
          ·
            refine ⟨1907126418722358116647513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2542835224963144155530017 1907126418722358116647513)
            ·
              refine ⟨1430344814041768587485635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907126418722358116647513 1430344814041768587485635)
              ·
                refine ⟨2145517221062652881228453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1430344814041768587485635 2145517221062652881228453)
                ·
                  refine ⟨402284478949247415230335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2145517221062652881228453 402284478949247415230335)
                  ·
                    rfl

theorem cell20_881377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_881377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881377 prefixEnd_881377 := by exact prefixLift 881377
  have htrace : WordTrace (prefixWord ++ tailWord_881377) baseStart_881377 baseEnd_881377 := by
    simpa [prefixWord, tailWord_881377, baseEnd_881377] using wordTrace_append hprefix tailTrace_881377
  have hstable : (prefixWord ++ tailWord_881377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881377).length < 2 ^ (prefixWord ++ tailWord_881377).sum := by decide
  have hdescent : baseEnd_881377 < baseStart_881377 := by decide
  rcases family_descends (prefixWord ++ tailWord_881377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881405 : List Nat := [1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_881405 : Nat := 118140960795 + 881405 * 2 ^ 59
def prefixEnd_881405 : Nat := 4983230072969 + 3 ^ 40 * 881405 * 2
def baseEnd_881405 : Nat := 134099086304067920765629

theorem tailTrace_881405 : CollatzResearch.WordTrace tailWord_881405 prefixEnd_881405 134099086304067920765629 := by
  unfold tailWord_881405
  simp only [CollatzResearch.WordTrace]
  refine ⟨32147481371827691834645669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21431654247885127889763779 32147481371827691834645669)
  ·
    refine ⟨6027652757217692218996063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32147481371827691834645669 6027652757217692218996063)
    ·
      refine ⟨9041479135826538328494095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6027652757217692218996063 9041479135826538328494095)
      ·
        refine ⟨13562218703739807492741143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041479135826538328494095 13562218703739807492741143)
        ·
          refine ⟨20343328055609711239111715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13562218703739807492741143 20343328055609711239111715)
          ·
            refine ⟨30514992083414566858667573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20343328055609711239111715 30514992083414566858667573)
            ·
              refine ⟨2860780507820115643000085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30514992083414566858667573 2860780507820115643000085)
              ·
                refine ⟨134099086304067920765629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2860780507820115643000085 134099086304067920765629)
                ·
                  rfl

theorem cell20_881405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_881405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881405 prefixEnd_881405 := by exact prefixLift 881405
  have htrace : WordTrace (prefixWord ++ tailWord_881405) baseStart_881405 baseEnd_881405 := by
    simpa [prefixWord, tailWord_881405, baseEnd_881405] using wordTrace_append hprefix tailTrace_881405
  have hstable : (prefixWord ++ tailWord_881405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881405).length < 2 ^ (prefixWord ++ tailWord_881405).sum := by decide
  have hdescent : baseEnd_881405 < baseStart_881405 := by decide
  rcases family_descends (prefixWord ++ tailWord_881405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881429 : List Nat := [1, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_881429 : Nat := 118140960795 + 881429 * 2 ^ 59
def prefixEnd_881429 : Nat := 4983230072969 + 3 ^ 40 * 881429 * 2
def baseEnd_881429 : Nat := 402308213166166345496789

theorem tailTrace_881429 : CollatzResearch.WordTrace tailWord_881429 prefixEnd_881429 402308213166166345496789 := by
  unfold tailWord_881429
  simp only [CollatzResearch.WordTrace]
  refine ⟨32148356723740743933519341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21432237815827162622346227 32148356723740743933519341)
  ·
    refine ⟨12055633771402778975069753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32148356723740743933519341 12055633771402778975069753)
    ·
      refine ⟨9041725328552084231302315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12055633771402778975069753 9041725328552084231302315)
      ·
        refine ⟨13562587992828126346953473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9041725328552084231302315 13562587992828126346953473)
        ·
          refine ⟨10171940994621094760215105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13562587992828126346953473 10171940994621094760215105)
          ·
            refine ⟨7628955745965821070161329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10171940994621094760215105 7628955745965821070161329)
            ·
              refine ⟨5721716809474365802620997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7628955745965821070161329 5721716809474365802620997)
              ·
                refine ⟨1072821901776443587991437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5721716809474365802620997 1072821901776443587991437)
                ·
                  refine ⟨402308213166166345496789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072821901776443587991437 402308213166166345496789)
                  ·
                    rfl

theorem cell20_881429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_881429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881429 prefixEnd_881429 := by exact prefixLift 881429
  have htrace : WordTrace (prefixWord ++ tailWord_881429) baseStart_881429 baseEnd_881429 := by
    simpa [prefixWord, tailWord_881429, baseEnd_881429] using wordTrace_append hprefix tailTrace_881429
  have hstable : (prefixWord ++ tailWord_881429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881429).length < 2 ^ (prefixWord ++ tailWord_881429).sum := by decide
  have hdescent : baseEnd_881429 < baseStart_881429 := by decide
  rcases family_descends (prefixWord ++ tailWord_881429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881484 : List Nat := [2, 2, 1, 3, 3, 2, 2, 2, 3]
def baseStart_881484 : Nat := 118140960795 + 881484 * 2 ^ 59
def prefixEnd_881484 : Nat := 4983230072969 + 3 ^ 40 * 881484 * 2
def baseEnd_881484 : Nat := 402333316664830598663231

theorem tailTrace_881484 : CollatzResearch.WordTrace tailWord_881484 prefixEnd_881484 402333316664830598663231 := by
  unfold tailWord_881484
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075181369270744163385753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21433575159027658884514337 16075181369270744163385753)
  ·
    refine ⟨12056386026953058122539315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16075181369270744163385753 12056386026953058122539315)
    ·
      refine ⟨18084579040429587183808973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056386026953058122539315 18084579040429587183808973)
      ·
        refine ⟨6781717140161095193928365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18084579040429587183808973 6781717140161095193928365)
        ·
          refine ⟨2543143927560410697723137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6781717140161095193928365 2543143927560410697723137)
          ·
            refine ⟨1907357945670308023292353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543143927560410697723137 1907357945670308023292353)
            ·
              refine ⟨1430518459252731017469265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907357945670308023292353 1430518459252731017469265)
              ·
                refine ⟨1072888844439548263101949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430518459252731017469265 1072888844439548263101949)
                ·
                  refine ⟨402333316664830598663231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1072888844439548263101949 402333316664830598663231)
                  ·
                    rfl

theorem cell20_881484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_881484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881484 prefixEnd_881484 := by exact prefixLift 881484
  have htrace : WordTrace (prefixWord ++ tailWord_881484) baseStart_881484 baseEnd_881484 := by
    simpa [prefixWord, tailWord_881484, baseEnd_881484] using wordTrace_append hprefix tailTrace_881484
  have hstable : (prefixWord ++ tailWord_881484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881484).length < 2 ^ (prefixWord ++ tailWord_881484).sum := by decide
  have hdescent : baseEnd_881484 < baseStart_881484 := by decide
  rcases family_descends (prefixWord ++ tailWord_881484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881488 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_881488 : Nat := 118140960795 + 881488 * 2 ^ 59
def prefixEnd_881488 : Nat := 4983230072969 + 3 ^ 40 * 881488 * 2
def baseEnd_881488 : Nat := 402335142373824362529881

theorem tailTrace_881488 : CollatzResearch.WordTrace tailWord_881488 prefixEnd_881488 402335142373824362529881 := by
  unfold tailWord_881488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075254315263498504958559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21433672420351331339944745 16075254315263498504958559)
  ·
    refine ⟨24112881472895247757437839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16075254315263498504958559 24112881472895247757437839)
    ·
      refine ⟨36169322209342871636156759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24112881472895247757437839 36169322209342871636156759)
      ·
        refine ⟨54253983314014307454235139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36169322209342871636156759 54253983314014307454235139)
        ·
          refine ⟨81380974971021461181352709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 54253983314014307454235139 81380974971021461181352709)
          ·
            refine ⟨15258932807066523971503633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 81380974971021461181352709 15258932807066523971503633)
            ·
              refine ⟨11444199605299892978627725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15258932807066523971503633 11444199605299892978627725)
              ·
                refine ⟨4291574851987459866985397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11444199605299892978627725 4291574851987459866985397)
                ·
                  refine ⟨402335142373824362529881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291574851987459866985397 402335142373824362529881)
                  ·
                    rfl

theorem cell20_881488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_881488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881488 prefixEnd_881488 := by exact prefixLift 881488
  have htrace : WordTrace (prefixWord ++ tailWord_881488) baseStart_881488 baseEnd_881488 := by
    simpa [prefixWord, tailWord_881488, baseEnd_881488] using wordTrace_append hprefix tailTrace_881488
  have hstable : (prefixWord ++ tailWord_881488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881488).length < 2 ^ (prefixWord ++ tailWord_881488).sum := by decide
  have hdescent : baseEnd_881488 < baseStart_881488 := by decide
  rcases family_descends (prefixWord ++ tailWord_881488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881498 : List Nat := [3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_881498 : Nat := 118140960795 + 881498 * 2 ^ 59
def prefixEnd_881498 : Nat := 4983230072969 + 3 ^ 40 * 881498 * 2
def baseEnd_881498 : Nat := 134113235548769590732169

theorem tailTrace_881498 : CollatzResearch.WordTrace tailWord_881498 prefixEnd_881498 134113235548769590732169 := by
  unfold tailWord_881498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8037718340122692179445287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21433915573660512478520765 8037718340122692179445287)
  ·
    refine ⟨12056577510184038269167931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8037718340122692179445287 12056577510184038269167931)
    ·
      refine ⟨18084866265276057403751897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12056577510184038269167931 18084866265276057403751897)
      ·
        refine ⟨13563649698957043052813923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18084866265276057403751897 13563649698957043052813923)
        ·
          refine ⟨20345474548435564579220885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13563649698957043052813923 20345474548435564579220885)
          ·
            refine ⟨953694119457917089650979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20345474548435564579220885 953694119457917089650979)
            ·
              refine ⟨1430541179186875634476469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 953694119457917089650979 1430541179186875634476469)
              ·
                refine ⟨134113235548769590732169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1430541179186875634476469 134113235548769590732169)
                ·
                  rfl

theorem cell20_881498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_881498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881498 prefixEnd_881498 := by exact prefixLift 881498
  have htrace : WordTrace (prefixWord ++ tailWord_881498) baseStart_881498 baseEnd_881498 := by
    simpa [prefixWord, tailWord_881498, baseEnd_881498] using wordTrace_append hprefix tailTrace_881498
  have hstable : (prefixWord ++ tailWord_881498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881498).length < 2 ^ (prefixWord ++ tailWord_881498).sum := by decide
  have hdescent : baseEnd_881498 < baseStart_881498 := by decide
  rcases family_descends (prefixWord ++ tailWord_881498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881512 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 6]
def baseStart_881512 : Nat := 118140960795 + 881512 * 2 ^ 59
def prefixEnd_881512 : Nat := 4983230072969 + 3 ^ 40 * 881512 * 2
def baseEnd_881512 : Nat := 402346096627786945729783

theorem tailTrace_881512 : CollatzResearch.WordTrace tailWord_881512 prefixEnd_881512 402346096627786945729783 := by
  unfold tailWord_881512
  simp only [CollatzResearch.WordTrace]
  refine ⟨16075691991220024554395395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21434255988293366072527193 16075691991220024554395395)
  ·
    refine ⟨24113537986830036831593093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16075691991220024554395395 24113537986830036831593093)
    ·
      refine ⟨4521288372530631905923705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24113537986830036831593093 4521288372530631905923705)
      ·
        refine ⟨3390966279397973929442779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4521288372530631905923705 3390966279397973929442779)
        ·
          refine ⟨5086449419096960894164169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390966279397973929442779 5086449419096960894164169)
          ·
            refine ⟨3814837064322720670623127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5086449419096960894164169 3814837064322720670623127)
            ·
              refine ⟨5722255596484081005934691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814837064322720670623127 5722255596484081005934691)
              ·
                refine ⟨8583383394726121508902037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5722255596484081005934691 8583383394726121508902037)
                ·
                  refine ⟨402346096627786945729783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8583383394726121508902037 402346096627786945729783)
                  ·
                    rfl

theorem cell20_881512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_881512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881512 prefixEnd_881512 := by exact prefixLift 881512
  have htrace : WordTrace (prefixWord ++ tailWord_881512) baseStart_881512 baseEnd_881512 := by
    simpa [prefixWord, tailWord_881512, baseEnd_881512] using wordTrace_append hprefix tailTrace_881512
  have hstable : (prefixWord ++ tailWord_881512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881512).length < 2 ^ (prefixWord ++ tailWord_881512).sum := by decide
  have hdescent : baseEnd_881512 < baseStart_881512 := by decide
  rcases family_descends (prefixWord ++ tailWord_881512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881529 : List Nat := [1, 2, 1, 3, 2, 3, 1, 5, 2]
def baseStart_881529 : Nat := 118140960795 + 881529 * 2 ^ 59
def prefixEnd_881529 : Nat := 4983230072969 + 3 ^ 40 * 881529 * 2
def baseEnd_881529 : Nat := 402353855891010442163047

theorem tailTrace_881529 : CollatzResearch.WordTrace tailWord_881529 prefixEnd_881529 402353855891010442163047 := by
  unfold tailWord_881529
  simp only [CollatzResearch.WordTrace]
  refine ⟨32152004023378461012159641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21434669348918974008106427 32152004023378461012159641)
  ·
    refine ⟨24114003017533845759119731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32152004023378461012159641 24114003017533845759119731)
    ·
      refine ⟨36171004526300768638679597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24114003017533845759119731 36171004526300768638679597)
      ·
        refine ⟨13564126697362788239504849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36171004526300768638679597 13564126697362788239504849)
        ·
          refine ⟨10173095023022091179628637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13564126697362788239504849 10173095023022091179628637)
          ·
            refine ⟨3814910633633284192360739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10173095023022091179628637 3814910633633284192360739)
            ·
              refine ⟨5722365950449926288541109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3814910633633284192360739 5722365950449926288541109)
              ·
                refine ⟨536471807854680589550729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5722365950449926288541109 536471807854680589550729)
                ·
                  refine ⟨402353855891010442163047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536471807854680589550729 402353855891010442163047)
                  ·
                    rfl

theorem cell20_881529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_881529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881529 prefixEnd_881529 := by exact prefixLift 881529
  have htrace : WordTrace (prefixWord ++ tailWord_881529) baseStart_881529 baseEnd_881529 := by
    simpa [prefixWord, tailWord_881529, baseEnd_881529] using wordTrace_append hprefix tailTrace_881529
  have hstable : (prefixWord ++ tailWord_881529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881529).length < 2 ^ (prefixWord ++ tailWord_881529).sum := by decide
  have hdescent : baseEnd_881529 < baseStart_881529 := by decide
  rcases family_descends (prefixWord ++ tailWord_881529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881543 : List Nat := [1, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_881543 : Nat := 118140960795 + 881543 * 2 ^ 59
def prefixEnd_881543 : Nat := 4983230072969 + 3 ^ 40 * 881543 * 2
def baseEnd_881543 : Nat := 402360245872488615696323

theorem tailTrace_881543 : CollatzResearch.WordTrace tailWord_881543 prefixEnd_881543 402360245872488615696323 := by
  unfold tailWord_881543
  simp only [CollatzResearch.WordTrace]
  refine ⟨32152514645327741403169283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21435009763551827602112855 32152514645327741403169283)
  ·
    refine ⟨48228771967991612104753925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32152514645327741403169283 48228771967991612104753925)
    ·
      refine ⟨9042894743998427269641361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48228771967991612104753925 9042894743998427269641361)
      ·
        refine ⟨6782171057998820452231021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9042894743998427269641361 6782171057998820452231021)
        ·
          refine ⟨2543314146749557669586633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6782171057998820452231021 2543314146749557669586633)
          ·
            refine ⟨1907485610062168252189975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2543314146749557669586633 1907485610062168252189975)
            ·
              refine ⟨2861228415093252378284963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1907485610062168252189975 2861228415093252378284963)
              ·
                refine ⟨4291842622639878567427445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2861228415093252378284963 4291842622639878567427445)
                ·
                  refine ⟨402360245872488615696323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4291842622639878567427445 402360245872488615696323)
                  ·
                    rfl

theorem cell20_881543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_881543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881543 prefixEnd_881543 := by exact prefixLift 881543
  have htrace : WordTrace (prefixWord ++ tailWord_881543) baseStart_881543 baseEnd_881543 := by
    simpa [prefixWord, tailWord_881543, baseEnd_881543] using wordTrace_append hprefix tailTrace_881543
  have hstable : (prefixWord ++ tailWord_881543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881543).length < 2 ^ (prefixWord ++ tailWord_881543).sum := by decide
  have hdescent : baseEnd_881543 < baseStart_881543 := by decide
  rcases family_descends (prefixWord ++ tailWord_881543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881546 : List Nat := [3, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_881546 : Nat := 118140960795 + 881546 * 2 ^ 59
def prefixEnd_881546 : Nat := 4983230072969 + 3 ^ 40 * 881546 * 2
def baseEnd_881546 : Nat := 402361615154233938596311

theorem tailTrace_881546 : CollatzResearch.WordTrace tailWord_881546 prefixEnd_881546 402361615154233938596311 := by
  unfold tailWord_881546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038156016079218228882123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21435082709544581943685661 8038156016079218228882123)
  ·
    refine ⟨12057234024118827343323185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038156016079218228882123 12057234024118827343323185)
    ·
      refine ⟨9042925518089120507492389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12057234024118827343323185 9042925518089120507492389)
      ·
        refine ⟨1695548534641710095154823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9042925518089120507492389 1695548534641710095154823)
        ·
          refine ⟨2543322801962565142732235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1695548534641710095154823 2543322801962565142732235)
          ·
            refine ⟨3814984202943847714098353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2543322801962565142732235 3814984202943847714098353)
            ·
              refine ⟨2861238152207885785573765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3814984202943847714098353 2861238152207885785573765)
              ·
                refine ⟨536482153538978584795081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2861238152207885785573765 536482153538978584795081)
                ·
                  refine ⟨402361615154233938596311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536482153538978584795081 402361615154233938596311)
                  ·
                    rfl

theorem cell20_881546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_881546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881546 prefixEnd_881546 := by exact prefixLift 881546
  have htrace : WordTrace (prefixWord ++ tailWord_881546) baseStart_881546 baseEnd_881546 := by
    simpa [prefixWord, tailWord_881546, baseEnd_881546] using wordTrace_append hprefix tailTrace_881546
  have hstable : (prefixWord ++ tailWord_881546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881546).length < 2 ^ (prefixWord ++ tailWord_881546).sum := by decide
  have hdescent : baseEnd_881546 < baseStart_881546 := by decide
  rcases family_descends (prefixWord ++ tailWord_881546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881640 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_881640 : Nat := 118140960795 + 881640 * 2 ^ 59
def prefixEnd_881640 : Nat := 4983230072969 + 3 ^ 40 * 881640 * 2
def baseEnd_881640 : Nat := 402404519315587389462593

theorem tailTrace_881640 : CollatzResearch.WordTrace tailWord_881640 prefixEnd_881640 402404519315587389462593 := by
  unfold tailWord_881640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078026262988163484725187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21437368350650884646300249 16078026262988163484725187)
  ·
    refine ⟨24117039394482245227087781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078026262988163484725187 24117039394482245227087781)
    ·
      refine ⟨4521944886465420980078959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24117039394482245227087781 4521944886465420980078959)
      ·
        refine ⟨6782917329698131470118439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4521944886465420980078959 6782917329698131470118439)
        ·
          refine ⟨10174375994547197205177659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6782917329698131470118439 10174375994547197205177659)
          ·
            refine ⟨15261563991820795807766489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10174375994547197205177659 15261563991820795807766489)
            ·
              refine ⟨11446172993865596855824867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15261563991820795807766489 11446172993865596855824867)
              ·
                refine ⟨17169259490798395283737301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11446172993865596855824867 17169259490798395283737301)
                ·
                  refine ⟨402404519315587389462593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17169259490798395283737301 402404519315587389462593)
                  ·
                    rfl

theorem cell20_881640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_881640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881640 prefixEnd_881640 := by exact prefixLift 881640
  have htrace : WordTrace (prefixWord ++ tailWord_881640) baseStart_881640 baseEnd_881640 := by
    simpa [prefixWord, tailWord_881640, baseEnd_881640] using wordTrace_append hprefix tailTrace_881640
  have hstable : (prefixWord ++ tailWord_881640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881640).length < 2 ^ (prefixWord ++ tailWord_881640).sum := by decide
  have hdescent : baseEnd_881640 < baseStart_881640 := by decide
  rcases family_descends (prefixWord ++ tailWord_881640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881650 : List Nat := [3, 2, 1, 5, 1, 8]
def baseStart_881650 : Nat := 118140960795 + 881650 * 2 ^ 59
def prefixEnd_881650 : Nat := 4983230072969 + 3 ^ 40 * 881650 * 2
def baseEnd_881650 : Nat := 14904040132891548115897

theorem tailTrace_881650 : CollatzResearch.WordTrace tailWord_881650 prefixEnd_881650 14904040132891548115897 := by
  unfold tailWord_881650
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039104313985024669328601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21437611503960065784876269 8039104313985024669328601)
  ·
    refine ⟨6029328235488768501996451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8039104313985024669328601 6029328235488768501996451)
    ·
      refine ⟨9043992353233152752994677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6029328235488768501996451 9043992353233152752994677)
      ·
        refine ⟨847874283115608070593251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9043992353233152752994677 847874283115608070593251)
        ·
          refine ⟨1271811424673412105889877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 847874283115608070593251 1271811424673412105889877)
          ·
            refine ⟨14904040132891548115897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1271811424673412105889877 14904040132891548115897)
            ·
              rfl

theorem cell20_881650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 8].length) (baseStart_881650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881650 prefixEnd_881650 := by exact prefixLift 881650
  have htrace : WordTrace (prefixWord ++ tailWord_881650) baseStart_881650 baseEnd_881650 := by
    simpa [prefixWord, tailWord_881650, baseEnd_881650] using wordTrace_append hprefix tailTrace_881650
  have hstable : (prefixWord ++ tailWord_881650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881650).length < 2 ^ (prefixWord ++ tailWord_881650).sum := by decide
  have hdescent : baseEnd_881650 < baseStart_881650 := by decide
  rcases family_descends (prefixWord ++ tailWord_881650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881657 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_881657 : Nat := 118140960795 + 881657 * 2 ^ 59
def prefixEnd_881657 : Nat := 4983230072969 + 3 ^ 40 * 881657 * 2
def baseEnd_881657 : Nat := 402412278578810885895857

theorem tailTrace_881657 : CollatzResearch.WordTrace tailWord_881657 prefixEnd_881657 402412278578810885895857 := by
  unfold tailWord_881657
  simp only [CollatzResearch.WordTrace]
  refine ⟨32156672566914738872819225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21437781711276492581879483 32156672566914738872819225)
  ·
    refine ⟨24117504425186054154614419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32156672566914738872819225 24117504425186054154614419)
    ·
      refine ⟨36176256637779081231921629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24117504425186054154614419 36176256637779081231921629)
      ·
        refine ⟨13566096239167155461970611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36176256637779081231921629 13566096239167155461970611)
        ·
          refine ⟨20349144358750733192955917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13566096239167155461970611 20349144358750733192955917)
          ·
            refine ⟨7630929134531524947358469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20349144358750733192955917 7630929134531524947358469)
            ·
              refine ⟨1430799212724660927629713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7630929134531524947358469 1430799212724660927629713)
              ·
                refine ⟨1073099409543495695722285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1430799212724660927629713 1073099409543495695722285)
                ·
                  refine ⟨402412278578810885895857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073099409543495695722285 402412278578810885895857)
                  ·
                    rfl

theorem cell20_881657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_881657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881657 prefixEnd_881657 := by exact prefixLift 881657
  have htrace : WordTrace (prefixWord ++ tailWord_881657) baseStart_881657 baseEnd_881657 := by
    simpa [prefixWord, tailWord_881657, baseEnd_881657] using wordTrace_append hprefix tailTrace_881657
  have hstable : (prefixWord ++ tailWord_881657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881657).length < 2 ^ (prefixWord ++ tailWord_881657).sum := by decide
  have hdescent : baseEnd_881657 < baseStart_881657 := by decide
  rcases family_descends (prefixWord ++ tailWord_881657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881660 : List Nat := [2, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_881660 : Nat := 118140960795 + 881660 * 2 ^ 59
def prefixEnd_881660 : Nat := 4983230072969 + 3 ^ 40 * 881660 * 2
def baseEnd_881660 : Nat := 402413647860556208795845

theorem tailTrace_881660 : CollatzResearch.WordTrace tailWord_881660 prefixEnd_881660 402413647860556208795845 := by
  unfold tailWord_881660
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078390992951935192589217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21437854657269246923452289 16078390992951935192589217)
  ·
    refine ⟨12058793244713951394441913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16078390992951935192589217 12058793244713951394441913)
    ·
      refine ⟨9044094933535463545831435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12058793244713951394441913 9044094933535463545831435)
      ·
        refine ⟨13566142400303195318747153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9044094933535463545831435 13566142400303195318747153)
        ·
          refine ⟨10174606800227396489060365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13566142400303195318747153 10174606800227396489060365)
          ·
            refine ⟨3815477550085273683397637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10174606800227396489060365 3815477550085273683397637)
            ·
              refine ⟨715402040640988815637057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3815477550085273683397637 715402040640988815637057)
              ·
                refine ⟨536551530480741611727793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 715402040640988815637057 536551530480741611727793)
                ·
                  refine ⟨402413647860556208795845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536551530480741611727793 402413647860556208795845)
                  ·
                    rfl

theorem cell20_881660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_881660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881660 prefixEnd_881660 := by exact prefixLift 881660
  have htrace : WordTrace (prefixWord ++ tailWord_881660) baseStart_881660 baseEnd_881660 := by
    simpa [prefixWord, tailWord_881660, baseEnd_881660] using wordTrace_append hprefix tailTrace_881660
  have hstable : (prefixWord ++ tailWord_881660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881660).length < 2 ^ (prefixWord ++ tailWord_881660).sum := by decide
  have hdescent : baseEnd_881660 < baseStart_881660 := by decide
  rcases family_descends (prefixWord ++ tailWord_881660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881688 : List Nat := [2, 1, 2, 3, 2, 3, 3, 4]
def baseStart_881688 : Nat := 118140960795 + 881688 * 2 ^ 59
def prefixEnd_881688 : Nat := 4983230072969 + 3 ^ 40 * 881688 * 2
def baseEnd_881688 : Nat := 134142142607837518620799

theorem tailTrace_881688 : CollatzResearch.WordTrace tailWord_881688 prefixEnd_881688 134142142607837518620799 := by
  unfold tailWord_881688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16078901614901215583598859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21438535486534954111465145 16078901614901215583598859)
  ·
    refine ⟨24118352422351823375398289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16078901614901215583598859 24118352422351823375398289)
    ·
      refine ⟨18088764316763867531548717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24118352422351823375398289 18088764316763867531548717)
      ·
        refine ⟨6783286618786450324330769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18088764316763867531548717 6783286618786450324330769)
        ·
          refine ⟨5087464964089837743248077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6783286618786450324330769 5087464964089837743248077)
          ·
            refine ⟨1907799361533689153718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5087464964089837743248077 1907799361533689153718029)
            ·
              refine ⟨715424760575133432644261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907799361533689153718029 715424760575133432644261)
              ·
                refine ⟨134142142607837518620799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715424760575133432644261 134142142607837518620799)
                ·
                  rfl

theorem cell20_881688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 4].length) (baseStart_881688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881688 prefixEnd_881688 := by exact prefixLift 881688
  have htrace : WordTrace (prefixWord ++ tailWord_881688) baseStart_881688 baseEnd_881688 := by
    simpa [prefixWord, tailWord_881688, baseEnd_881688] using wordTrace_append hprefix tailTrace_881688
  have hstable : (prefixWord ++ tailWord_881688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881688).length < 2 ^ (prefixWord ++ tailWord_881688).sum := by decide
  have hdescent : baseEnd_881688 < baseStart_881688 := by decide
  rcases family_descends (prefixWord ++ tailWord_881688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881698 : List Nat := [3, 3, 1, 1, 1, 4, 2, 3, 2]
def baseStart_881698 : Nat := 118140960795 + 881698 * 2 ^ 59
def prefixEnd_881698 : Nat := 4983230072969 + 3 ^ 40 * 881698 * 2
def baseEnd_881698 : Nat := 402430992095996965529023

theorem tailTrace_881698 : CollatzResearch.WordTrace tailWord_881698 prefixEnd_881698 402430992095996965529023 := by
  unfold tailWord_881698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8039541989941550718765437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21438778639844135250041165 8039541989941550718765437)
  ·
    refine ⟨3014828246228081519537039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8039541989941550718765437 3014828246228081519537039)
    ·
      refine ⟨4522242369342122279305559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3014828246228081519537039 4522242369342122279305559)
      ·
        refine ⟨6783363554013183418958339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4522242369342122279305559 6783363554013183418958339)
        ·
          refine ⟨10175045331019775128437509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6783363554013183418958339 10175045331019775128437509)
          ·
            refine ⟨1907820999566207836582033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10175045331019775128437509 1907820999566207836582033)
            ·
              refine ⟨1430865749674655877436525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1907820999566207836582033 1430865749674655877436525)
              ·
                refine ⟨536574656127995954038697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1430865749674655877436525 536574656127995954038697)
                ·
                  refine ⟨402430992095996965529023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536574656127995954038697 402430992095996965529023)
                  ·
                    rfl

theorem cell20_881698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_881698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881698 prefixEnd_881698 := by exact prefixLift 881698
  have htrace : WordTrace (prefixWord ++ tailWord_881698) baseStart_881698 baseEnd_881698 := by
    simpa [prefixWord, tailWord_881698, baseEnd_881698] using wordTrace_append hprefix tailTrace_881698
  have hstable : (prefixWord ++ tailWord_881698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881698).length < 2 ^ (prefixWord ++ tailWord_881698).sum := by decide
  have hdescent : baseEnd_881698 < baseStart_881698 := by decide
  rcases family_descends (prefixWord ++ tailWord_881698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881729 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_881729 : Nat := 118140960795 + 881729 * 2 ^ 59
def prefixEnd_881729 : Nat := 4983230072969 + 3 ^ 40 * 881729 * 2
def baseEnd_881729 : Nat := 402445141340698635495563

theorem tailTrace_881729 : CollatzResearch.WordTrace tailWord_881729 prefixEnd_881729 402445141340698635495563 := by
  unfold tailWord_881729
  simp only [CollatzResearch.WordTrace]
  refine ⟨32159298622653895169440241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21439532415102596779626827 32159298622653895169440241)
  ·
    refine ⟨24119473966990421377080181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32159298622653895169440241 24119473966990421377080181)
    ·
      refine ⟨2261200684405352004101267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24119473966990421377080181 2261200684405352004101267)
      ·
        refine ⟨3391801026608028006151901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261200684405352004101267 3391801026608028006151901)
        ·
          refine ⟨1271925384978010502306963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3391801026608028006151901 1271925384978010502306963)
          ·
            refine ⟨1907888077467015753460445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1271925384978010502306963 1907888077467015753460445)
            ·
              refine ⟨715458029050130907547667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1907888077467015753460445 715458029050130907547667)
              ·
                refine ⟨1073187043575196361321501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 715458029050130907547667 1073187043575196361321501)
                ·
                  refine ⟨402445141340698635495563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073187043575196361321501 402445141340698635495563)
                  ·
                    rfl

theorem cell20_881729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_881729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881729 prefixEnd_881729 := by exact prefixLift 881729
  have htrace : WordTrace (prefixWord ++ tailWord_881729) baseStart_881729 baseEnd_881729 := by
    simpa [prefixWord, tailWord_881729, baseEnd_881729] using wordTrace_append hprefix tailTrace_881729
  have hstable : (prefixWord ++ tailWord_881729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881729).length < 2 ^ (prefixWord ++ tailWord_881729).sum := by decide
  have hdescent : baseEnd_881729 < baseStart_881729 := by decide
  rcases family_descends (prefixWord ++ tailWord_881729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881761 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_881761 : Nat := 118140960795 + 881761 * 2 ^ 59
def prefixEnd_881761 : Nat := 4983230072969 + 3 ^ 40 * 881761 * 2
def baseEnd_881761 : Nat := 402459747012648746428765

theorem tailTrace_881761 : CollatzResearch.WordTrace tailWord_881761 prefixEnd_881761 402459747012648746428765 := by
  unfold tailWord_881761
  simp only [CollatzResearch.WordTrace]
  refine ⟨32160465758537964634605137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21440310505691976423070091 32160465758537964634605137)
  ·
    refine ⟨24120349318903473475953853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32160465758537964634605137 24120349318903473475953853)
    ·
      refine ⟨9045130994588802553482695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24120349318903473475953853 9045130994588802553482695)
      ·
        refine ⟨13567696491883203830224043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9045130994588802553482695 13567696491883203830224043)
        ·
          refine ⟨20351544737824805745336065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13567696491883203830224043 20351544737824805745336065)
          ·
            refine ⟨15263658553368604309002049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20351544737824805745336065 15263658553368604309002049)
            ·
              refine ⟨11447743915026453231751537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15263658553368604309002049 11447743915026453231751537)
              ·
                refine ⟨8585807936269839923813653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11447743915026453231751537 8585807936269839923813653)
                ·
                  refine ⟨402459747012648746428765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8585807936269839923813653 402459747012648746428765)
                  ·
                    rfl

theorem cell20_881761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_881761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881761 prefixEnd_881761 := by exact prefixLift 881761
  have htrace : WordTrace (prefixWord ++ tailWord_881761) baseStart_881761 baseEnd_881761 := by
    simpa [prefixWord, tailWord_881761, baseEnd_881761] using wordTrace_append hprefix tailTrace_881761
  have hstable : (prefixWord ++ tailWord_881761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881761).length < 2 ^ (prefixWord ++ tailWord_881761).sum := by decide
  have hdescent : baseEnd_881761 < baseStart_881761 := by decide
  rcases family_descends (prefixWord ++ tailWord_881761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881781 : List Nat := [1, 3, 4, 3, 1, 1, 2, 5]
def baseStart_881781 : Nat := 118140960795 + 881781 * 2 ^ 59
def prefixEnd_881781 : Nat := 4983230072969 + 3 ^ 40 * 881781 * 2
def baseEnd_881781 : Nat := 134156291852539188587339

theorem tailTrace_881781 : CollatzResearch.WordTrace tailWord_881781 prefixEnd_881781 134156291852539188587339 := by
  unfold tailWord_881781
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161195218465508050333197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21440796812310338700222131 32161195218465508050333197)
  ·
    refine ⟨12060448206924565518874949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32161195218465508050333197 12060448206924565518874949)
    ·
      refine ⟨2261334038798356034789053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12060448206924565518874949 2261334038798356034789053)
      ·
        refine ⟨848000264549383513045895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2261334038798356034789053 848000264549383513045895)
        ·
          refine ⟨1272000396824075269568843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848000264549383513045895 1272000396824075269568843)
          ·
            refine ⟨1908000595236112904353265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272000396824075269568843 1908000595236112904353265)
            ·
              refine ⟨1431000446427084678264949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908000595236112904353265 1431000446427084678264949)
              ·
                refine ⟨134156291852539188587339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431000446427084678264949 134156291852539188587339)
                ·
                  rfl

theorem cell20_881781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 5].length) (baseStart_881781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881781 prefixEnd_881781 := by exact prefixLift 881781
  have htrace : WordTrace (prefixWord ++ tailWord_881781) baseStart_881781 baseEnd_881781 := by
    simpa [prefixWord, tailWord_881781, baseEnd_881781] using wordTrace_append hprefix tailTrace_881781
  have hstable : (prefixWord ++ tailWord_881781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881781).length < 2 ^ (prefixWord ++ tailWord_881781).sum := by decide
  have hdescent : baseEnd_881781 < baseStart_881781 := by decide
  rcases family_descends (prefixWord ++ tailWord_881781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881799 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_881799 : Nat := 118140960795 + 881799 * 2 ^ 59
def prefixEnd_881799 : Nat := 4983230072969 + 3 ^ 40 * 881799 * 2
def baseEnd_881799 : Nat := 402477091248089503161943

theorem tailTrace_881799 : CollatzResearch.WordTrace tailWord_881799 prefixEnd_881799 402477091248089503161943 := by
  unfold tailWord_881799
  simp only [CollatzResearch.WordTrace]
  refine ⟨32161851732400297124488451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21441234488266864749658967 32161851732400297124488451)
  ·
    refine ⟨48242777598600445686732677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32161851732400297124488451 48242777598600445686732677)
    ·
      refine ⟨9045520799737583566262377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48242777598600445686732677 9045520799737583566262377)
      ·
        refine ⟨6784140599803187674696783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9045520799737583566262377 6784140599803187674696783)
        ·
          refine ⟨10176210899704781512045175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6784140599803187674696783 10176210899704781512045175)
          ·
            refine ⟨15264316349557172268067763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10176210899704781512045175 15264316349557172268067763)
            ·
              refine ⟨22896474524335758402101645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15264316349557172268067763 22896474524335758402101645)
              ·
                refine ⟨8586177946625909400788117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22896474524335758402101645 8586177946625909400788117)
                ·
                  refine ⟨402477091248089503161943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8586177946625909400788117 402477091248089503161943)
                  ·
                    rfl

theorem cell20_881799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_881799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881799 prefixEnd_881799 := by exact prefixLift 881799
  have htrace : WordTrace (prefixWord ++ tailWord_881799) baseStart_881799 baseEnd_881799 := by
    simpa [prefixWord, tailWord_881799, baseEnd_881799] using wordTrace_append hprefix tailTrace_881799
  have hstable : (prefixWord ++ tailWord_881799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881799).length < 2 ^ (prefixWord ++ tailWord_881799).sum := by decide
  have hdescent : baseEnd_881799 < baseStart_881799 := by decide
  rcases family_descends (prefixWord ++ tailWord_881799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881823 : List Nat := [1, 1, 2, 6, 2, 8]
def baseStart_881823 : Nat := 118140960795 + 881823 * 2 ^ 59
def prefixEnd_881823 : Nat := 4983230072969 + 3 ^ 40 * 881823 * 2
def baseEnd_881823 : Nat := 14906964648224151346735

theorem tailTrace_881823 : CollatzResearch.WordTrace tailWord_881823 prefixEnd_881823 14906964648224151346735 := by
  unfold tailWord_881823
  simp only [CollatzResearch.WordTrace]
  refine ⟨32162727084313349223362123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21441818056208899482241415 32162727084313349223362123)
  ·
    refine ⟨48244090626470023835043185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32162727084313349223362123 48244090626470023835043185)
    ·
      refine ⟨36183067969852517876282389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48244090626470023835043185 36183067969852517876282389)
      ·
        refine ⟨1696081311086836775450737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 36183067969852517876282389 1696081311086836775450737)
        ·
          refine ⟨1272060983315127581588053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696081311086836775450737 1272060983315127581588053)
          ·
            refine ⟨14906964648224151346735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1272060983315127581588053 14906964648224151346735)
            ·
              rfl

theorem cell20_881823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 8].length) (baseStart_881823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881823 prefixEnd_881823 := by exact prefixLift 881823
  have htrace : WordTrace (prefixWord ++ tailWord_881823) baseStart_881823 baseEnd_881823 := by
    simpa [prefixWord, tailWord_881823, baseEnd_881823] using wordTrace_append hprefix tailTrace_881823
  have hstable : (prefixWord ++ tailWord_881823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881823).length < 2 ^ (prefixWord ++ tailWord_881823).sum := by decide
  have hdescent : baseEnd_881823 < baseStart_881823 := by decide
  rcases family_descends (prefixWord ++ tailWord_881823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881854 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_881854 : Nat := 118140960795 + 881854 * 2 ^ 59
def prefixEnd_881854 : Nat := 4983230072969 + 3 ^ 40 * 881854 * 2
def baseEnd_881854 : Nat := 402502194746753756328385

theorem tailTrace_881854 : CollatzResearch.WordTrace tailWord_881854 prefixEnd_881854 402502194746753756328385 := by
  unfold tailWord_881854
  simp only [CollatzResearch.WordTrace]
  refine ⟨4020482218400130189717577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21442571831467361011827077 4020482218400130189717577)
  ·
    refine ⟨3015361663800097642288183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4020482218400130189717577 3015361663800097642288183)
    ·
      refine ⟨4523042495700146463432275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015361663800097642288183 4523042495700146463432275)
      ·
        refine ⟨6784563743550219695148413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523042495700146463432275 6784563743550219695148413)
        ·
          refine ⟨2544211403831332385680655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6784563743550219695148413 2544211403831332385680655)
          ·
            refine ⟨3816317105746998578520983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2544211403831332385680655 3816317105746998578520983)
            ·
              refine ⟨5724475658620497867781475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3816317105746998578520983 5724475658620497867781475)
              ·
                refine ⟨8586713487930746801672213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5724475658620497867781475 8586713487930746801672213)
                ·
                  refine ⟨402502194746753756328385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8586713487930746801672213 402502194746753756328385)
                  ·
                    rfl

theorem cell20_881854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_881854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881854 prefixEnd_881854 := by exact prefixLift 881854
  have htrace : WordTrace (prefixWord ++ tailWord_881854) baseStart_881854 baseEnd_881854 := by
    simpa [prefixWord, tailWord_881854, baseEnd_881854] using wordTrace_append hprefix tailTrace_881854
  have hstable : (prefixWord ++ tailWord_881854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881854).length < 2 ^ (prefixWord ++ tailWord_881854).sum := by decide
  have hdescent : baseEnd_881854 < baseStart_881854 := by decide
  rcases family_descends (prefixWord ++ tailWord_881854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881857 : List Nat := [1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_881857 : Nat := 118140960795 + 881857 * 2 ^ 59
def prefixEnd_881857 : Nat := 4983230072969 + 3 ^ 40 * 881857 * 2
def baseEnd_881857 : Nat := 134167854676166359742791

theorem tailTrace_881857 : CollatzResearch.WordTrace tailWord_881857 prefixEnd_881857 134167854676166359742791 := by
  unfold tailWord_881857
  simp only [CollatzResearch.WordTrace]
  refine ⟨32163967166190173030099825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21442644777460115353399883 32163967166190173030099825)
  ·
    refine ⟨24122975374642629772574869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32163967166190173030099825 24122975374642629772574869)
    ·
      refine ⟨1130764470686373270589447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24122975374642629772574869 1130764470686373270589447)
      ·
        refine ⟨1696146706029559905884171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130764470686373270589447 1696146706029559905884171)
        ·
          refine ⟨2544220059044339858826257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696146706029559905884171 2544220059044339858826257)
          ·
            refine ⟨1908165044283254894119693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544220059044339858826257 1908165044283254894119693)
            ·
              refine ⟨715561891606220585294885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1908165044283254894119693 715561891606220585294885)
              ·
                refine ⟨134167854676166359742791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715561891606220585294885 134167854676166359742791)
                ·
                  rfl

theorem cell20_881857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_881857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881857 prefixEnd_881857 := by exact prefixLift 881857
  have htrace : WordTrace (prefixWord ++ tailWord_881857) baseStart_881857 baseEnd_881857 := by
    simpa [prefixWord, tailWord_881857, baseEnd_881857] using wordTrace_append hprefix tailTrace_881857
  have hstable : (prefixWord ++ tailWord_881857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881857).length < 2 ^ (prefixWord ++ tailWord_881857).sum := by decide
  have hdescent : baseEnd_881857 < baseStart_881857 := by decide
  rcases family_descends (prefixWord ++ tailWord_881857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881908 : List Nat := [2, 6, 1, 2, 2, 1, 2, 4]
def baseStart_881908 : Nat := 118140960795 + 881908 * 2 ^ 59
def prefixEnd_881908 : Nat := 4983230072969 + 3 ^ 40 * 881908 * 2
def baseEnd_881908 : Nat := 134175613939389856176055

theorem tailTrace_881908 : CollatzResearch.WordTrace tailWord_881908 prefixEnd_881908 134175613939389856176055 := by
  unfold tailWord_881908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16082913644502704370103189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21443884859336939160137585 16082913644502704370103189)
  ·
    refine ⟨753886577086064267348587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16082913644502704370103189 753886577086064267348587)
    ·
      refine ⟨1130829865629096401022881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753886577086064267348587 1130829865629096401022881)
      ·
        refine ⟨848122399221822300767161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1130829865629096401022881 848122399221822300767161)
        ·
          refine ⟨636091799416366725575371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848122399221822300767161 636091799416366725575371)
          ·
            refine ⟨954137699124550088363057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636091799416366725575371 954137699124550088363057)
            ·
              refine ⟨715603274343412566272293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954137699124550088363057 715603274343412566272293)
              ·
                refine ⟨134175613939389856176055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715603274343412566272293 134175613939389856176055)
                ·
                  rfl

theorem cell20_881908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 4].length) (baseStart_881908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881908 prefixEnd_881908 := by exact prefixLift 881908
  have htrace : WordTrace (prefixWord ++ tailWord_881908) baseStart_881908 baseEnd_881908 := by
    simpa [prefixWord, tailWord_881908, baseEnd_881908] using wordTrace_append hprefix tailTrace_881908
  have hstable : (prefixWord ++ tailWord_881908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881908).length < 2 ^ (prefixWord ++ tailWord_881908).sum := by decide
  have hdescent : baseEnd_881908 < baseStart_881908 := by decide
  rcases family_descends (prefixWord ++ tailWord_881908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881913 : List Nat := [1, 2, 1, 3, 1, 1, 3, 4, 4]
def baseStart_881913 : Nat := 118140960795 + 881913 * 2 ^ 59
def prefixEnd_881913 : Nat := 4983230072969 + 3 ^ 40 * 881913 * 2
def baseEnd_881913 : Nat := 402529123954411773361477

theorem tailTrace_881913 : CollatzResearch.WordTrace tailWord_881913 prefixEnd_881913 402529123954411773361477 := by
  unfold tailWord_881913
  simp only [CollatzResearch.WordTrace]
  refine ⟨32166009653987294594138393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21444006435991529729425595 32166009653987294594138393)
  ·
    refine ⟨24124507240490470945603795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32166009653987294594138393 24124507240490470945603795)
    ·
      refine ⟨36186760860735706418405693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24124507240490470945603795 36186760860735706418405693)
      ·
        refine ⟨13570035322775889906902135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36186760860735706418405693 13570035322775889906902135)
        ·
          refine ⟨20355052984163834860353203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13570035322775889906902135 20355052984163834860353203)
          ·
            refine ⟨30532579476245752290529805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20355052984163834860353203 30532579476245752290529805)
            ·
              refine ⟨11449717303592157108948677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30532579476245752290529805 11449717303592157108948677)
              ·
                refine ⟨2146821994423529457927877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11449717303592157108948677 2146821994423529457927877)
                ·
                  refine ⟨402529123954411773361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2146821994423529457927877 402529123954411773361477)
                  ·
                    rfl

theorem cell20_881913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_881913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881913 prefixEnd_881913 := by exact prefixLift 881913
  have htrace : WordTrace (prefixWord ++ tailWord_881913) baseStart_881913 baseEnd_881913 := by
    simpa [prefixWord, tailWord_881913, baseEnd_881913] using wordTrace_append hprefix tailTrace_881913
  have hstable : (prefixWord ++ tailWord_881913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881913).length < 2 ^ (prefixWord ++ tailWord_881913).sum := by decide
  have hdescent : baseEnd_881913 < baseStart_881913 := by decide
  rcases family_descends (prefixWord ++ tailWord_881913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881922 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 2]
def baseStart_881922 : Nat := 118140960795 + 881922 * 2 ^ 59
def prefixEnd_881922 : Nat := 4983230072969 + 3 ^ 40 * 881922 * 2
def baseEnd_881922 : Nat := 402533231799647742061441

theorem tailTrace_881922 : CollatzResearch.WordTrace tailWord_881922 prefixEnd_881922 402533231799647742061441 := by
  unfold tailWord_881922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041584477738672282804005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21444225273969792754144013 8041584477738672282804005)
  ·
    refine ⟨1507797089576001053025751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8041584477738672282804005 1507797089576001053025751)
    ·
      refine ⟨2261695634364001579538627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1507797089576001053025751 2261695634364001579538627)
      ·
        refine ⟨3392543451546002369307941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2261695634364001579538627 3392543451546002369307941)
        ·
          refine ⟨636101897164875444245239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3392543451546002369307941 636101897164875444245239)
          ·
            refine ⟨954152845747313166367859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636101897164875444245239 954152845747313166367859)
            ·
              refine ⟨1431229268620969749551789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954152845747313166367859 1431229268620969749551789)
              ·
                refine ⟨536710975732863656081921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431229268620969749551789 536710975732863656081921)
                ·
                  refine ⟨402533231799647742061441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536710975732863656081921 402533231799647742061441)
                  ·
                    rfl

theorem cell20_881922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_881922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881922 prefixEnd_881922 := by exact prefixLift 881922
  have htrace : WordTrace (prefixWord ++ tailWord_881922) baseStart_881922 baseEnd_881922 := by
    simpa [prefixWord, tailWord_881922, baseEnd_881922] using wordTrace_append hprefix tailTrace_881922
  have hstable : (prefixWord ++ tailWord_881922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881922).length < 2 ^ (prefixWord ++ tailWord_881922).sum := by decide
  have hdescent : baseEnd_881922 < baseStart_881922 := by decide
  rcases family_descends (prefixWord ++ tailWord_881922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881944 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 5]
def baseStart_881944 : Nat := 118140960795 + 881944 * 2 ^ 59
def prefixEnd_881944 : Nat := 4983230072969 + 3 ^ 40 * 881944 * 2
def baseEnd_881944 : Nat := 402543273199113443328017

theorem tailTrace_881944 : CollatzResearch.WordTrace tailWord_881944 prefixEnd_881944 402543273199113443328017 := by
  unfold tailWord_881944
  simp only [CollatzResearch.WordTrace]
  refine ⟨16083570158437493444258443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21444760211249991259011257 16083570158437493444258443)
  ·
    refine ⟨24125355237656240166387665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16083570158437493444258443 24125355237656240166387665)
    ·
      refine ⟨18094016428242180124790749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24125355237656240166387665 18094016428242180124790749)
      ·
        refine ⟨6785256160590817546796531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18094016428242180124790749 6785256160590817546796531)
        ·
          refine ⟨10177884240886226320194797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6785256160590817546796531 10177884240886226320194797)
          ·
            refine ⟨3816706590332334870073049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10177884240886226320194797 3816706590332334870073049)
            ·
              refine ⟨2862529942749251152554787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3816706590332334870073049 2862529942749251152554787)
              ·
                refine ⟨4293794914123876728832181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2862529942749251152554787 4293794914123876728832181)
                ·
                  refine ⟨402543273199113443328017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4293794914123876728832181 402543273199113443328017)
                  ·
                    rfl

theorem cell20_881944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5].length) (baseStart_881944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881944 prefixEnd_881944 := by exact prefixLift 881944
  have htrace : WordTrace (prefixWord ++ tailWord_881944) baseStart_881944 baseEnd_881944 := by
    simpa [prefixWord, tailWord_881944, baseEnd_881944] using wordTrace_append hprefix tailTrace_881944
  have hstable : (prefixWord ++ tailWord_881944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881944).length < 2 ^ (prefixWord ++ tailWord_881944).sum := by decide
  have hdescent : baseEnd_881944 < baseStart_881944 := by decide
  rcases family_descends (prefixWord ++ tailWord_881944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881954 : List Nat := [3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_881954 : Nat := 118140960795 + 881954 * 2 ^ 59
def prefixEnd_881954 : Nat := 4983230072969 + 3 ^ 40 * 881954 * 2
def baseEnd_881954 : Nat := 134182612490532617664881

theorem tailTrace_881954 : CollatzResearch.WordTrace tailWord_881954 prefixEnd_881954 134182612490532617664881 := by
  unfold tailWord_881954
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041876261709689649095229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21445003364559172397587277 8041876261709689649095229)
  ·
    refine ⟨3015703598141133618410711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8041876261709689649095229 3015703598141133618410711)
    ·
      refine ⟨4523555397211700427616067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015703598141133618410711 4523555397211700427616067)
      ·
        refine ⟨6785333095817550641424101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4523555397211700427616067 6785333095817550641424101)
        ·
          refine ⟨1272249955465790745267019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6785333095817550641424101 1272249955465790745267019)
          ·
            refine ⟨1908374933198686117900529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1272249955465790745267019 1908374933198686117900529)
            ·
              refine ⟨1431281199899014588425397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1908374933198686117900529 1431281199899014588425397)
              ·
                refine ⟨134182612490532617664881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1431281199899014588425397 134182612490532617664881)
                ·
                  rfl

theorem cell20_881954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_881954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881954 prefixEnd_881954 := by exact prefixLift 881954
  have htrace : WordTrace (prefixWord ++ tailWord_881954) baseStart_881954 baseEnd_881954 := by
    simpa [prefixWord, tailWord_881954, baseEnd_881954] using wordTrace_append hprefix tailTrace_881954
  have hstable : (prefixWord ++ tailWord_881954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881954).length < 2 ^ (prefixWord ++ tailWord_881954).sum := by decide
  have hdescent : baseEnd_881954 < baseStart_881954 := by decide
  rcases family_descends (prefixWord ++ tailWord_881954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_881996 : List Nat := [2, 2, 1, 3, 2, 10]
def baseStart_881996 : Nat := 118140960795 + 881996 * 2 ^ 59
def prefixEnd_881996 : Nat := 4983230072969 + 3 ^ 40 * 881996 * 2
def baseEnd_881996 : Nat := 14909889163556754577573

theorem tailTrace_881996 : CollatzResearch.WordTrace tailWord_881996 prefixEnd_881996 14909889163556754577573 := by
  unfold tailWord_881996
  simp only [CollatzResearch.WordTrace]
  refine ⟨16084518456343299884704921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21446024608457733179606561 16084518456343299884704921)
  ·
    refine ⟨12063388842257474913528691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16084518456343299884704921 12063388842257474913528691)
    ·
      refine ⟨18095083263386212370293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12063388842257474913528691 18095083263386212370293037)
      ·
        refine ⟨6785656223769829638859889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18095083263386212370293037 6785656223769829638859889)
        ·
          refine ⟨5089242167827372229144917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6785656223769829638859889 5089242167827372229144917)
          ·
            refine ⟨14909889163556754577573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5089242167827372229144917 14909889163556754577573)
            ·
              rfl

theorem cell20_881996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 10].length) (baseStart_881996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_881996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_881996 prefixEnd_881996 := by exact prefixLift 881996
  have htrace : WordTrace (prefixWord ++ tailWord_881996) baseStart_881996 baseEnd_881996 := by
    simpa [prefixWord, tailWord_881996, baseEnd_881996] using wordTrace_append hprefix tailTrace_881996
  have hstable : (prefixWord ++ tailWord_881996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_881996).length < 2 ^ (prefixWord ++ tailWord_881996).sum := by decide
  have hdescent : baseEnd_881996 < baseStart_881996 := by decide
  rcases family_descends (prefixWord ++ tailWord_881996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882082 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_882082 : Nat := 118140960795 + 882082 * 2 ^ 59
def prefixEnd_882082 : Nat := 4983230072969 + 3 ^ 40 * 882082 * 2
def baseEnd_882082 : Nat := 402606260159398296727453

theorem tailTrace_882082 : CollatzResearch.WordTrace tailWord_882082 prefixEnd_882082 402606260159398296727453 := by
  unfold tailWord_882082
  simp only [CollatzResearch.WordTrace]
  refine ⟨8043043397593759114260125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21448115726916690971360333 8043043397593759114260125)
  ·
    refine ⟨3016141274097659667847547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8043043397593759114260125 3016141274097659667847547)
    ·
      refine ⟨4524211911146489501771321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3016141274097659667847547 4524211911146489501771321)
      ·
        refine ⟨3393158933359867126328491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4524211911146489501771321 3393158933359867126328491)
        ·
          refine ⟨5089738400039800689492737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3393158933359867126328491 5089738400039800689492737)
          ·
            refine ⟨3817303800029850517119553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5089738400039800689492737 3817303800029850517119553)
            ·
              refine ⟨2862977850022387887839665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3817303800029850517119553 2862977850022387887839665)
              ·
                refine ⟨2147233387516790915879749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2862977850022387887839665 2147233387516790915879749)
                ·
                  refine ⟨402606260159398296727453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2147233387516790915879749 402606260159398296727453)
                  ·
                    rfl

theorem cell20_882082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_882082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882082 prefixEnd_882082 := by exact prefixLift 882082
  have htrace : WordTrace (prefixWord ++ tailWord_882082) baseStart_882082 baseEnd_882082 := by
    simpa [prefixWord, tailWord_882082, baseEnd_882082] using wordTrace_append hprefix tailTrace_882082
  have hstable : (prefixWord ++ tailWord_882082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882082).length < 2 ^ (prefixWord ++ tailWord_882082).sum := by decide
  have hdescent : baseEnd_882082 < baseStart_882082 := by decide
  rcases family_descends (prefixWord ++ tailWord_882082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882155 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_882155 : Nat := 118140960795 + 882155 * 2 ^ 59
def prefixEnd_882155 : Nat := 4983230072969 + 3 ^ 40 * 882155 * 2
def baseEnd_882155 : Nat := 402639579348534487293821

theorem tailTrace_882155 : CollatzResearch.WordTrace tailWord_882155 prefixEnd_882155 402639579348534487293821 := by
  unfold tailWord_882155
  simp only [CollatzResearch.WordTrace]
  refine ⟨32174836119110569924447919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21449890746073713282965279 32174836119110569924447919)
  ·
    refine ⟨48262254178665854886671879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32174836119110569924447919 48262254178665854886671879)
    ·
      refine ⟨72393381267998782330007819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48262254178665854886671879 72393381267998782330007819)
      ·
        refine ⟨108590071901998173495011729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 72393381267998782330007819 108590071901998173495011729)
        ·
          refine ⟨81442553926498630121258797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 108590071901998173495011729 81442553926498630121258797)
          ·
            refine ⟨30540957722436986295472049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 81442553926498630121258797 30540957722436986295472049)
            ·
              refine ⟨22905718291827739721604037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30540957722436986295472049 22905718291827739721604037)
              ·
                refine ⟨4294822179717701197800757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22905718291827739721604037 4294822179717701197800757)
                ·
                  refine ⟨402639579348534487293821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4294822179717701197800757 402639579348534487293821)
                  ·
                    rfl

theorem cell20_882155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_882155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882155 prefixEnd_882155 := by exact prefixLift 882155
  have htrace : WordTrace (prefixWord ++ tailWord_882155) baseStart_882155 baseEnd_882155 := by
    simpa [prefixWord, tailWord_882155, baseEnd_882155] using wordTrace_append hprefix tailTrace_882155
  have hstable : (prefixWord ++ tailWord_882155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882155).length < 2 ^ (prefixWord ++ tailWord_882155).sum := by decide
  have hdescent : baseEnd_882155 < baseStart_882155 := by decide
  rcases family_descends (prefixWord ++ tailWord_882155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882165 : List Nat := [1, 3, 5, 1, 1, 9]
def baseStart_882165 : Nat := 118140960795 + 882165 * 2 ^ 59
def prefixEnd_882165 : Nat := 4983230072969 + 3 ^ 40 * 882165 * 2
def baseEnd_882165 : Nat := 14912746060037736924461

theorem tailTrace_882165 : CollatzResearch.WordTrace tailWord_882165 prefixEnd_882165 14912746060037736924461 := by
  unfold tailWord_882165
  simp only [CollatzResearch.WordTrace]
  refine ⟨32175200849074341632311949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21450133899382894421541299 32175200849074341632311949)
  ·
    refine ⟨12065700318402878112116981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32175200849074341632311949 12065700318402878112116981)
    ·
      refine ⟨1131159404850269823010967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12065700318402878112116981 1131159404850269823010967)
      ·
        refine ⟨1696739107275404734516451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131159404850269823010967 1696739107275404734516451)
        ·
          refine ⟨2545108660913107101774677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696739107275404734516451 2545108660913107101774677)
          ·
            refine ⟨14912746060037736924461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2545108660913107101774677 14912746060037736924461)
            ·
              rfl

theorem cell20_882165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 9].length) (baseStart_882165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882165 prefixEnd_882165 := by exact prefixLift 882165
  have htrace : WordTrace (prefixWord ++ tailWord_882165) baseStart_882165 baseEnd_882165 := by
    simpa [prefixWord, tailWord_882165, baseEnd_882165] using wordTrace_append hprefix tailTrace_882165
  have hstable : (prefixWord ++ tailWord_882165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882165).length < 2 ^ (prefixWord ++ tailWord_882165).sum := by decide
  have hdescent : baseEnd_882165 < baseStart_882165 := by decide
  rcases family_descends (prefixWord ++ tailWord_882165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882172 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_882172 : Nat := 118140960795 + 882172 * 2 ^ 59
def prefixEnd_882172 : Nat := 4983230072969 + 3 ^ 40 * 882172 * 2
def baseEnd_882172 : Nat := 402647338611757983727085

theorem tailTrace_882172 : CollatzResearch.WordTrace tailWord_882172 prefixEnd_882172 402647338611757983727085 := by
  unfold tailWord_882172
  simp only [CollatzResearch.WordTrace]
  refine ⟨16087728080024490913908385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21450304106699321218544513 16087728080024490913908385)
  ·
    refine ⟨12065796060018368185431289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16087728080024490913908385 12065796060018368185431289)
    ·
      refine ⟨9049347045013776139073467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12065796060018368185431289 9049347045013776139073467)
      ·
        refine ⟨13574020567520664208610201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9049347045013776139073467 13574020567520664208610201)
        ·
          refine ⟨10180515425640498156457651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13574020567520664208610201 10180515425640498156457651)
          ·
            refine ⟨15270773138460747234686477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10180515425640498156457651 15270773138460747234686477)
            ·
              refine ⟨5726539926922780213007429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15270773138460747234686477 5726539926922780213007429)
              ·
                refine ⟨1073726236298021289938893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5726539926922780213007429 1073726236298021289938893)
                ·
                  refine ⟨402647338611757983727085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073726236298021289938893 402647338611757983727085)
                  ·
                    rfl

theorem cell20_882172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_882172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882172 prefixEnd_882172 := by exact prefixLift 882172
  have htrace : WordTrace (prefixWord ++ tailWord_882172) baseStart_882172 baseEnd_882172 := by
    simpa [prefixWord, tailWord_882172, baseEnd_882172] using wordTrace_append hprefix tailTrace_882172
  have hstable : (prefixWord ++ tailWord_882172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882172).length < 2 ^ (prefixWord ++ tailWord_882172).sum := by decide
  have hdescent : baseEnd_882172 < baseStart_882172 := by decide
  rcases family_descends (prefixWord ++ tailWord_882172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882227 : List Nat := [1, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_882227 : Nat := 118140960795 + 882227 * 2 ^ 59
def prefixEnd_882227 : Nat := 4983230072969 + 3 ^ 40 * 882227 * 2
def baseEnd_882227 : Nat := 402672442110422236893527

theorem tailTrace_882227 : CollatzResearch.WordTrace tailWord_882227 prefixEnd_882227 402672442110422236893527 := by
  unfold tailWord_882227
  simp only [CollatzResearch.WordTrace]
  refine ⟨32177462174849726221068935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21451641449899817480712623 32177462174849726221068935)
  ·
    refine ⟨48266193262274589331603403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32177462174849726221068935 48266193262274589331603403)
    ·
      refine ⟨72399289893411883997405105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48266193262274589331603403 72399289893411883997405105)
      ·
        refine ⟨54299467420058912998053829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 72399289893411883997405105 54299467420058912998053829)
        ·
          refine ⟨10181150141261046187135093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 54299467420058912998053829 10181150141261046187135093)
          ·
            refine ⟨954482825743223080043915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10181150141261046187135093 954482825743223080043915)
            ·
              refine ⟨1431724238614834620065873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954482825743223080043915 1431724238614834620065873)
              ·
                refine ⟨1073793178961125965049405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1431724238614834620065873 1073793178961125965049405)
                ·
                  refine ⟨402672442110422236893527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073793178961125965049405 402672442110422236893527)
                  ·
                    rfl

theorem cell20_882227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_882227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882227 prefixEnd_882227 := by exact prefixLift 882227
  have htrace : WordTrace (prefixWord ++ tailWord_882227) baseStart_882227 baseEnd_882227 := by
    simpa [prefixWord, tailWord_882227, baseEnd_882227] using wordTrace_append hprefix tailTrace_882227
  have hstable : (prefixWord ++ tailWord_882227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882227).length < 2 ^ (prefixWord ++ tailWord_882227).sum := by decide
  have hdescent : baseEnd_882227 < baseStart_882227 := by decide
  rcases family_descends (prefixWord ++ tailWord_882227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882234 : List Nat := [3, 1, 1, 1, 3, 2, 1, 6, 2]
def baseStart_882234 : Nat := 118140960795 + 882234 * 2 ^ 59
def prefixEnd_882234 : Nat := 4983230072969 + 3 ^ 40 * 882234 * 2
def baseEnd_882234 : Nat := 402675637101161323660165

theorem tailTrace_882234 : CollatzResearch.WordTrace tailWord_882234 prefixEnd_882234 402675637101161323660165 := by
  unfold tailWord_882234
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044429371456091604143439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21451811657216244277715837 8044429371456091604143439)
  ·
    refine ⟨12066644057184137406215159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8044429371456091604143439 12066644057184137406215159)
    ·
      refine ⟨18099966085776206109322739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12066644057184137406215159 18099966085776206109322739)
      ·
        refine ⟨27149949128664309163984109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18099966085776206109322739 27149949128664309163984109)
        ·
          refine ⟨10181230923249115936494041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27149949128664309163984109 10181230923249115936494041)
          ·
            refine ⟨7635923192436836952370531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10181230923249115936494041 7635923192436836952370531)
            ·
              refine ⟨11453884788655255428555797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7635923192436836952370531 11453884788655255428555797)
              ·
                refine ⟨536900849468215098213553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11453884788655255428555797 536900849468215098213553)
                ·
                  refine ⟨402675637101161323660165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536900849468215098213553 402675637101161323660165)
                  ·
                    rfl

theorem cell20_882234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_882234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882234 prefixEnd_882234 := by exact prefixLift 882234
  have htrace : WordTrace (prefixWord ++ tailWord_882234) baseStart_882234 baseEnd_882234 := by
    simpa [prefixWord, tailWord_882234, baseEnd_882234] using wordTrace_append hprefix tailTrace_882234
  have hstable : (prefixWord ++ tailWord_882234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882234).length < 2 ^ (prefixWord ++ tailWord_882234).sum := by decide
  have hdescent : baseEnd_882234 < baseStart_882234 := by decide
  rcases family_descends (prefixWord ++ tailWord_882234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882258 : List Nat := [3, 2, 2, 1, 2, 4, 2, 4]
def baseStart_882258 : Nat := 118140960795 + 882258 * 2 ^ 59
def prefixEnd_882258 : Nat := 4983230072969 + 3 ^ 40 * 882258 * 2
def baseEnd_882258 : Nat := 134228863785041302286689

theorem tailTrace_882258 : CollatzResearch.WordTrace tailWord_882258 prefixEnd_882258 134228863785041302286689 := by
  unfold tailWord_882258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8044648209434354628861857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21452395225158279010298285 8044648209434354628861857)
  ·
    refine ⟨6033486157075765971646393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8044648209434354628861857 6033486157075765971646393)
    ·
      refine ⟨4525114617806824478734795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6033486157075765971646393 4525114617806824478734795)
      ·
        refine ⟨6787671926710236718102193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525114617806824478734795 6787671926710236718102193)
        ·
          refine ⟨5090753945032677538576645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6787671926710236718102193 5090753945032677538576645)
          ·
            refine ⟨954516364693627038483121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5090753945032677538576645 954516364693627038483121)
            ·
              refine ⟨715887273520220278862341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954516364693627038483121 715887273520220278862341)
              ·
                refine ⟨134228863785041302286689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 715887273520220278862341 134228863785041302286689)
                ·
                  rfl

theorem cell20_882258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_882258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882258 prefixEnd_882258 := by exact prefixLift 882258
  have htrace : WordTrace (prefixWord ++ tailWord_882258) baseStart_882258 baseEnd_882258 := by
    simpa [prefixWord, tailWord_882258, baseEnd_882258] using wordTrace_append hprefix tailTrace_882258
  have hstable : (prefixWord ++ tailWord_882258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882258).length < 2 ^ (prefixWord ++ tailWord_882258).sum := by decide
  have hdescent : baseEnd_882258 < baseStart_882258 := by decide
  rcases family_descends (prefixWord ++ tailWord_882258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882268 : List Nat := [2, 2, 4, 1, 2, 3, 1, 3, 2]
def baseStart_882268 : Nat := 118140960795 + 882268 * 2 ^ 59
def prefixEnd_882268 : Nat := 4983230072969 + 3 ^ 40 * 882268 * 2
def baseEnd_882268 : Nat := 402691155627608316526693

theorem tailTrace_882268 : CollatzResearch.WordTrace tailWord_882268 prefixEnd_882268 402691155627608316526693 := by
  unfold tailWord_882268
  simp only [CollatzResearch.WordTrace]
  refine ⟨16089478783850595111655729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21452638378467460148874305 16089478783850595111655729)
  ·
    refine ⟨12067109087887946333741797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16089478783850595111655729 12067109087887946333741797)
    ·
      refine ⟨2262582953978989937576587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12067109087887946333741797 2262582953978989937576587)
      ·
        refine ⟨3393874430968484906364881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2262582953978989937576587 3393874430968484906364881)
        ·
          refine ⟨2545405823226363679773661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3393874430968484906364881 2545405823226363679773661)
          ·
            refine ⟨954527183709886379915123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2545405823226363679773661 954527183709886379915123)
            ·
              refine ⟨1431790775564829569872685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954527183709886379915123 1431790775564829569872685)
              ·
                refine ⟨536921540836811088702257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1431790775564829569872685 536921540836811088702257)
                ·
                  refine ⟨402691155627608316526693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 536921540836811088702257 402691155627608316526693)
                  ·
                    rfl

theorem cell20_882268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_882268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882268 prefixEnd_882268 := by exact prefixLift 882268
  have htrace : WordTrace (prefixWord ++ tailWord_882268) baseStart_882268 baseEnd_882268 := by
    simpa [prefixWord, tailWord_882268, baseEnd_882268] using wordTrace_append hprefix tailTrace_882268
  have hstable : (prefixWord ++ tailWord_882268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882268).length < 2 ^ (prefixWord ++ tailWord_882268).sum := by decide
  have hdescent : baseEnd_882268 < baseStart_882268 := by decide
  rcases family_descends (prefixWord ++ tailWord_882268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882358 : List Nat := [5, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_882358 : Nat := 118140960795 + 882358 * 2 ^ 59
def prefixEnd_882358 : Nat := 4983230072969 + 3 ^ 40 * 882358 * 2
def baseEnd_882358 : Nat := 402732234079968003526325

theorem tailTrace_882358 : CollatzResearch.WordTrace tailWord_882358 prefixEnd_882358 402732234079968003526325 := by
  unfold tailWord_882358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011390008585945974630483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21454826758250090396058485 2011390008585945974630483)
  ·
    refine ⟨3017085012878918961945725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2011390008585945974630483 3017085012878918961945725)
    ·
      refine ⟨1131406879829594610729647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3017085012878918961945725 1131406879829594610729647)
      ·
        refine ⟨1697110319744391916094471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131406879829594610729647 1697110319744391916094471)
        ·
          refine ⟨2545665479616587874141707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697110319744391916094471 2545665479616587874141707)
          ·
            refine ⟨3818498219424881811212561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2545665479616587874141707 3818498219424881811212561)
            ·
              refine ⟨2863873664568661358409421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818498219424881811212561 2863873664568661358409421)
              ·
                refine ⟨1073952624213248009403533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863873664568661358409421 1073952624213248009403533)
                ·
                  refine ⟨402732234079968003526325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073952624213248009403533 402732234079968003526325)
                  ·
                    rfl

theorem cell20_882358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_882358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882358 prefixEnd_882358 := by exact prefixLift 882358
  have htrace : WordTrace (prefixWord ++ tailWord_882358) baseStart_882358 baseEnd_882358 := by
    simpa [prefixWord, tailWord_882358, baseEnd_882358] using wordTrace_append hprefix tailTrace_882358
  have hstable : (prefixWord ++ tailWord_882358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882358).length < 2 ^ (prefixWord ++ tailWord_882358).sum := by decide
  have hdescent : baseEnd_882358 < baseStart_882358 := by decide
  rcases family_descends (prefixWord ++ tailWord_882358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882362 : List Nat := [3, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_882362 : Nat := 118140960795 + 882362 * 2 ^ 59
def prefixEnd_882362 : Nat := 4983230072969 + 3 ^ 40 * 882362 * 2
def baseEnd_882362 : Nat := 402734059788961767392975

theorem tailTrace_882362 : CollatzResearch.WordTrace tailWord_882362 prefixEnd_882362 402734059788961767392975 := by
  unfold tailWord_882362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8045596507340161069308335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21454924019573762851488893 8045596507340161069308335)
  ·
    refine ⟨12068394761010241603962503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8045596507340161069308335 12068394761010241603962503)
    ·
      refine ⟨18102592141515362405943755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12068394761010241603962503 18102592141515362405943755)
      ·
        refine ⟨27153888212273043608915633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18102592141515362405943755 27153888212273043608915633)
        ·
          refine ⟨20365416159204782706686725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27153888212273043608915633 20365416159204782706686725)
          ·
            refine ⟨3818515529850896757503761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20365416159204782706686725 3818515529850896757503761)
            ·
              refine ⟨2863886647388172568127821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3818515529850896757503761 2863886647388172568127821)
              ·
                refine ⟨1073957492770564713047933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2863886647388172568127821 1073957492770564713047933)
                ·
                  refine ⟨402734059788961767392975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1073957492770564713047933 402734059788961767392975)
                  ·
                    rfl

theorem cell20_882362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_882362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882362 prefixEnd_882362 := by exact prefixLift 882362
  have htrace : WordTrace (prefixWord ++ tailWord_882362) baseStart_882362 baseEnd_882362 := by
    simpa [prefixWord, tailWord_882362, baseEnd_882362] using wordTrace_append hprefix tailTrace_882362
  have hstable : (prefixWord ++ tailWord_882362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882362).length < 2 ^ (prefixWord ++ tailWord_882362).sum := by decide
  have hdescent : baseEnd_882362 < baseStart_882362 := by decide
  rcases family_descends (prefixWord ++ tailWord_882362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882400 : List Nat := [2, 1, 1, 3, 1, 2, 5, 2, 3]
def baseStart_882400 : Nat := 118140960795 + 882400 * 2 ^ 59
def prefixEnd_882400 : Nat := 4983230072969 + 3 ^ 40 * 882400 * 2
def baseEnd_882400 : Nat := 402751404024402524126153

theorem tailTrace_882400 : CollatzResearch.WordTrace tailWord_882400 prefixEnd_882400 402751404024402524126153 := by
  unfold tailWord_882400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16091886001611488383558327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21455848002148651178077769 16091886001611488383558327)
  ·
    refine ⟨24137829002417232575337491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16091886001611488383558327 24137829002417232575337491)
    ·
      refine ⟨36206743503625848863006237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24137829002417232575337491 36206743503625848863006237)
      ·
        refine ⟨13577528813859693323627339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36206743503625848863006237 13577528813859693323627339)
        ·
          refine ⟨20366293220789539985441009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13577528813859693323627339 20366293220789539985441009)
          ·
            refine ⟨15274719915592154989080757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20366293220789539985441009 15274719915592154989080757)
            ·
              refine ⟨1432004992086764530226321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15274719915592154989080757 1432004992086764530226321)
              ·
                refine ⟨1074003744065073397669741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1432004992086764530226321 1074003744065073397669741)
                ·
                  refine ⟨402751404024402524126153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074003744065073397669741 402751404024402524126153)
                  ·
                    rfl

theorem cell20_882400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_882400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882400 prefixEnd_882400 := by exact prefixLift 882400
  have htrace : WordTrace (prefixWord ++ tailWord_882400) baseStart_882400 baseEnd_882400 := by
    simpa [prefixWord, tailWord_882400, baseEnd_882400] using wordTrace_append hprefix tailTrace_882400
  have hstable : (prefixWord ++ tailWord_882400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882400).length < 2 ^ (prefixWord ++ tailWord_882400).sum := by decide
  have hdescent : baseEnd_882400 < baseStart_882400 := by decide
  rcases family_descends (prefixWord ++ tailWord_882400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882414 : List Nat := [4, 1, 2, 1, 1, 2, 2, 7]
def baseStart_882414 : Nat := 118140960795 + 882414 * 2 ^ 59
def prefixEnd_882414 : Nat := 4983230072969 + 3 ^ 40 * 882414 * 2
def baseEnd_882414 : Nat := 134252598001960232553143

theorem tailTrace_882414 : CollatzResearch.WordTrace tailWord_882414 prefixEnd_882414 134252598001960232553143 := by
  unfold tailWord_882414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023035328146532144765787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21456188416781504772084197 4023035328146532144765787)
  ·
    refine ⟨6034552992219798217148681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023035328146532144765787 6034552992219798217148681)
    ·
      refine ⟨4525914744164848662861511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6034552992219798217148681 4525914744164848662861511)
      ·
        refine ⟨6788872116247272994292267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4525914744164848662861511 6788872116247272994292267)
        ·
          refine ⟨10183308174370909491438401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6788872116247272994292267 10183308174370909491438401)
          ·
            refine ⟨7637481130778182118578801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10183308174370909491438401 7637481130778182118578801)
            ·
              refine ⟨5728110848083636588934101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7637481130778182118578801 5728110848083636588934101)
              ·
                refine ⟨134252598001960232553143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5728110848083636588934101 134252598001960232553143)
                ·
                  rfl

theorem cell20_882414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_882414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882414 prefixEnd_882414 := by exact prefixLift 882414
  have htrace : WordTrace (prefixWord ++ tailWord_882414) baseStart_882414 baseEnd_882414 := by
    simpa [prefixWord, tailWord_882414, baseEnd_882414] using wordTrace_append hprefix tailTrace_882414
  have hstable : (prefixWord ++ tailWord_882414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882414).length < 2 ^ (prefixWord ++ tailWord_882414).sum := by decide
  have hdescent : baseEnd_882414 < baseStart_882414 := by decide
  rcases family_descends (prefixWord ++ tailWord_882414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882417 : List Nat := [1, 2, 2, 2, 2, 4, 3, 1, 3]
def baseStart_882417 : Nat := 118140960795 + 882417 * 2 ^ 59
def prefixEnd_882417 : Nat := 4983230072969 + 3 ^ 40 * 882417 * 2
def baseEnd_882417 : Nat := 402759163287626020559417

theorem tailTrace_882417 : CollatzResearch.WordTrace tailWord_882417 prefixEnd_882417 402759163287626020559417 := by
  unfold tailWord_882417
  simp only [CollatzResearch.WordTrace]
  refine ⟨32184392044161388670485505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21456261362774259113657003 32184392044161388670485505)
  ·
    refine ⟨24138294033121041502864129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32184392044161388670485505 24138294033121041502864129)
    ·
      refine ⟨18103720524840781127148097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24138294033121041502864129 18103720524840781127148097)
      ·
        refine ⟨13577790393630585845361073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18103720524840781127148097 13577790393630585845361073)
        ·
          refine ⟨10183342795222939384020805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13577790393630585845361073 10183342795222939384020805)
          ·
            refine ⟨1909376774104301134503901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10183342795222939384020805 1909376774104301134503901)
            ·
              refine ⟨716016290289112925438963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1909376774104301134503901 716016290289112925438963)
              ·
                refine ⟨1074024435433669388158445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716016290289112925438963 1074024435433669388158445)
                ·
                  refine ⟨402759163287626020559417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074024435433669388158445 402759163287626020559417)
                  ·
                    rfl

theorem cell20_882417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 1, 3].length) (baseStart_882417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882417 prefixEnd_882417 := by exact prefixLift 882417
  have htrace : WordTrace (prefixWord ++ tailWord_882417) baseStart_882417 baseEnd_882417 := by
    simpa [prefixWord, tailWord_882417, baseEnd_882417] using wordTrace_append hprefix tailTrace_882417
  have hstable : (prefixWord ++ tailWord_882417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882417).length < 2 ^ (prefixWord ++ tailWord_882417).sum := by decide
  have hdescent : baseEnd_882417 < baseStart_882417 := by decide
  rcases family_descends (prefixWord ++ tailWord_882417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882472 : List Nat := [2, 1, 5, 1, 1, 4, 2, 1, 3]
def baseStart_882472 : Nat := 118140960795 + 882472 * 2 ^ 59
def prefixEnd_882472 : Nat := 4983230072969 + 3 ^ 40 * 882472 * 2
def baseEnd_882472 : Nat := 402784266786290273725859

theorem tailTrace_882472 : CollatzResearch.WordTrace tailWord_882472 prefixEnd_882472 402784266786290273725859 := by
  unfold tailWord_882472
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093199029481066531868835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21457598705974755375825113 16093199029481066531868835)
  ·
    refine ⟨24139798544221599797803253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16093199029481066531868835 24139798544221599797803253)
    ·
      refine ⟨2263106113520774981044055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24139798544221599797803253 2263106113520774981044055)
      ·
        refine ⟨3394659170281162471566083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263106113520774981044055 3394659170281162471566083)
        ·
          refine ⟨5091988755421743707349125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3394659170281162471566083 5091988755421743707349125)
          ·
            refine ⟨954747891641576945127961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5091988755421743707349125 954747891641576945127961)
            ·
              refine ⟨716060918731182708845971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 954747891641576945127961 716060918731182708845971)
              ·
                refine ⟨1074091378096774063268957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716060918731182708845971 1074091378096774063268957)
                ·
                  refine ⟨402784266786290273725859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074091378096774063268957 402784266786290273725859)
                  ·
                    rfl

theorem cell20_882472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_882472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882472 prefixEnd_882472 := by exact prefixLift 882472
  have htrace : WordTrace (prefixWord ++ tailWord_882472) baseStart_882472 baseEnd_882472 := by
    simpa [prefixWord, tailWord_882472, baseEnd_882472] using wordTrace_append hprefix tailTrace_882472
  have hstable : (prefixWord ++ tailWord_882472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882472).length < 2 ^ (prefixWord ++ tailWord_882472).sum := by decide
  have hdescent : baseEnd_882472 < baseStart_882472 := by decide
  rcases family_descends (prefixWord ++ tailWord_882472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882476 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_882476 : Nat := 118140960795 + 882476 * 2 ^ 59
def prefixEnd_882476 : Nat := 4983230072969 + 3 ^ 40 * 882476 * 2
def baseEnd_882476 : Nat := 402786092495284037592509

theorem tailTrace_882476 : CollatzResearch.WordTrace tailWord_882476 prefixEnd_882476 402786092495284037592509 := by
  unfold tailWord_882476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16093271975473820873441641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21457695967298427831255521 16093271975473820873441641)
  ·
    refine ⟨12069953981605365655081231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16093271975473820873441641 12069953981605365655081231)
    ·
      refine ⟨18104930972408048482621847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12069953981605365655081231 18104930972408048482621847)
      ·
        refine ⟨27157396458612072723932771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18104930972408048482621847 27157396458612072723932771)
        ·
          refine ⟨40736094687918109085899157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27157396458612072723932771 40736094687918109085899157)
          ·
            refine ⟨1909504438496161363401523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40736094687918109085899157 1909504438496161363401523)
            ·
              refine ⟨2864256657744242045102285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909504438496161363401523 2864256657744242045102285)
              ·
                refine ⟨1074096246654090766913357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2864256657744242045102285 1074096246654090766913357)
                ·
                  refine ⟨402786092495284037592509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074096246654090766913357 402786092495284037592509)
                  ·
                    rfl

theorem cell20_882476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_882476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882476 prefixEnd_882476 := by exact prefixLift 882476
  have htrace : WordTrace (prefixWord ++ tailWord_882476) baseStart_882476 baseEnd_882476 := by
    simpa [prefixWord, tailWord_882476, baseEnd_882476] using wordTrace_append hprefix tailTrace_882476
  have hstable : (prefixWord ++ tailWord_882476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882476).length < 2 ^ (prefixWord ++ tailWord_882476).sum := by decide
  have hdescent : baseEnd_882476 < baseStart_882476 := by decide
  rcases family_descends (prefixWord ++ tailWord_882476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882490 : List Nat := [3, 1, 1, 1, 5, 1, 2, 6]
def baseStart_882490 : Nat := 118140960795 + 882490 * 2 ^ 59
def prefixEnd_882490 : Nat := 4983230072969 + 3 ^ 40 * 882490 * 2
def baseEnd_882490 : Nat := 134264160825587403708595

theorem tailTrace_882490 : CollatzResearch.WordTrace tailWord_882490 prefixEnd_882490 134264160825587403708595 := by
  unfold tailWord_882490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046763643224230534473231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21458036381931281425261949 8046763643224230534473231)
  ·
    refine ⟨12070145464836345801709847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8046763643224230534473231 12070145464836345801709847)
    ·
      refine ⟨18105218197254518702564771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12070145464836345801709847 18105218197254518702564771)
      ·
        refine ⟨27157827295881778053847157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18105218197254518702564771 27157827295881778053847157)
        ·
          refine ⟨2546046308988916692548171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27157827295881778053847157 2546046308988916692548171)
          ·
            refine ⟨3819069463483375038822257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546046308988916692548171 3819069463483375038822257)
            ·
              refine ⟨2864302097612531279116693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3819069463483375038822257 2864302097612531279116693)
              ·
                refine ⟨134264160825587403708595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2864302097612531279116693 134264160825587403708595)
                ·
                  rfl

theorem cell20_882490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 6].length) (baseStart_882490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882490 prefixEnd_882490 := by exact prefixLift 882490
  have htrace : WordTrace (prefixWord ++ tailWord_882490) baseStart_882490 baseEnd_882490 := by
    simpa [prefixWord, tailWord_882490, baseEnd_882490] using wordTrace_append hprefix tailTrace_882490
  have hstable : (prefixWord ++ tailWord_882490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882490).length < 2 ^ (prefixWord ++ tailWord_882490).sum := by decide
  have hdescent : baseEnd_882490 < baseStart_882490 := by decide
  rcases family_descends (prefixWord ++ tailWord_882490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882514 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_882514 : Nat := 118140960795 + 882514 * 2 ^ 59
def prefixEnd_882514 : Nat := 4983230072969 + 3 ^ 40 * 882514 * 2
def baseEnd_882514 : Nat := 402803436730724794325687

theorem tailTrace_882514 : CollatzResearch.WordTrace tailWord_882514 prefixEnd_882514 402803436730724794325687 := by
  unfold tailWord_882514
  simp only [CollatzResearch.WordTrace]
  refine ⟨8046982481202493559191649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21458619949873316157844397 8046982481202493559191649)
  ·
    refine ⟨6035236860901870169393737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8046982481202493559191649 6035236860901870169393737)
    ·
      refine ⟨4526427645676402627045303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6035236860901870169393737 4526427645676402627045303)
      ·
        refine ⟨6789641468514603940567955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4526427645676402627045303 6789641468514603940567955)
        ·
          refine ⟨10184462202771905910851933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6789641468514603940567955 10184462202771905910851933)
          ·
            refine ⟨3819173326039464716569475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10184462202771905910851933 3819173326039464716569475)
            ·
              refine ⟨5728759989059197074854213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3819173326039464716569475 5728759989059197074854213)
              ·
                refine ⟨1074142497948599451535165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5728759989059197074854213 1074142497948599451535165)
                ·
                  refine ⟨402803436730724794325687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074142497948599451535165 402803436730724794325687)
                  ·
                    rfl

theorem cell20_882514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_882514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882514 prefixEnd_882514 := by exact prefixLift 882514
  have htrace : WordTrace (prefixWord ++ tailWord_882514) baseStart_882514 baseEnd_882514 := by
    simpa [prefixWord, tailWord_882514, baseEnd_882514] using wordTrace_append hprefix tailTrace_882514
  have hstable : (prefixWord ++ tailWord_882514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882514).length < 2 ^ (prefixWord ++ tailWord_882514).sum := by decide
  have hdescent : baseEnd_882514 < baseStart_882514 := by decide
  rcases family_descends (prefixWord ++ tailWord_882514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882517 : List Nat := [1, 3, 2, 2, 2, 2, 4, 2, 2]
def baseStart_882517 : Nat := 118140960795 + 882517 * 2 ^ 59
def prefixEnd_882517 : Nat := 4983230072969 + 3 ^ 40 * 882517 * 2
def baseEnd_882517 : Nat := 402804806012470117225675

theorem tailTrace_882517 : CollatzResearch.WordTrace tailWord_882517 prefixEnd_882517 402804806012470117225675 := by
  unfold tailWord_882517
  simp only [CollatzResearch.WordTrace]
  refine ⟨32188039343799105749125805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21458692895866070499417203 32188039343799105749125805)
  ·
    refine ⟨12070514753924664655922177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32188039343799105749125805 12070514753924664655922177)
    ·
      refine ⟨9052886065443498491941633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12070514753924664655922177 9052886065443498491941633)
      ·
        refine ⟨6789664549082623868956225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9052886065443498491941633 6789664549082623868956225)
        ·
          refine ⟨5092248411811967901717169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6789664549082623868956225 5092248411811967901717169)
          ·
            refine ⟨3819186308858975926287877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092248411811967901717169 3819186308858975926287877)
            ·
              refine ⟨716097432911057986178977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3819186308858975926287877 716097432911057986178977)
              ·
                refine ⟨537073074683293489634233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716097432911057986178977 537073074683293489634233)
                ·
                  refine ⟨402804806012470117225675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537073074683293489634233 402804806012470117225675)
                  ·
                    rfl

theorem cell20_882517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 2, 2].length) (baseStart_882517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882517 prefixEnd_882517 := by exact prefixLift 882517
  have htrace : WordTrace (prefixWord ++ tailWord_882517) baseStart_882517 baseEnd_882517 := by
    simpa [prefixWord, tailWord_882517, baseEnd_882517] using wordTrace_append hprefix tailTrace_882517
  have hstable : (prefixWord ++ tailWord_882517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882517).length < 2 ^ (prefixWord ++ tailWord_882517).sum := by decide
  have hdescent : baseEnd_882517 < baseStart_882517 := by decide
  rcases family_descends (prefixWord ++ tailWord_882517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882524 : List Nat := [2, 2, 4, 2, 2, 2, 1, 5]
def baseStart_882524 : Nat := 118140960795 + 882524 * 2 ^ 59
def prefixEnd_882524 : Nat := 4983230072969 + 3 ^ 40 * 882524 * 2
def baseEnd_882524 : Nat := 134269333667736401330771

theorem tailTrace_882524 : CollatzResearch.WordTrace tailWord_882524 prefixEnd_882524 134269333667736401330771 := by
  unfold tailWord_882524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094147327386872972315313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21458863103182497296420417 16094147327386872972315313)
  ·
    refine ⟨12070610495540154729236485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16094147327386872972315313 12070610495540154729236485)
    ·
      refine ⟨2263239467913779011731841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12070610495540154729236485 2263239467913779011731841)
      ·
        refine ⟨1697429600935334258798881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263239467913779011731841 1697429600935334258798881)
        ·
          refine ⟨1273072200701500694099161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697429600935334258798881 1273072200701500694099161)
          ·
            refine ⟨954804150526125520574371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273072200701500694099161 954804150526125520574371)
            ·
              refine ⟨1432206225789188280861557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954804150526125520574371 1432206225789188280861557)
              ·
                refine ⟨134269333667736401330771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1432206225789188280861557 134269333667736401330771)
                ·
                  rfl

theorem cell20_882524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_882524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882524 prefixEnd_882524 := by exact prefixLift 882524
  have htrace : WordTrace (prefixWord ++ tailWord_882524) baseStart_882524 baseEnd_882524 := by
    simpa [prefixWord, tailWord_882524, baseEnd_882524] using wordTrace_append hprefix tailTrace_882524
  have hstable : (prefixWord ++ tailWord_882524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882524).length < 2 ^ (prefixWord ++ tailWord_882524).sum := by decide
  have hdescent : baseEnd_882524 < baseStart_882524 := by decide
  rcases family_descends (prefixWord ++ tailWord_882524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882528 : List Nat := [2, 1, 1, 3, 3, 2, 3, 5]
def baseStart_882528 : Nat := 118140960795 + 882528 * 2 ^ 59
def prefixEnd_882528 : Nat := 4983230072969 + 3 ^ 40 * 882528 * 2
def baseEnd_882528 : Nat := 134269942237400989286321

theorem tailTrace_882528 : CollatzResearch.WordTrace tailWord_882528 prefixEnd_882528 134269942237400989286321 := by
  unfold tailWord_882528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16094220273379627313888119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21458960364506169751850825 16094220273379627313888119)
  ·
    refine ⟨24141330410069440970832179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16094220273379627313888119 24141330410069440970832179)
    ·
      refine ⟨36211995615104161456248269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24141330410069440970832179 36211995615104161456248269)
      ·
        refine ⟨13579498355664060546093101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36211995615104161456248269 13579498355664060546093101)
        ·
          refine ⟨5092311883374022704784913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13579498355664060546093101 5092311883374022704784913)
          ·
            refine ⟨3819233912530517028588685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5092311883374022704784913 3819233912530517028588685)
            ·
              refine ⟨1432212717198943885720757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3819233912530517028588685 1432212717198943885720757)
              ·
                refine ⟨134269942237400989286321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1432212717198943885720757 134269942237400989286321)
                ·
                  rfl

theorem cell20_882528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 5].length) (baseStart_882528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882528 prefixEnd_882528 := by exact prefixLift 882528
  have htrace : WordTrace (prefixWord ++ tailWord_882528) baseStart_882528 baseEnd_882528 := by
    simpa [prefixWord, tailWord_882528, baseEnd_882528] using wordTrace_append hprefix tailTrace_882528
  have hstable : (prefixWord ++ tailWord_882528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882528).length < 2 ^ (prefixWord ++ tailWord_882528).sum := by decide
  have hdescent : baseEnd_882528 < baseStart_882528 := by decide
  rcases family_descends (prefixWord ++ tailWord_882528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882582 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_882582 : Nat := 118140960795 + 882582 * 2 ^ 59
def prefixEnd_882582 : Nat := 4983230072969 + 3 ^ 40 * 882582 * 2
def baseEnd_882582 : Nat := 402834473783618780058743

theorem tailTrace_882582 : CollatzResearch.WordTrace tailWord_882582 prefixEnd_882582 402834473783618780058743 := by
  unfold tailWord_882582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011900630535226365640125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21460273392375747900161333 2011900630535226365640125)
  ·
    refine ⟨754462736450709887115047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2011900630535226365640125 754462736450709887115047)
    ·
      refine ⟨1131694104676064830672571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754462736450709887115047 1131694104676064830672571)
      ·
        refine ⟨1697541157014097246008857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1131694104676064830672571 1697541157014097246008857)
        ·
          refine ⟨1273155867760572934506643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697541157014097246008857 1273155867760572934506643)
          ·
            refine ⟨1909733801640859401759965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273155867760572934506643 1909733801640859401759965)
            ·
              refine ⟨716150175615322275659987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1909733801640859401759965 716150175615322275659987)
              ·
                refine ⟨1074225263422983413489981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716150175615322275659987 1074225263422983413489981)
                ·
                  refine ⟨402834473783618780058743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074225263422983413489981 402834473783618780058743)
                  ·
                    rfl

theorem cell20_882582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_882582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882582 prefixEnd_882582 := by exact prefixLift 882582
  have htrace : WordTrace (prefixWord ++ tailWord_882582) baseStart_882582 baseEnd_882582 := by
    simpa [prefixWord, tailWord_882582, baseEnd_882582] using wordTrace_append hprefix tailTrace_882582
  have hstable : (prefixWord ++ tailWord_882582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882582).length < 2 ^ (prefixWord ++ tailWord_882582).sum := by decide
  have hdescent : baseEnd_882582 < baseStart_882582 := by decide
  rcases family_descends (prefixWord ++ tailWord_882582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882600 : List Nat := [2, 1, 6, 2, 1, 1, 1, 6]
def baseStart_882600 : Nat := 118140960795 + 882600 * 2 ^ 59
def prefixEnd_882600 : Nat := 4983230072969 + 3 ^ 40 * 882600 * 2
def baseEnd_882600 : Nat := 134280896491363572486223

theorem tailTrace_882600 : CollatzResearch.WordTrace tailWord_882600 prefixEnd_882600 134280896491363572486223 := by
  unfold tailWord_882600
  simp only [CollatzResearch.WordTrace]
  refine ⟨16095533301249205462198627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21460711068332273949598169 16095533301249205462198627)
  ·
    refine ⟨24143299951873808193297941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16095533301249205462198627 24143299951873808193297941)
    ·
      refine ⟨1131717185244084759060841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24143299951873808193297941 1131717185244084759060841)
      ·
        refine ⟨848787888933063569295631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131717185244084759060841 848787888933063569295631)
        ·
          refine ⟨1273181833399595353943447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848787888933063569295631 1273181833399595353943447)
          ·
            refine ⟨1909772750099393030915171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273181833399595353943447 1909772750099393030915171)
            ·
              refine ⟨2864659125149089546372757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1909772750099393030915171 2864659125149089546372757)
              ·
                refine ⟨134280896491363572486223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2864659125149089546372757 134280896491363572486223)
                ·
                  rfl

theorem cell20_882600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 6].length) (baseStart_882600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882600 prefixEnd_882600 := by exact prefixLift 882600
  have htrace : WordTrace (prefixWord ++ tailWord_882600) baseStart_882600 baseEnd_882600 := by
    simpa [prefixWord, tailWord_882600, baseEnd_882600] using wordTrace_append hprefix tailTrace_882600
  have hstable : (prefixWord ++ tailWord_882600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882600).length < 2 ^ (prefixWord ++ tailWord_882600).sum := by decide
  have hdescent : baseEnd_882600 < baseStart_882600 := by decide
  rcases family_descends (prefixWord ++ tailWord_882600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882606 : List Nat := [4, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_882606 : Nat := 118140960795 + 882606 * 2 ^ 59
def prefixEnd_882606 : Nat := 4983230072969 + 3 ^ 40 * 882606 * 2
def baseEnd_882606 : Nat := 402845428037581363258645

theorem tailTrace_882606 : CollatzResearch.WordTrace tailWord_882606 prefixEnd_882606 402845428037581363258645 := by
  unfold tailWord_882606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023910680059584243639459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21460856960317782632743781 4023910680059584243639459)
  ·
    refine ⟨6035866020089376365459189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4023910680059584243639459 6035866020089376365459189)
    ·
      refine ⟨565862439383379034261799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6035866020089376365459189 565862439383379034261799)
      ·
        refine ⟨848793659075068551392699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565862439383379034261799 848793659075068551392699)
        ·
          refine ⟨1273190488612602827089049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848793659075068551392699 1273190488612602827089049)
          ·
            refine ⟨954892866459452120316787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273190488612602827089049 954892866459452120316787)
            ·
              refine ⟨1432339299689178180475181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 954892866459452120316787 1432339299689178180475181)
              ·
                refine ⟨537127237383441817678193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1432339299689178180475181 537127237383441817678193)
                ·
                  refine ⟨402845428037581363258645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537127237383441817678193 402845428037581363258645)
                  ·
                    rfl

theorem cell20_882606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_882606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882606 prefixEnd_882606 := by exact prefixLift 882606
  have htrace : WordTrace (prefixWord ++ tailWord_882606) baseStart_882606 baseEnd_882606 := by
    simpa [prefixWord, tailWord_882606, baseEnd_882606] using wordTrace_append hprefix tailTrace_882606
  have hstable : (prefixWord ++ tailWord_882606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882606).length < 2 ^ (prefixWord ++ tailWord_882606).sum := by decide
  have hdescent : baseEnd_882606 < baseStart_882606 := by decide
  rcases family_descends (prefixWord ++ tailWord_882606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882645 : List Nat := [1, 3, 2, 3, 2, 1, 4, 1, 3]
def baseStart_882645 : Nat := 118140960795 + 882645 * 2 ^ 59
def prefixEnd_882645 : Nat := 4983230072969 + 3 ^ 40 * 882645 * 2
def baseEnd_882645 : Nat := 402863228700270560958485

theorem tailTrace_882645 : CollatzResearch.WordTrace tailWord_882645 prefixEnd_882645 402863228700270560958485 := by
  unfold tailWord_882645
  simp only [CollatzResearch.WordTrace]
  refine ⟨32192707887335383609785389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21461805258223589073190259 32192707887335383609785389)
  ·
    refine ⟨12072265457750768853669521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32192707887335383609785389 12072265457750768853669521)
    ·
      refine ⟨9054199093313076640252141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12072265457750768853669521 9054199093313076640252141)
      ·
        refine ⟨3395324659992403740094553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9054199093313076640252141 3395324659992403740094553)
        ·
          refine ⟨2546493494994302805070915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3395324659992403740094553 2546493494994302805070915)
          ·
            refine ⟨3819740242491454207606373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546493494994302805070915 3819740242491454207606373)
            ·
              refine ⟨716201295467147663926195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3819740242491454207606373 716201295467147663926195)
              ·
                refine ⟨1074301943200721495889293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 716201295467147663926195 1074301943200721495889293)
                ·
                  refine ⟨402863228700270560958485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1074301943200721495889293 402863228700270560958485)
                  ·
                    rfl

theorem cell20_882645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_882645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882645 prefixEnd_882645 := by exact prefixLift 882645
  have htrace : WordTrace (prefixWord ++ tailWord_882645) baseStart_882645 baseEnd_882645 := by
    simpa [prefixWord, tailWord_882645, baseEnd_882645] using wordTrace_append hprefix tailTrace_882645
  have hstable : (prefixWord ++ tailWord_882645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882645).length < 2 ^ (prefixWord ++ tailWord_882645).sum := by decide
  have hdescent : baseEnd_882645 < baseStart_882645 := by decide
  rcases family_descends (prefixWord ++ tailWord_882645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882656 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_882656 : Nat := 118140960795 + 882656 * 2 ^ 59
def prefixEnd_882656 : Nat := 4983230072969 + 3 ^ 40 * 882656 * 2
def baseEnd_882656 : Nat := 402868249400003411591773

theorem tailTrace_882656 : CollatzResearch.WordTrace tailWord_882656 prefixEnd_882656 402868249400003411591773 := by
  unfold tailWord_882656
  simp only [CollatzResearch.WordTrace]
  refine ⟨16096554545147766244217911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21462072726863688325623881 16096554545147766244217911)
  ·
    refine ⟨24144831817721649366326867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16096554545147766244217911 24144831817721649366326867)
    ·
      refine ⟨36217247726582474049490301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24144831817721649366326867 36217247726582474049490301)
      ·
        refine ⟨13581467897468427768558863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36217247726582474049490301 13581467897468427768558863)
        ·
          refine ⟨20372201846202641652838295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13581467897468427768558863 20372201846202641652838295)
          ·
            refine ⟨30558302769303962479257443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20372201846202641652838295 30558302769303962479257443)
            ·
              refine ⟨45837454153955943718886165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30558302769303962479257443 45837454153955943718886165)
              ·
                refine ⟨2148630663466684861822789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 45837454153955943718886165 2148630663466684861822789)
                ·
                  refine ⟨402868249400003411591773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148630663466684861822789 402868249400003411591773)
                  ·
                    rfl

theorem cell20_882656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_882656 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882656 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882656 prefixEnd_882656 := by exact prefixLift 882656
  have htrace : WordTrace (prefixWord ++ tailWord_882656) baseStart_882656 baseEnd_882656 := by
    simpa [prefixWord, tailWord_882656, baseEnd_882656] using wordTrace_append hprefix tailTrace_882656
  have hstable : (prefixWord ++ tailWord_882656).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882656).length < 2 ^ (prefixWord ++ tailWord_882656).sum := by decide
  have hdescent : baseEnd_882656 < baseStart_882656 := by decide
  rcases family_descends (prefixWord ++ tailWord_882656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882686 : List Nat := [4, 2, 2, 2, 1, 1, 4, 2, 2]
def baseStart_882686 : Nat := 118140960795 + 882686 * 2 ^ 59
def prefixEnd_882686 : Nat := 4983230072969 + 3 ^ 40 * 882686 * 2
def baseEnd_882686 : Nat := 402881942217456640591651

theorem tailTrace_882686 : CollatzResearch.WordTrace tailWord_882686 prefixEnd_882686 402881942217456640591651 := by
  unfold tailWord_882686
  simp only [CollatzResearch.WordTrace]
  refine ⟨4024275410023355951503489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21462802186791231741351941 4024275410023355951503489)
  ·
    refine ⟨3018206557517516963627617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4024275410023355951503489 3018206557517516963627617)
    ·
      refine ⟨2263654918138137722720713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018206557517516963627617 2263654918138137722720713)
      ·
        refine ⟨1697741188603603292040535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263654918138137722720713 1697741188603603292040535)
        ·
          refine ⟨2546611782905404938060803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1697741188603603292040535 2546611782905404938060803)
          ·
            refine ⟨3819917674358107407091205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2546611782905404938060803 3819917674358107407091205)
            ·
              refine ⟨716234563942145138829601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3819917674358107407091205 716234563942145138829601)
              ·
                refine ⟨537175922956608854122201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 716234563942145138829601 537175922956608854122201)
                ·
                  refine ⟨402881942217456640591651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 537175922956608854122201 402881942217456640591651)
                  ·
                    rfl

theorem cell20_882686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_882686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882686 prefixEnd_882686 := by exact prefixLift 882686
  have htrace : WordTrace (prefixWord ++ tailWord_882686) baseStart_882686 baseEnd_882686 := by
    simpa [prefixWord, tailWord_882686, baseEnd_882686] using wordTrace_append hprefix tailTrace_882686
  have hstable : (prefixWord ++ tailWord_882686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882686).length < 2 ^ (prefixWord ++ tailWord_882686).sum := by decide
  have hdescent : baseEnd_882686 < baseStart_882686 := by decide
  rcases family_descends (prefixWord ++ tailWord_882686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882742 : List Nat := [5, 1, 2, 1, 1, 1, 3, 1, 5]
def baseStart_882742 : Nat := 118140960795 + 882742 * 2 ^ 59
def prefixEnd_882742 : Nat := 4983230072969 + 3 ^ 40 * 882742 * 2
def baseEnd_882742 : Nat := 402907502143369334724755

theorem tailTrace_882742 : CollatzResearch.WordTrace tailWord_882742 prefixEnd_882742 402907502143369334724755 := by
  unfold tailWord_882742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012265360498998073504155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21464163845322646117377653 2012265360498998073504155)
  ·
    refine ⟨3018398040748497110256233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012265360498998073504155 3018398040748497110256233)
    ·
      refine ⟨2263798530561372832692175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018398040748497110256233 2263798530561372832692175)
      ·
        refine ⟨3395697795842059249038263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2263798530561372832692175 3395697795842059249038263)
        ·
          refine ⟨5093546693763088873557395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395697795842059249038263 5093546693763088873557395)
          ·
            refine ⟨7640320040644633310336093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093546693763088873557395 7640320040644633310336093)
            ·
              refine ⟨2865120015241737491376035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7640320040644633310336093 2865120015241737491376035)
              ·
                refine ⟨4297680022862606237064053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2865120015241737491376035 4297680022862606237064053)
                ·
                  refine ⟨402907502143369334724755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4297680022862606237064053 402907502143369334724755)
                  ·
                    rfl

theorem cell20_882742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_882742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882742 prefixEnd_882742 := by exact prefixLift 882742
  have htrace : WordTrace (prefixWord ++ tailWord_882742) baseStart_882742 baseEnd_882742 := by
    simpa [prefixWord, tailWord_882742, baseEnd_882742] using wordTrace_append hprefix tailTrace_882742
  have hstable : (prefixWord ++ tailWord_882742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882742).length < 2 ^ (prefixWord ++ tailWord_882742).sum := by decide
  have hdescent : baseEnd_882742 < baseStart_882742 := by decide
  rcases family_descends (prefixWord ++ tailWord_882742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882749 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 4]
def baseStart_882749 : Nat := 118140960795 + 882749 * 2 ^ 59
def prefixEnd_882749 : Nat := 4983230072969 + 3 ^ 40 * 882749 * 2
def baseEnd_882749 : Nat := 402910697134108421491393

theorem tailTrace_882749 : CollatzResearch.WordTrace tailWord_882749 prefixEnd_882749 402910697134108421491393 := by
  unfold tailWord_882749
  simp only [CollatzResearch.WordTrace]
  refine ⟨32196501078958609371571301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464334052639072914380867 32196501078958609371571301)
  ·
    refine ⟨6036843952304739257169619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32196501078958609371571301 6036843952304739257169619)
    ·
      refine ⟨9055265928457108885754429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6036843952304739257169619 9055265928457108885754429)
      ·
        refine ⟨3395724723171415832157911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9055265928457108885754429 3395724723171415832157911)
        ·
          refine ⟨5093587084757123748236867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3395724723171415832157911 5093587084757123748236867)
          ·
            refine ⟨7640380627135685622355301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5093587084757123748236867 7640380627135685622355301)
            ·
              refine ⟨1432571367587941054191619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7640380627135685622355301 1432571367587941054191619)
              ·
                refine ⟨2148857051381911581287429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1432571367587941054191619 2148857051381911581287429)
                ·
                  refine ⟨402910697134108421491393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2148857051381911581287429 402910697134108421491393)
                  ·
                    rfl

theorem cell20_882749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_882749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882749 prefixEnd_882749 := by exact prefixLift 882749
  have htrace : WordTrace (prefixWord ++ tailWord_882749) baseStart_882749 baseEnd_882749 := by
    simpa [prefixWord, tailWord_882749, baseEnd_882749] using wordTrace_append hprefix tailTrace_882749
  have hstable : (prefixWord ++ tailWord_882749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882749).length < 2 ^ (prefixWord ++ tailWord_882749).sum := by decide
  have hdescent : baseEnd_882749 < baseStart_882749 := by decide
  rcases family_descends (prefixWord ++ tailWord_882749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_882773 : List Nat := [1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_882773 : Nat := 118140960795 + 882773 * 2 ^ 59
def prefixEnd_882773 : Nat := 4983230072969 + 3 ^ 40 * 882773 * 2
def baseEnd_882773 : Nat := 134307217129357001563765

theorem tailTrace_882773 : CollatzResearch.WordTrace tailWord_882773 prefixEnd_882773 134307217129357001563765 := by
  unfold tailWord_882773
  simp only [CollatzResearch.WordTrace]
  refine ⟨32197376430871661470444973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21464917620581107646963315 32197376430871661470444973)
  ·
    refine ⟨12074016161576873051416865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32197376430871661470444973 12074016161576873051416865)
    ·
      refine ⟨9055512121182654788562649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12074016161576873051416865 9055512121182654788562649)
      ·
        refine ⟨6791634090886991091421987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9055512121182654788562649 6791634090886991091421987)
        ·
          refine ⟨10187451136330486637132981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6791634090886991091421987 10187451136330486637132981)
          ·
            refine ⟨955073544030983122231217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10187451136330486637132981 955073544030983122231217)
            ·
              refine ⟨716305158023237341673413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 955073544030983122231217 716305158023237341673413)
              ·
                refine ⟨134307217129357001563765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 716305158023237341673413 134307217129357001563765)
                ·
                  rfl

theorem cell20_882773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_882773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_882773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_882773 prefixEnd_882773 := by exact prefixLift 882773
  have htrace : WordTrace (prefixWord ++ tailWord_882773) baseStart_882773 baseEnd_882773 := by
    simpa [prefixWord, tailWord_882773, baseEnd_882773] using wordTrace_append hprefix tailTrace_882773
  have hstable : (prefixWord ++ tailWord_882773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_882773).length < 2 ^ (prefixWord ++ tailWord_882773).sum := by decide
  have hdescent : baseEnd_882773 < baseStart_882773 := by decide
  rcases family_descends (prefixWord ++ tailWord_882773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
