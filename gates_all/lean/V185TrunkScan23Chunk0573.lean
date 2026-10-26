import V185TrunkScan23Chunk0572

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3387647 : List Nat := [1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_3387647 : Nat := 118140960795 + 3387647 * 2 ^ 59
def prefixEnd_3387647 : Nat := 4983230072969 + 3 ^ 40 * 3387647 * 2
def baseEnd_3387647 : Nat := 1739491198761812549233001

theorem tailTrace_3387647 : CollatzResearch.WordTrace tailWord_3387647 prefixEnd_3387647 1739491198761812549233001 := by
  unfold tailWord_3387647
  simp only [CollatzResearch.WordTrace]
  refine ⟨123557636758140957890873195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82371757838760638593915463 123557636758140957890873195)
  ·
    refine ⟨185336455137211436836309793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123557636758140957890873195 185336455137211436836309793)
    ·
      refine ⟨139002341352908577627232345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185336455137211436836309793 139002341352908577627232345)
      ·
        refine ⟨104251756014681433220424259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139002341352908577627232345 104251756014681433220424259)
        ·
          refine ⟨156377634022022149830636389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104251756014681433220424259 156377634022022149830636389)
          ·
            refine ⟨29320806379129153093244323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156377634022022149830636389 29320806379129153093244323)
            ·
              refine ⟨43981209568693729639866485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29320806379129153093244323 43981209568693729639866485)
              ·
                refine ⟨4123238397065037153737483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43981209568693729639866485 4123238397065037153737483)
                ·
                  refine ⟨6184857595597555730606225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123238397065037153737483 6184857595597555730606225)
                  ·
                    refine ⟨4638643196698166797954669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6184857595597555730606225 4638643196698166797954669)
                    ·
                      refine ⟨1739491198761812549233001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638643196698166797954669 1739491198761812549233001)
                      ·
                        rfl

theorem cell23_3387647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_3387647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387647 prefixEnd_3387647 := by exact prefixLift 3387647
  have htrace : WordTrace (prefixWord ++ tailWord_3387647) baseStart_3387647 baseEnd_3387647 := by
    simpa [prefixWord, tailWord_3387647, baseEnd_3387647] using wordTrace_append hprefix tailTrace_3387647
  have hstable : (prefixWord ++ tailWord_3387647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387647).length < 2 ^ (prefixWord ++ tailWord_3387647).sum := by decide
  have hdescent : baseEnd_3387647 < baseStart_3387647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387655 : List Nat := [1, 1, 4, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3387655 : Nat := 118140960795 + 3387655 * 2 ^ 59
def prefixEnd_3387655 : Nat := 4983230072969 + 3 ^ 40 * 3387655 * 2
def baseEnd_3387655 : Nat := 1739495306607048517932965

theorem tailTrace_3387655 : CollatzResearch.WordTrace tailWord_3387655 prefixEnd_3387655 1739495306607048517932965 := by
  unfold tailWord_3387655
  simp only [CollatzResearch.WordTrace]
  refine ⟨123557928542111975257164419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82371952361407983504776279 123557928542111975257164419)
  ·
    refine ⟨185336892813167962885746629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123557928542111975257164419 185336892813167962885746629)
    ·
      refine ⟨34750667402468993041077493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185336892813167962885746629 34750667402468993041077493)
      ·
        refine ⟨3257875068981468097601015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34750667402468993041077493 3257875068981468097601015)
        ·
          refine ⟨4886812603472202146401523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3257875068981468097601015 4886812603472202146401523)
          ·
            refine ⟨7330218905208303219602285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4886812603472202146401523 7330218905208303219602285)
            ·
              refine ⟨2748832089453113707350857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7330218905208303219602285 2748832089453113707350857)
              ·
                refine ⟨2061624067089835280513143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2748832089453113707350857 2061624067089835280513143)
                ·
                  refine ⟨3092436100634752920769715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061624067089835280513143 3092436100634752920769715)
                  ·
                    refine ⟨4638654150952129381154573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092436100634752920769715 4638654150952129381154573)
                    ·
                      refine ⟨1739495306607048517932965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638654150952129381154573 1739495306607048517932965)
                      ·
                        rfl

theorem cell23_3387655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3387655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387655 prefixEnd_3387655 := by exact prefixLift 3387655
  have htrace : WordTrace (prefixWord ++ tailWord_3387655) baseStart_3387655 baseEnd_3387655 := by
    simpa [prefixWord, tailWord_3387655, baseEnd_3387655] using wordTrace_append hprefix tailTrace_3387655
  have hstable : (prefixWord ++ tailWord_3387655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387655).length < 2 ^ (prefixWord ++ tailWord_3387655).sum := by decide
  have hdescent : baseEnd_3387655 < baseStart_3387655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387671 : List Nat := [1, 1, 3, 4, 1, 4, 2, 1, 2, 4]
def baseStart_3387671 : Nat := 118140960795 + 3387671 * 2 ^ 59
def prefixEnd_3387671 : Nat := 4983230072969 + 3 ^ 40 * 3387671 * 2
def baseEnd_3387671 : Nat := 579834507432506818444297

theorem tailTrace_3387671 : CollatzResearch.WordTrace tailWord_3387671 prefixEnd_3387671 579834507432506818444297 := by
  unfold tailWord_3387671
  simp only [CollatzResearch.WordTrace]
  refine ⟨123558512110054009989746867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82372341406702673326497911 123558512110054009989746867)
  ·
    refine ⟨185337768165081014984620301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123558512110054009989746867 185337768165081014984620301)
    ·
      refine ⟨69501663061905380619232613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185337768165081014984620301 69501663061905380619232613)
      ·
        refine ⟨13031561824107258866106115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69501663061905380619232613 13031561824107258866106115)
        ·
          refine ⟨19547342736160888299159173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13031561824107258866106115 19547342736160888299159173)
          ·
            refine ⟨3665126763030166556092345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19547342736160888299159173 3665126763030166556092345)
            ·
              refine ⟨2748845072272624917069259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665126763030166556092345 2748845072272624917069259)
              ·
                refine ⟨4123267608408937375603889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2748845072272624917069259 4123267608408937375603889)
                ·
                  refine ⟨3092450706306703031702917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4123267608408937375603889 3092450706306703031702917)
                  ·
                    refine ⟨579834507432506818444297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092450706306703031702917 579834507432506818444297)
                    ·
                      rfl

theorem cell23_3387671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_3387671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387671 prefixEnd_3387671 := by exact prefixLift 3387671
  have htrace : WordTrace (prefixWord ++ tailWord_3387671) baseStart_3387671 baseEnd_3387671 := by
    simpa [prefixWord, tailWord_3387671, baseEnd_3387671] using wordTrace_append hprefix tailTrace_3387671
  have hstable : (prefixWord ++ tailWord_3387671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387671).length < 2 ^ (prefixWord ++ tailWord_3387671).sum := by decide
  have hdescent : baseEnd_3387671 < baseStart_3387671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387678 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 1, 1, 4]
def baseStart_3387678 : Nat := 118140960795 + 3387678 * 2 ^ 59
def prefixEnd_3387678 : Nat := 4983230072969 + 3 ^ 40 * 3387678 * 2
def baseEnd_3387678 : Nat := 1739507116662101927945359

theorem tailTrace_3387678 : CollatzResearch.WordTrace tailWord_3387678 prefixEnd_3387678 1739507116662101927945359 := by
  unfold tailWord_3387678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15444845927628581273156461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82372511614019100123501125 15444845927628581273156461)
  ·
    refine ⟨5791817222860717977433673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15444845927628581273156461 5791817222860717977433673)
    ·
      refine ⟨4343862917145538483075255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5791817222860717977433673 4343862917145538483075255)
      ·
        refine ⟨6515794375718307724612883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4343862917145538483075255 6515794375718307724612883)
        ·
          refine ⟨9773691563577461586919325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515794375718307724612883 9773691563577461586919325)
          ·
            refine ⟨3665134336341548095094747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9773691563577461586919325 3665134336341548095094747)
            ·
              refine ⟨5497701504512322142642121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665134336341548095094747 5497701504512322142642121)
              ·
                refine ⟨4123276128384241606981591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5497701504512322142642121 4123276128384241606981591)
                ·
                  refine ⟨6184914192576362410472387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123276128384241606981591 6184914192576362410472387)
                  ·
                    refine ⟨9277371288864543615708581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6184914192576362410472387 9277371288864543615708581)
                    ·
                      refine ⟨1739507116662101927945359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277371288864543615708581 1739507116662101927945359)
                      ·
                        rfl

theorem cell23_3387678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_3387678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387678 prefixEnd_3387678 := by exact prefixLift 3387678
  have htrace : WordTrace (prefixWord ++ tailWord_3387678) baseStart_3387678 baseEnd_3387678 := by
    simpa [prefixWord, tailWord_3387678, baseEnd_3387678] using wordTrace_append hprefix tailTrace_3387678
  have hstable : (prefixWord ++ tailWord_3387678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387678).length < 2 ^ (prefixWord ++ tailWord_3387678).sum := by decide
  have hdescent : baseEnd_3387678 < baseStart_3387678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387704 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2]
def baseStart_3387704 : Nat := 118140960795 + 3387704 * 2 ^ 59
def prefixEnd_3387704 : Nat := 4983230072969 + 3 ^ 40 * 3387704 * 2
def baseEnd_3387704 : Nat := 1739520467159118826220239

theorem tailTrace_3387704 : CollatzResearch.WordTrace tailWord_3387704 prefixEnd_3387704 1739520467159118826220239 := by
  unfold tailWord_3387704
  simp only [CollatzResearch.WordTrace]
  refine ⟨61779857859467228312849083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82373143812622971083798777 61779857859467228312849083)
  ·
    refine ⟨92669786789200842469273625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61779857859467228312849083 92669786789200842469273625)
    ·
      refine ⟨69502340091900631851955219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92669786789200842469273625 69502340091900631851955219)
      ·
        refine ⟨104253510137850947777932829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69502340091900631851955219 104253510137850947777932829)
        ·
          refine ⟨39095066301694105416724811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104253510137850947777932829 39095066301694105416724811)
          ·
            refine ⟨58642599452541158125087217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39095066301694105416724811 58642599452541158125087217)
            ·
              refine ⟨43981949589405868593815413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58642599452541158125087217 43981949589405868593815413)
              ·
                refine ⟨4123307774006800180670195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43981949589405868593815413 4123307774006800180670195)
                ·
                  refine ⟨6184961661010200271005293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123307774006800180670195 6184961661010200271005293)
                  ·
                    refine ⟨2319360622878825101626985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6184961661010200271005293 2319360622878825101626985)
                    ·
                      refine ⟨1739520467159118826220239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319360622878825101626985 1739520467159118826220239)
                      ·
                        rfl

theorem cell23_3387704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_3387704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387704 prefixEnd_3387704 := by exact prefixLift 3387704
  have htrace : WordTrace (prefixWord ++ tailWord_3387704) baseStart_3387704 baseEnd_3387704 := by
    simpa [prefixWord, tailWord_3387704, baseEnd_3387704] using wordTrace_append hprefix tailTrace_3387704
  have hstable : (prefixWord ++ tailWord_3387704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387704).length < 2 ^ (prefixWord ++ tailWord_3387704).sum := by decide
  have hdescent : baseEnd_3387704 < baseStart_3387704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387720 : List Nat := [2, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3387720 : Nat := 118140960795 + 3387720 * 2 ^ 59
def prefixEnd_3387720 : Nat := 4983230072969 + 3 ^ 40 * 3387720 * 2
def baseEnd_3387720 : Nat := 1739528682849590763620165

theorem tailTrace_3387720 : CollatzResearch.WordTrace tailWord_3387720 prefixEnd_3387720 1739528682849590763620165 := by
  unfold tailWord_3387720
  simp only [CollatzResearch.WordTrace]
  refine ⟨61780149643438245679140307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82373532857917660905520409 61780149643438245679140307)
  ·
    refine ⟨92670224465157368518710461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61780149643438245679140307 92670224465157368518710461)
    ·
      refine ⟨34751334174434013194516423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92670224465157368518710461 34751334174434013194516423)
      ·
        refine ⟨52127001261651019791774635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34751334174434013194516423 52127001261651019791774635)
        ·
          refine ⟨78190501892476529687661953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52127001261651019791774635 78190501892476529687661953)
          ·
            refine ⟨58642876419357397265746465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78190501892476529687661953 58642876419357397265746465)
            ·
              refine ⟨43982157314518047949309849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58642876419357397265746465 43982157314518047949309849)
              ·
                refine ⟨32986617985888535961982387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43982157314518047949309849 32986617985888535961982387)
                ·
                  refine ⟨49479926978832803942973581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32986617985888535961982387 49479926978832803942973581)
                  ·
                    refine ⟨18554972617062301478615093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49479926978832803942973581 18554972617062301478615093)
                    ·
                      refine ⟨1739528682849590763620165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18554972617062301478615093 1739528682849590763620165)
                      ·
                        rfl

theorem cell23_3387720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3387720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387720 prefixEnd_3387720 := by exact prefixLift 3387720
  have htrace : WordTrace (prefixWord ++ tailWord_3387720) baseStart_3387720 baseEnd_3387720 := by
    simpa [prefixWord, tailWord_3387720, baseEnd_3387720] using wordTrace_append hprefix tailTrace_3387720
  have hstable : (prefixWord ++ tailWord_3387720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387720).length < 2 ^ (prefixWord ++ tailWord_3387720).sum := by decide
  have hdescent : baseEnd_3387720 < baseStart_3387720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387770 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_3387770 : Nat := 118140960795 + 3387770 * 2 ^ 59
def prefixEnd_3387770 : Nat := 4983230072969 + 3 ^ 40 * 3387770 * 2
def baseEnd_3387770 : Nat := 579851452294105189331645

theorem tailTrace_3387770 : CollatzResearch.WordTrace tailWord_3387770 prefixEnd_3387770 579851452294105189331645 := by
  unfold tailWord_3387770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30890530734173837474400191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82374748624463566598400509 30890530734173837474400191)
  ·
    refine ⟨46335796101260756211600287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30890530734173837474400191 46335796101260756211600287)
    ·
      refine ⟨69503694151891134317400431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46335796101260756211600287 69503694151891134317400431)
      ·
        refine ⟨104255541227836701476100647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69503694151891134317400431 104255541227836701476100647)
        ·
          refine ⟨156383311841755052214150971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104255541227836701476100647 156383311841755052214150971)
          ·
            refine ⟨234574967762632578321226457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156383311841755052214150971 234574967762632578321226457)
            ·
              refine ⟨175931225821974433740919843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234574967762632578321226457 175931225821974433740919843)
              ·
                refine ⟨263896838732961650611379765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175931225821974433740919843 263896838732961650611379765)
                ·
                  refine ⟨24740328631215154744816853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263896838732961650611379765 24740328631215154744816853)
                  ·
                    refine ⟨579851452294105189331645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24740328631215154744816853 579851452294105189331645)
                    ·
                      rfl

theorem cell23_3387770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_3387770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387770 prefixEnd_3387770 := by exact prefixLift 3387770
  have htrace : WordTrace (prefixWord ++ tailWord_3387770) baseStart_3387770 baseEnd_3387770 := by
    simpa [prefixWord, tailWord_3387770, baseEnd_3387770] using wordTrace_append hprefix tailTrace_3387770
  have hstable : (prefixWord ++ tailWord_3387770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387770).length < 2 ^ (prefixWord ++ tailWord_3387770).sum := by decide
  have hdescent : baseEnd_3387770 < baseStart_3387770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387807 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3387807 : Nat := 118140960795 + 3387807 * 2 ^ 59
def prefixEnd_3387807 : Nat := 4983230072969 + 3 ^ 40 * 3387807 * 2
def baseEnd_3387807 : Nat := 1739573355666531923232265

theorem tailTrace_3387807 : CollatzResearch.WordTrace tailWord_3387807 prefixEnd_3387807 1739573355666531923232265 := by
  unfold tailWord_3387807
  simp only [CollatzResearch.WordTrace]
  refine ⟨123563472437561305216697675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82375648291707536811131783 123563472437561305216697675)
  ·
    refine ⟨185345208656341957825046513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123563472437561305216697675 185345208656341957825046513)
    ·
      refine ⟨139008906492256468368784885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185345208656341957825046513 139008906492256468368784885)
      ·
        refine ⟨13032084983649043909573583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139008906492256468368784885 13032084983649043909573583)
        ·
          refine ⟨19548127475473565864360375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13032084983649043909573583 19548127475473565864360375)
          ·
            refine ⟨29322191213210348796540563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19548127475473565864360375 29322191213210348796540563)
            ·
              refine ⟨43983286819815523194810845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29322191213210348796540563 43983286819815523194810845)
              ·
                refine ⟨16493732557430821198054067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43983286819815523194810845 16493732557430821198054067)
                ·
                  refine ⟨24740598836146231797081101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16493732557430821198054067 24740598836146231797081101)
                  ·
                    refine ⟨9277724563554836923905413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24740598836146231797081101 9277724563554836923905413)
                    ·
                      refine ⟨1739573355666531923232265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277724563554836923905413 1739573355666531923232265)
                      ·
                        rfl

theorem cell23_3387807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3387807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387807 prefixEnd_3387807 := by exact prefixLift 3387807
  have htrace : WordTrace (prefixWord ++ tailWord_3387807) baseStart_3387807 baseEnd_3387807 := by
    simpa [prefixWord, tailWord_3387807, baseEnd_3387807] using wordTrace_append hprefix tailTrace_3387807
  have hstable : (prefixWord ++ tailWord_3387807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387807).length < 2 ^ (prefixWord ++ tailWord_3387807).sum := by decide
  have hdescent : baseEnd_3387807 < baseStart_3387807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387817 : List Nat := [1, 2, 1, 1, 1, 1, 3, 4, 5, 4]
def baseStart_3387817 : Nat := 118140960795 + 3387817 * 2 ^ 59
def prefixEnd_3387817 : Nat := 4983230072969 + 3 ^ 40 * 3387817 * 2
def baseEnd_3387817 : Nat := 579859496824358961369073

theorem tailTrace_3387817 : CollatzResearch.WordTrace tailWord_3387817 prefixEnd_3387817 579859496824358961369073 := by
  unfold tailWord_3387817
  simp only [CollatzResearch.WordTrace]
  refine ⟨123563837167525076924561705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82375891445016717949707803 123563837167525076924561705)
  ·
    refine ⟨92672877875643807693421279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123563837167525076924561705 92672877875643807693421279)
    ·
      refine ⟨139009316813465711540131919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92672877875643807693421279 139009316813465711540131919)
      ·
        refine ⟨208513975220198567310197879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139009316813465711540131919 208513975220198567310197879)
        ·
          refine ⟨312770962830297850965296819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208513975220198567310197879 312770962830297850965296819)
          ·
            refine ⟨469156444245446776447945229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312770962830297850965296819 469156444245446776447945229)
            ·
              refine ⟨175933666592042541167979461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 469156444245446776447945229 175933666592042541167979461)
              ·
                refine ⟨32987562486007976468996149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175933666592042541167979461 32987562486007976468996149)
                ·
                  refine ⟨3092583983063247793968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32987562486007976468996149 3092583983063247793968389)
                  ·
                    refine ⟨579859496824358961369073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092583983063247793968389 579859496824358961369073)
                    ·
                      rfl

theorem cell23_3387817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 5, 4].length) (baseStart_3387817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387817 prefixEnd_3387817 := by exact prefixLift 3387817
  have htrace : WordTrace (prefixWord ++ tailWord_3387817) baseStart_3387817 baseEnd_3387817 := by
    simpa [prefixWord, tailWord_3387817, baseEnd_3387817] using wordTrace_append hprefix tailTrace_3387817
  have hstable : (prefixWord ++ tailWord_3387817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387817).length < 2 ^ (prefixWord ++ tailWord_3387817).sum := by decide
  have hdescent : baseEnd_3387817 < baseStart_3387817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387821 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 2, 5]
def baseStart_3387821 : Nat := 118140960795 + 3387821 * 2 ^ 59
def prefixEnd_3387821 : Nat := 4983230072969 + 3 ^ 40 * 3387821 * 2
def baseEnd_3387821 : Nat := 579860181465231622819067

theorem tailTrace_3387821 : CollatzResearch.WordTrace tailWord_3387821 prefixEnd_3387821 579860181465231622819067 := by
  unfold tailWord_3387821
  simp only [CollatzResearch.WordTrace]
  refine ⟨123563983059510585607707317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82375988706340390405138211 123563983059510585607707317)
  ·
    refine ⟨11584123411829117400722561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123563983059510585607707317 11584123411829117400722561)
    ·
      refine ⟨8688092558871838050541921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11584123411829117400722561 8688092558871838050541921)
      ·
        refine ⟨6516069419153878537906441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8688092558871838050541921 6516069419153878537906441)
        ·
          refine ⟨4887052064365408903429831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516069419153878537906441 4887052064365408903429831)
          ·
            refine ⟨7330578096548113355144747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887052064365408903429831 7330578096548113355144747)
            ·
              refine ⟨10995867144822170032717121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330578096548113355144747 10995867144822170032717121)
              ·
                refine ⟨8246900358616627524537841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10995867144822170032717121 8246900358616627524537841)
                ·
                  refine ⟨6185175268962470643403381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246900358616627524537841 6185175268962470643403381)
                  ·
                    refine ⟨579860181465231622819067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6185175268962470643403381 579860181465231622819067)
                    ·
                      rfl

theorem cell23_3387821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_3387821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387821 prefixEnd_3387821 := by exact prefixLift 3387821
  have htrace : WordTrace (prefixWord ++ tailWord_3387821) baseStart_3387821 baseEnd_3387821 := by
    simpa [prefixWord, tailWord_3387821, baseEnd_3387821] using wordTrace_append hprefix tailTrace_3387821
  have hstable : (prefixWord ++ tailWord_3387821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387821).length < 2 ^ (prefixWord ++ tailWord_3387821).sum := by decide
  have hdescent : baseEnd_3387821 < baseStart_3387821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387857 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_3387857 : Nat := 118140960795 + 3387857 * 2 ^ 59
def prefixEnd_3387857 : Nat := 4983230072969 + 3 ^ 40 * 3387857 * 2
def baseEnd_3387857 : Nat := 1739599029699256727607035

theorem tailTrace_3387857 : CollatzResearch.WordTrace tailWord_3387857 prefixEnd_3387857 1739599029699256727607035 := by
  unfold tailWord_3387857
  simp only [CollatzResearch.WordTrace]
  refine ⟨123565296087380163756017825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82376864058253442504011883 123565296087380163756017825)
  ·
    refine ⟨92673972065535122817013369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123565296087380163756017825 92673972065535122817013369)
    ·
      refine ⟨69505479049151342112760027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92673972065535122817013369 69505479049151342112760027)
      ·
        refine ⟨104258218573727013169140041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69505479049151342112760027 104258218573727013169140041)
        ·
          refine ⟨78193663930295259876855031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104258218573727013169140041 78193663930295259876855031)
          ·
            refine ⟨117290495895442889815282547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78193663930295259876855031 117290495895442889815282547)
            ·
              refine ⟨175935743843164334722923821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117290495895442889815282547 175935743843164334722923821)
              ·
                refine ⟨65975903941186625521096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175935743843164334722923821 65975903941186625521096433)
                ·
                  refine ⟨49481927955889969140822325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65975903941186625521096433 49481927955889969140822325)
                  ·
                    refine ⟨4638930745864684606952093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49481927955889969140822325 4638930745864684606952093)
                    ·
                      refine ⟨1739599029699256727607035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638930745864684606952093 1739599029699256727607035)
                      ·
                        rfl

theorem cell23_3387857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_3387857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387857 prefixEnd_3387857 := by exact prefixLift 3387857
  have htrace : WordTrace (prefixWord ++ tailWord_3387857) baseStart_3387857 baseEnd_3387857 := by
    simpa [prefixWord, tailWord_3387857, baseEnd_3387857] using wordTrace_append hprefix tailTrace_3387857
  have hstable : (prefixWord ++ tailWord_3387857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387857).length < 2 ^ (prefixWord ++ tailWord_3387857).sum := by decide
  have hdescent : baseEnd_3387857 < baseStart_3387857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387858 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_3387858 : Nat := 118140960795 + 3387858 * 2 ^ 59
def prefixEnd_3387858 : Nat := 4983230072969 + 3 ^ 40 * 3387858 * 2
def baseEnd_3387858 : Nat := 1739599543179911223694531

theorem tailTrace_3387858 : CollatzResearch.WordTrace tailWord_3387858 prefixEnd_3387858 1739599543179911223694531 := by
  unfold tailWord_3387858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891333140094135231701057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82376888373584360617869485 30891333140094135231701057)
  ·
    refine ⟨23168499855070601423775793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30891333140094135231701057 23168499855070601423775793)
    ·
      refine ⟨17376374891302951067831845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23168499855070601423775793 17376374891302951067831845)
      ·
        refine ⟨3258070292119303325218471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17376374891302951067831845 3258070292119303325218471)
        ·
          refine ⟨4887105438178954987827707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3258070292119303325218471 4887105438178954987827707)
          ·
            refine ⟨7330658157268432481741561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887105438178954987827707 7330658157268432481741561)
            ·
              refine ⟨5497993617951324361306171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330658157268432481741561 5497993617951324361306171)
              ·
                refine ⟨8246990426926986541959257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497993617951324361306171 8246990426926986541959257)
                ·
                  refine ⟨6185242820195239906469443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246990426926986541959257 6185242820195239906469443)
                  ·
                    refine ⟨9277864230292859859704165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185242820195239906469443 9277864230292859859704165)
                    ·
                      refine ⟨1739599543179911223694531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9277864230292859859704165 1739599543179911223694531)
                      ·
                        rfl

theorem cell23_3387858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_3387858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387858 prefixEnd_3387858 := by exact prefixLift 3387858
  have htrace : WordTrace (prefixWord ++ tailWord_3387858) baseStart_3387858 baseEnd_3387858 := by
    simpa [prefixWord, tailWord_3387858, baseEnd_3387858] using wordTrace_append hprefix tailTrace_3387858
  have hstable : (prefixWord ++ tailWord_3387858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387858).length < 2 ^ (prefixWord ++ tailWord_3387858).sum := by decide
  have hdescent : baseEnd_3387858 < baseStart_3387858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387861 : List Nat := [1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_3387861 : Nat := 118140960795 + 3387861 * 2 ^ 59
def prefixEnd_3387861 : Nat := 4983230072969 + 3 ^ 40 * 3387861 * 2
def baseEnd_3387861 : Nat := 1739601083621874711957017

theorem tailTrace_3387861 : CollatzResearch.WordTrace tailWord_3387861 prefixEnd_3387861 1739601083621874711957017 := by
  unfold tailWord_3387861
  simp only [CollatzResearch.WordTrace]
  refine ⟨123565441979365672439163437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82376961319577114959442291 123565441979365672439163437)
  ·
    refine ⟨46337040742262127164686289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123565441979365672439163437 46337040742262127164686289)
    ·
      refine ⟨34752780556696595373514717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46337040742262127164686289 34752780556696595373514717)
      ·
        refine ⟨13032292708761223265068019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34752780556696595373514717 13032292708761223265068019)
        ·
          refine ⟨19548439063141834897602029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13032292708761223265068019 19548439063141834897602029)
          ·
            refine ⟨7330664648678188086600761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19548439063141834897602029 7330664648678188086600761)
            ·
              refine ⟨5497998486508641064950571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7330664648678188086600761 5497998486508641064950571)
              ·
                refine ⟨8246997729762961597425857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5497998486508641064950571 8246997729762961597425857)
                ·
                  refine ⟨6185248297322221198069393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8246997729762961597425857 6185248297322221198069393)
                  ·
                    refine ⟨4638936222991665898552045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6185248297322221198069393 4638936222991665898552045)
                    ·
                      refine ⟨1739601083621874711957017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4638936222991665898552045 1739601083621874711957017)
                      ·
                        rfl

theorem cell23_3387861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_3387861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387861 prefixEnd_3387861 := by exact prefixLift 3387861
  have htrace : WordTrace (prefixWord ++ tailWord_3387861) baseStart_3387861 baseEnd_3387861 := by
    simpa [prefixWord, tailWord_3387861, baseEnd_3387861] using wordTrace_append hprefix tailTrace_3387861
  have hstable : (prefixWord ++ tailWord_3387861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387861).length < 2 ^ (prefixWord ++ tailWord_3387861).sum := by decide
  have hdescent : baseEnd_3387861 < baseStart_3387861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387885 : List Nat := [1, 5, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_3387885 : Nat := 118140960795 + 3387885 * 2 ^ 59
def prefixEnd_3387885 : Nat := 4983230072969 + 3 ^ 40 * 3387885 * 2
def baseEnd_3387885 : Nat := 579871135719194206018969

theorem tailTrace_3387885 : CollatzResearch.WordTrace tailWord_3387885 prefixEnd_3387885 579871135719194206018969 := by
  unfold tailWord_3387885
  simp only [CollatzResearch.WordTrace]
  refine ⟨123566317331278724538037109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82377544887519149692024739 123566317331278724538037109)
  ·
    refine ⟨11584342249807380425440979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123566317331278724538037109 11584342249807380425440979)
    ·
      refine ⟨17376513374711070638161469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584342249807380425440979 17376513374711070638161469)
      ·
        refine ⟨6516192515516651489310551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17376513374711070638161469 6516192515516651489310551)
        ·
          refine ⟨9774288773274977233965827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516192515516651489310551 9774288773274977233965827)
          ·
            refine ⟨14661433159912465850948741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774288773274977233965827 14661433159912465850948741)
            ·
              refine ⟨2749018717483587347052889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14661433159912465850948741 2749018717483587347052889)
              ·
                refine ⟨2061764038112690510289667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749018717483587347052889 2061764038112690510289667)
                ·
                  refine ⟨3092646057169035765434501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2061764038112690510289667 3092646057169035765434501)
                  ·
                    refine ⟨579871135719194206018969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092646057169035765434501 579871135719194206018969)
                    ·
                      rfl

theorem cell23_3387885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_3387885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387885 prefixEnd_3387885 := by exact prefixLift 3387885
  have htrace : WordTrace (prefixWord ++ tailWord_3387885) baseStart_3387885 baseEnd_3387885 := by
    simpa [prefixWord, tailWord_3387885, baseEnd_3387885] using wordTrace_append hprefix tailTrace_3387885
  have hstable : (prefixWord ++ tailWord_3387885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387885).length < 2 ^ (prefixWord ++ tailWord_3387885).sum := by decide
  have hdescent : baseEnd_3387885 < baseStart_3387885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387894 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_3387894 : Nat := 118140960795 + 3387894 * 2 ^ 59
def prefixEnd_3387894 : Nat := 4983230072969 + 3 ^ 40 * 3387894 * 2
def baseEnd_3387894 : Nat := 579872676161157694281455

theorem tailTrace_3387894 : CollatzResearch.WordTrace tailWord_3387894 prefixEnd_3387894 579872676161157694281455 := by
  unfold tailWord_3387894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7722915349265382442194671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82377763725497412716743157 7722915349265382442194671)
  ·
    refine ⟨11584373023898073663292007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7722915349265382442194671 11584373023898073663292007)
    ·
      refine ⟨17376559535847110494938011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11584373023898073663292007 17376559535847110494938011)
      ·
        refine ⟨26064839303770665742407017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17376559535847110494938011 26064839303770665742407017)
        ·
          refine ⟨19548629477827999306805263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26064839303770665742407017 19548629477827999306805263)
          ·
            refine ⟨29322944216741998960207895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19548629477827999306805263 29322944216741998960207895)
            ·
              refine ⟨43984416325112998440311843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29322944216741998960207895 43984416325112998440311843)
              ·
                refine ⟨65976624487669497660467765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43984416325112998440311843 65976624487669497660467765)
                ·
                  refine ⟨6185308545719015405668853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65976624487669497660467765 6185308545719015405668853)
                  ·
                    refine ⟨579872676161157694281455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6185308545719015405668853 579872676161157694281455)
                    ·
                      rfl

theorem cell23_3387894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_3387894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387894 prefixEnd_3387894 := by exact prefixLift 3387894
  have htrace : WordTrace (prefixWord ++ tailWord_3387894) baseStart_3387894 baseEnd_3387894 := by
    simpa [prefixWord, tailWord_3387894, baseEnd_3387894] using wordTrace_append hprefix tailTrace_3387894
  have hstable : (prefixWord ++ tailWord_3387894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387894).length < 2 ^ (prefixWord ++ tailWord_3387894).sum := by decide
  have hdescent : baseEnd_3387894 < baseStart_3387894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387908 : List Nat := [2, 3, 2, 3, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3387908 : Nat := 118140960795 + 3387908 * 2 ^ 59
def prefixEnd_3387908 : Nat := 4983230072969 + 3 ^ 40 * 3387908 * 2
def baseEnd_3387908 : Nat := 1739625217212636028069301

theorem tailTrace_3387908 : CollatzResearch.WordTrace tailWord_3387908 prefixEnd_3387908 1739625217212636028069301 := by
  unfold tailWord_3387908
  simp only [CollatzResearch.WordTrace]
  refine ⟨61783578105097699733062189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82378104140130266310749585 61783578105097699733062189)
  ·
    refine ⟨23168841789411637399898321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61783578105097699733062189 23168841789411637399898321)
    ·
      refine ⟨17376631342058728049923741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23168841789411637399898321 17376631342058728049923741)
      ·
        refine ⟨6516236753272023018721403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17376631342058728049923741 6516236753272023018721403)
        ·
          refine ⟨9774355129908034528082105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516236753272023018721403 9774355129908034528082105)
          ·
            refine ⟨7330766347431025896061579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9774355129908034528082105 7330766347431025896061579)
            ·
              refine ⟨10996149521146538844092369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7330766347431025896061579 10996149521146538844092369)
              ·
                refine ⟨8247112140859904133069277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996149521146538844092369 8247112140859904133069277)
                ·
                  refine ⟨3092667052822464049900979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8247112140859904133069277 3092667052822464049900979)
                  ·
                    refine ⟨4639000579233696074851469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3092667052822464049900979 4639000579233696074851469)
                    ·
                      refine ⟨1739625217212636028069301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4639000579233696074851469 1739625217212636028069301)
                      ·
                        rfl

theorem cell23_3387908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3387908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387908 prefixEnd_3387908 := by exact prefixLift 3387908
  have htrace : WordTrace (prefixWord ++ tailWord_3387908) baseStart_3387908 baseEnd_3387908 := by
    simpa [prefixWord, tailWord_3387908, baseEnd_3387908] using wordTrace_append hprefix tailTrace_3387908
  have hstable : (prefixWord ++ tailWord_3387908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387908).length < 2 ^ (prefixWord ++ tailWord_3387908).sum := by decide
  have hdescent : baseEnd_3387908 < baseStart_3387908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387914 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_3387914 : Nat := 118140960795 + 3387914 * 2 ^ 59
def prefixEnd_3387914 : Nat := 4983230072969 + 3 ^ 40 * 3387914 * 2
def baseEnd_3387914 : Nat := 1739628298096563004594273

theorem tailTrace_3387914 : CollatzResearch.WordTrace tailWord_3387914 prefixEnd_3387914 1739628298096563004594273 := by
  unfold tailWord_3387914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30891843762043415622710699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82378250032115774993895197 30891843762043415622710699)
  ·
    refine ⟨46337765643065123434066049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30891843762043415622710699 46337765643065123434066049)
    ·
      refine ⟨34753324232298842575549537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46337765643065123434066049 34753324232298842575549537)
      ·
        refine ⟨26064993174224131931662153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34753324232298842575549537 26064993174224131931662153)
        ·
          refine ⟨19548744880668098948746615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26064993174224131931662153 19548744880668098948746615)
          ·
            refine ⟨29323117321002148423119923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19548744880668098948746615 29323117321002148423119923)
            ·
              refine ⟨43984675981503222634679885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29323117321002148423119923 43984675981503222634679885)
              ·
                refine ⟨16494253493063708488004957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43984675981503222634679885 16494253493063708488004957)
                ·
                  refine ⟨6185345059898890683001859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16494253493063708488004957 6185345059898890683001859)
                  ·
                    refine ⟨9278017589848336024502789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185345059898890683001859 9278017589848336024502789)
                    ·
                      refine ⟨1739628298096563004594273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9278017589848336024502789 1739628298096563004594273)
                      ·
                        rfl

theorem cell23_3387914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_3387914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387914 prefixEnd_3387914 := by exact prefixLift 3387914
  have htrace : WordTrace (prefixWord ++ tailWord_3387914) baseStart_3387914 baseEnd_3387914 := by
    simpa [prefixWord, tailWord_3387914, baseEnd_3387914] using wordTrace_append hprefix tailTrace_3387914
  have hstable : (prefixWord ++ tailWord_3387914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387914).length < 2 ^ (prefixWord ++ tailWord_3387914).sum := by decide
  have hdescent : baseEnd_3387914 < baseStart_3387914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387918 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3387918 : Nat := 118140960795 + 3387918 * 2 ^ 59
def prefixEnd_3387918 : Nat := 4983230072969 + 3 ^ 40 * 3387918 * 2
def baseEnd_3387918 : Nat := 1739630352019180988944255

theorem tailTrace_3387918 : CollatzResearch.WordTrace tailWord_3387918 prefixEnd_3387918 1739630352019180988944255 := by
  unfold tailWord_3387918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15445940117519896396748551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82378347293439447449325605 15445940117519896396748551)
  ·
    refine ⟨23168910176279844595122827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15445940117519896396748551 23168910176279844595122827)
    ·
      refine ⟨34753365264419766892684241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23168910176279844595122827 34753365264419766892684241)
      ·
        refine ⟨26065023948314825169513181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34753365264419766892684241 26065023948314825169513181)
        ·
          refine ⟨9774383980618059438567443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26065023948314825169513181 9774383980618059438567443)
          ·
            refine ⟨14661575970927089157851165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9774383980618059438567443 14661575970927089157851165)
            ·
              refine ⟨5498090989097658434194187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14661575970927089157851165 5498090989097658434194187)
              ·
                refine ⟨8247136483646487651291281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498090989097658434194187 8247136483646487651291281)
                ·
                  refine ⟨6185352362734865738468461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8247136483646487651291281 6185352362734865738468461)
                  ·
                    refine ⟨2319507136025574651925673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6185352362734865738468461 2319507136025574651925673)
                    ·
                      refine ⟨1739630352019180988944255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319507136025574651925673 1739630352019180988944255)
                      ·
                        rfl

theorem cell23_3387918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3387918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387918 prefixEnd_3387918 := by exact prefixLift 3387918
  have htrace : WordTrace (prefixWord ++ tailWord_3387918) baseStart_3387918 baseEnd_3387918 := by
    simpa [prefixWord, tailWord_3387918, baseEnd_3387918] using wordTrace_append hprefix tailTrace_3387918
  have hstable : (prefixWord ++ tailWord_3387918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387918).length < 2 ^ (prefixWord ++ tailWord_3387918).sum := by decide
  have hdescent : baseEnd_3387918 < baseStart_3387918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387928 : List Nat := [2, 1, 2, 3, 3, 3, 2, 1, 1, 5]
def baseStart_3387928 : Nat := 118140960795 + 3387928 * 2 ^ 59
def prefixEnd_3387928 : Nat := 4983230072969 + 3 ^ 40 * 3387928 * 2
def baseEnd_3387928 : Nat := 579878495608575316606403

theorem tailTrace_3387928 : CollatzResearch.WordTrace tailWord_3387928 prefixEnd_3387928 579878495608575316606403 := by
  unfold tailWord_3387928
  simp only [CollatzResearch.WordTrace]
  refine ⟨61783942835061471440926219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82378590446748628587901625 61783942835061471440926219)
  ·
    refine ⟨92675914252592207161389329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61783942835061471440926219 92675914252592207161389329)
    ·
      refine ⟨69506935689444155371041997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92675914252592207161389329 69506935689444155371041997)
      ·
        refine ⟨26065100883541558264140749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69506935689444155371041997 26065100883541558264140749)
        ·
          refine ⟨9774412831328084349052781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26065100883541558264140749 9774412831328084349052781)
          ·
            refine ⟨3665404811748031630894793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9774412831328084349052781 3665404811748031630894793)
            ·
              refine ⟨2749053608811023723171095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3665404811748031630894793 2749053608811023723171095)
              ·
                refine ⟨4123580413216535584756643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749053608811023723171095 4123580413216535584756643)
                ·
                  refine ⟨6185370619824803377134965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123580413216535584756643 6185370619824803377134965)
                  ·
                    refine ⟨579878495608575316606403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6185370619824803377134965 579878495608575316606403)
                    ·
                      rfl

theorem cell23_3387928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_3387928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387928 prefixEnd_3387928 := by exact prefixLift 3387928
  have htrace : WordTrace (prefixWord ++ tailWord_3387928) baseStart_3387928 baseEnd_3387928 := by
    simpa [prefixWord, tailWord_3387928, baseEnd_3387928] using wordTrace_append hprefix tailTrace_3387928
  have hstable : (prefixWord ++ tailWord_3387928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387928).length < 2 ^ (prefixWord ++ tailWord_3387928).sum := by decide
  have hdescent : baseEnd_3387928 < baseStart_3387928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387937 : List Nat := [1, 2, 3, 2, 2, 1, 12]
def baseStart_3387937 : Nat := 118140960795 + 3387937 * 2 ^ 59
def prefixEnd_3387937 : Nat := 4983230072969 + 3 ^ 40 * 3387937 * 2
def baseEnd_3387937 : Nat := 21477038372242177958107

theorem tailTrace_3387937 : CollatzResearch.WordTrace tailWord_3387937 prefixEnd_3387937 21477038372242177958107 := by
  unfold tailWord_3387937
  simp only [CollatzResearch.WordTrace]
  refine ⟨123568213927090337418930065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82378809284726891612620043 123568213927090337418930065)
  ·
    refine ⟨92676160445317753064197549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123568213927090337418930065 92676160445317753064197549)
    ·
      refine ⟨34753560166994157399074081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92676160445317753064197549 34753560166994157399074081)
      ·
        refine ⟨26065170125245618049305561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34753560166994157399074081 26065170125245618049305561)
        ·
          refine ⟨19548877593934213536979171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26065170125245618049305561 19548877593934213536979171)
          ·
            refine ⟨29323316390901320305468757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19548877593934213536979171 29323316390901320305468757)
            ·
              refine ⟨21477038372242177958107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29323316390901320305468757 21477038372242177958107)
              ·
                rfl

theorem cell23_3387937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 12].length) (baseStart_3387937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387937 prefixEnd_3387937 := by exact prefixLift 3387937
  have htrace : WordTrace (prefixWord ++ tailWord_3387937) baseStart_3387937 baseEnd_3387937 := by
    simpa [prefixWord, tailWord_3387937, baseEnd_3387937] using wordTrace_append hprefix tailTrace_3387937
  have hstable : (prefixWord ++ tailWord_3387937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387937).length < 2 ^ (prefixWord ++ tailWord_3387937).sum := by decide
  have hdescent : baseEnd_3387937 < baseStart_3387937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387941 : List Nat := [1, 3, 1, 2, 2, 1, 5, 2, 2, 4]
def baseStart_3387941 : Nat := 118140960795 + 3387941 * 2 ^ 59
def prefixEnd_3387941 : Nat := 4983230072969 + 3 ^ 40 * 3387941 * 2
def baseEnd_3387941 : Nat := 579880720691411466318883

theorem tailTrace_3387941 : CollatzResearch.WordTrace tailWord_3387941 prefixEnd_3387941 579880720691411466318883 := by
  unfold tailWord_3387941
  simp only [CollatzResearch.WordTrace]
  refine ⟨123568359819075846102075677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82378906546050564068050451 123568359819075846102075677)
  ·
    refine ⟨46338134932153442288278379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123568359819075846102075677 46338134932153442288278379)
    ·
      refine ⟨69507202398230163432417569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46338134932153442288278379 69507202398230163432417569)
      ·
        refine ⟨52130401798672622574313177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69507202398230163432417569 52130401798672622574313177)
        ·
          refine ⟨39097801349004466930734883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52130401798672622574313177 39097801349004466930734883)
          ·
            refine ⟨58646702023506700396102325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39097801349004466930734883 58646702023506700396102325)
            ·
              refine ⟨5498128314703753162134593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58646702023506700396102325 5498128314703753162134593)
              ·
                refine ⟨4123596236027814871600945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498128314703753162134593 4123596236027814871600945)
                ·
                  refine ⟨3092697177020861153700709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4123596236027814871600945 3092697177020861153700709)
                  ·
                    refine ⟨579880720691411466318883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3092697177020861153700709 579880720691411466318883)
                    ·
                      rfl

theorem cell23_3387941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_3387941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387941 prefixEnd_3387941 := by exact prefixLift 3387941
  have htrace : WordTrace (prefixWord ++ tailWord_3387941) baseStart_3387941 baseEnd_3387941 := by
    simpa [prefixWord, tailWord_3387941, baseEnd_3387941] using wordTrace_append hprefix tailTrace_3387941
  have hstable : (prefixWord ++ tailWord_3387941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387941).length < 2 ^ (prefixWord ++ tailWord_3387941).sum := by decide
  have hdescent : baseEnd_3387941 < baseStart_3387941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3387958 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3387958 : Nat := 118140960795 + 3387958 * 2 ^ 59
def prefixEnd_3387958 : Nat := 4983230072969 + 3 ^ 40 * 3387958 * 2
def baseEnd_3387958 : Nat := 579883630415120277481357

theorem tailTrace_3387958 : CollatzResearch.WordTrace tailWord_3387958 prefixEnd_3387958 579883630415120277481357 := by
  unfold tailWord_3387958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7723061241250891125340283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82379319906676172003629685 7723061241250891125340283)
  ·
    refine ⟨11584591861876336688010425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7723061241250891125340283 11584591861876336688010425)
    ·
      refine ⟨8688443896407252516007819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11584591861876336688010425 8688443896407252516007819)
      ·
        refine ⟨13032665844610878774011729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8688443896407252516007819 13032665844610878774011729)
        ·
          refine ⟨9774499383458159080508797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13032665844610878774011729 9774499383458159080508797)
          ·
            refine ⟨3665437268796809655190799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9774499383458159080508797 3665437268796809655190799)
            ·
              refine ⟨5498155903195214482786199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665437268796809655190799 5498155903195214482786199)
              ·
                refine ⟨8247233854792821724179299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498155903195214482786199 8247233854792821724179299)
                ·
                  refine ⟨12370850782189232586268949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247233854792821724179299 12370850782189232586268949)
                  ·
                    refine ⟨579883630415120277481357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12370850782189232586268949 579883630415120277481357)
                    ·
                      rfl

theorem cell23_3387958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3387958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3387958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3387958 prefixEnd_3387958 := by exact prefixLift 3387958
  have htrace : WordTrace (prefixWord ++ tailWord_3387958) baseStart_3387958 baseEnd_3387958 := by
    simpa [prefixWord, tailWord_3387958, baseEnd_3387958] using wordTrace_append hprefix tailTrace_3387958
  have hstable : (prefixWord ++ tailWord_3387958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3387958).length < 2 ^ (prefixWord ++ tailWord_3387958).sum := by decide
  have hdescent : baseEnd_3387958 < baseStart_3387958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3387958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388004 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 2, 3, 4]
def baseStart_3388004 : Nat := 118140960795 + 3388004 * 2 ^ 59
def prefixEnd_3388004 : Nat := 4983230072969 + 3 ^ 40 * 3388004 * 2
def baseEnd_3388004 : Nat := 1739674511355467652468859

theorem tailTrace_3388004 : CollatzResearch.WordTrace tailWord_3388004 prefixEnd_3388004 1739674511355467652468859 := by
  unfold tailWord_3388004
  simp only [CollatzResearch.WordTrace]
  refine ⟨61785328808923803930809533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82380438411898405241079377 61785328808923803930809533)
  ·
    refine ⟨23169498303346426474053575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61785328808923803930809533 23169498303346426474053575)
    ·
      refine ⟨34754247455019639711080363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23169498303346426474053575 34754247455019639711080363)
      ·
        refine ⟨52131371182529459566620545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34754247455019639711080363 52131371182529459566620545)
        ·
          refine ⟨39098528386897094674965409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52131371182529459566620545 39098528386897094674965409)
          ·
            refine ⟨29323896290172821006224057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39098528386897094674965409 29323896290172821006224057)
            ·
              refine ⟨21992922217629615754668043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29323896290172821006224057 21992922217629615754668043)
              ·
                refine ⟨32989383326444423632002065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21992922217629615754668043 32989383326444423632002065)
                ·
                  refine ⟨24742037494833317724001549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989383326444423632002065 24742037494833317724001549)
                  ·
                    refine ⟨9278264060562494146500581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24742037494833317724001549 9278264060562494146500581)
                    ·
                      refine ⟨1739674511355467652468859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9278264060562494146500581 1739674511355467652468859)
                      ·
                        rfl

theorem cell23_3388004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_3388004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388004 prefixEnd_3388004 := by exact prefixLift 3388004
  have htrace : WordTrace (prefixWord ++ tailWord_3388004) baseStart_3388004 baseEnd_3388004 := by
    simpa [prefixWord, tailWord_3388004, baseEnd_3388004] using wordTrace_append hprefix tailTrace_3388004
  have hstable : (prefixWord ++ tailWord_3388004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388004).length < 2 ^ (prefixWord ++ tailWord_3388004).sum := by decide
  have hdescent : baseEnd_3388004 < baseStart_3388004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388024 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3]
def baseStart_3388024 : Nat := 118140960795 + 3388024 * 2 ^ 59
def prefixEnd_3388024 : Nat := 4983230072969 + 3 ^ 40 * 3388024 * 2
def baseEnd_3388024 : Nat := 1739684780968557574218767

theorem tailTrace_3388024 : CollatzResearch.WordTrace tailWord_3388024 prefixEnd_3388024 1739684780968557574218767 := by
  unfold tailWord_3388024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61785693538887575638673563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82380924718516767518231417 61785693538887575638673563)
  ·
    refine ⟨92678540308331363458010345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61785693538887575638673563 92678540308331363458010345)
    ·
      refine ⟨69508905231248522593507759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92678540308331363458010345 69508905231248522593507759)
      ·
        refine ⟨104263357846872783890261639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69508905231248522593507759 104263357846872783890261639)
        ·
          refine ⟨156395036770309175835392459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104263357846872783890261639 156395036770309175835392459)
          ·
            refine ⟨234592555155463763753088689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156395036770309175835392459 234592555155463763753088689)
            ·
              refine ⟨175944416366597822814816517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234592555155463763753088689 175944416366597822814816517)
              ·
                refine ⟨32989578068737091777778097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 175944416366597822814816517 32989578068737091777778097)
                ·
                  refine ⟨24742183551552818833333573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32989578068737091777778097 24742183551552818833333573)
                  ·
                    refine ⟨4639159415916153531250045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24742183551552818833333573 4639159415916153531250045)
                    ·
                      refine ⟨1739684780968557574218767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4639159415916153531250045 1739684780968557574218767)
                      ·
                        rfl

theorem cell23_3388024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_3388024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388024 prefixEnd_3388024 := by exact prefixLift 3388024
  have htrace : WordTrace (prefixWord ++ tailWord_3388024) baseStart_3388024 baseEnd_3388024 := by
    simpa [prefixWord, tailWord_3388024, baseEnd_3388024] using wordTrace_append hprefix tailTrace_3388024
  have hstable : (prefixWord ++ tailWord_3388024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388024).length < 2 ^ (prefixWord ++ tailWord_3388024).sum := by decide
  have hdescent : baseEnd_3388024 < baseStart_3388024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388025 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 1, 3, 2]
def baseStart_3388025 : Nat := 118140960795 + 3388025 * 2 ^ 59
def prefixEnd_3388025 : Nat := 4983230072969 + 3 ^ 40 * 3388025 * 2
def baseEnd_3388025 : Nat := 1739685294449212070306263

theorem tailTrace_3388025 : CollatzResearch.WordTrace tailWord_3388025 prefixEnd_3388025 1739685294449212070306263 := by
  unfold tailWord_3388025
  simp only [CollatzResearch.WordTrace]
  refine ⟨123571423550771528448133529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82380949033847685632089019 123571423550771528448133529)
  ·
    refine ⟨92678567663078646336100147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123571423550771528448133529 92678567663078646336100147)
    ·
      refine ⟨139017851494617969504150221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92678567663078646336100147 139017851494617969504150221)
      ·
        refine ⟨52131694310481738564056333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139017851494617969504150221 52131694310481738564056333)
        ·
          refine ⟨19549385366430651961521125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52131694310481738564056333 19549385366430651961521125)
          ·
            refine ⟨3665509756205747242785211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19549385366430651961521125 3665509756205747242785211)
            ·
              refine ⟨5498264634308620864177817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3665509756205747242785211 5498264634308620864177817)
              ·
                refine ⟨4123698475731465648133363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498264634308620864177817 4123698475731465648133363)
                ·
                  refine ⟨6185547713597198472200045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123698475731465648133363 6185547713597198472200045)
                  ·
                    refine ⟨2319580392598949427075017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6185547713597198472200045 2319580392598949427075017)
                    ·
                      refine ⟨1739685294449212070306263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319580392598949427075017 1739685294449212070306263)
                      ·
                        rfl

theorem cell23_3388025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_3388025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388025 prefixEnd_3388025 := by exact prefixLift 3388025
  have htrace : WordTrace (prefixWord ++ tailWord_3388025) baseStart_3388025 baseEnd_3388025 := by
    simpa [prefixWord, tailWord_3388025, baseEnd_3388025] using wordTrace_append hprefix tailTrace_3388025
  have hstable : (prefixWord ++ tailWord_3388025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388025).length < 2 ^ (prefixWord ++ tailWord_3388025).sum := by decide
  have hdescent : baseEnd_3388025 < baseStart_3388025 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388042 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3388042 : Nat := 118140960795 + 3388042 * 2 ^ 59
def prefixEnd_3388042 : Nat := 4983230072969 + 3 ^ 40 * 3388042 * 2
def baseEnd_3388042 : Nat := 1739694023620338503793685

theorem tailTrace_3388042 : CollatzResearch.WordTrace tailWord_3388042 prefixEnd_3388042 1739694023620338503793685 := by
  unfold tailWord_3388042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30893010897927485087875595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82381362394473293567668253 30893010897927485087875595)
  ·
    refine ⟨46339516346891227631813393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30893010897927485087875595 46339516346891227631813393)
    ·
      refine ⟨34754637260168420723860045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46339516346891227631813393 34754637260168420723860045)
      ·
        refine ⟨13032988972563157771447517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34754637260168420723860045 13032988972563157771447517)
        ·
          refine ⟨4887370864711184164292819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13032988972563157771447517 4887370864711184164292819)
          ·
            refine ⟨7331056297066776246439229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887370864711184164292819 7331056297066776246439229)
            ·
              refine ⟨2749146111400041092414711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7331056297066776246439229 2749146111400041092414711)
              ·
                refine ⟨4123719167100061638622067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749146111400041092414711 4123719167100061638622067)
                ·
                  refine ⟨6185578750650092457933101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4123719167100061638622067 6185578750650092457933101)
                  ·
                    refine ⟨2319592031493784671724913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6185578750650092457933101 2319592031493784671724913)
                    ·
                      refine ⟨1739694023620338503793685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319592031493784671724913 1739694023620338503793685)
                      ·
                        rfl

theorem cell23_3388042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3388042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388042 prefixEnd_3388042 := by exact prefixLift 3388042
  have htrace : WordTrace (prefixWord ++ tailWord_3388042) baseStart_3388042 baseEnd_3388042 := by
    simpa [prefixWord, tailWord_3388042, baseEnd_3388042] using wordTrace_append hprefix tailTrace_3388042
  have hstable : (prefixWord ++ tailWord_3388042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388042).length < 2 ^ (prefixWord ++ tailWord_3388042).sum := by decide
  have hdescent : baseEnd_3388042 < baseStart_3388042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388055 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_3388055 : Nat := 118140960795 + 3388055 * 2 ^ 59
def prefixEnd_3388055 : Nat := 4983230072969 + 3 ^ 40 * 3388055 * 2
def baseEnd_3388055 : Nat := 1739700698868846952931125

theorem tailTrace_3388055 : CollatzResearch.WordTrace tailWord_3388055 prefixEnd_3388055 1739700698868846952931125 := by
  unfold tailWord_3388055
  simp only [CollatzResearch.WordTrace]
  refine ⟨123572517740662843571725619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82381678493775229047817079 123572517740662843571725619)
  ·
    refine ⟨185358776610994265357588429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123572517740662843571725619 185358776610994265357588429)
    ·
      refine ⟨69509541229122849509095661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185358776610994265357588429 69509541229122849509095661)
      ·
        refine ⟨26066077960921068565910873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69509541229122849509095661 26066077960921068565910873)
        ·
          refine ⟨19549558470690801424433155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26066077960921068565910873 19549558470690801424433155)
          ·
            refine ⟨29324337706036202136649733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19549558470690801424433155 29324337706036202136649733)
            ·
              refine ⟨5498313319881787900621825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29324337706036202136649733 5498313319881787900621825)
              ·
                refine ⟨4123734989911340925466369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5498313319881787900621825 4123734989911340925466369)
                ·
                  refine ⟨3092801242433505694099777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4123734989911340925466369 3092801242433505694099777)
                  ·
                    refine ⟨2319600931825129270574833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092801242433505694099777 2319600931825129270574833)
                    ·
                      refine ⟨1739700698868846952931125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319600931825129270574833 1739700698868846952931125)
                      ·
                        rfl

theorem cell23_3388055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_3388055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388055 prefixEnd_3388055 := by exact prefixLift 3388055
  have htrace : WordTrace (prefixWord ++ tailWord_3388055) baseStart_3388055 baseEnd_3388055 := by
    simpa [prefixWord, tailWord_3388055, baseEnd_3388055] using wordTrace_append hprefix tailTrace_3388055
  have hstable : (prefixWord ++ tailWord_3388055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388055).length < 2 ^ (prefixWord ++ tailWord_3388055).sum := by decide
  have hdescent : baseEnd_3388055 < baseStart_3388055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388078 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3388078 : Nat := 118140960795 + 3388078 * 2 ^ 59
def prefixEnd_3388078 : Nat := 4983230072969 + 3 ^ 40 * 3388078 * 2
def baseEnd_3388078 : Nat := 193301389880433373660391

theorem tailTrace_3388078 : CollatzResearch.WordTrace tailWord_3388078 prefixEnd_3388078 193301389880433373660391 := by
  unfold tailWord_3388078
  simp only [CollatzResearch.WordTrace]
  refine ⟨15446669577447439812476611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82382237746386345666541925 15446669577447439812476611)
  ·
    refine ⟨23170004366171159718714917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15446669577447439812476611 23170004366171159718714917)
    ·
      refine ⟨4344375818657092447259047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23170004366171159718714917 4344375818657092447259047)
      ·
        refine ⟨6516563727985638670888571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344375818657092447259047 6516563727985638670888571)
        ·
          refine ⟨9774845591978458006332857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516563727985638670888571 9774845591978458006332857)
          ·
            refine ⟨7331134193983843504749643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9774845591978458006332857 7331134193983843504749643)
            ·
              refine ⟨10996701290975765257124465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7331134193983843504749643 10996701290975765257124465)
              ·
                refine ⟨8247525968231823942843349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10996701290975765257124465 8247525968231823942843349)
                ·
                  refine ⟨193301389880433373660391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8247525968231823942843349 193301389880433373660391)
                  ·
                    rfl

theorem cell23_3388078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3388078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388078 prefixEnd_3388078 := by exact prefixLift 3388078
  have htrace : WordTrace (prefixWord ++ tailWord_3388078) baseStart_3388078 baseEnd_3388078 := by
    simpa [prefixWord, tailWord_3388078, baseEnd_3388078] using wordTrace_append hprefix tailTrace_3388078
  have hstable : (prefixWord ++ tailWord_3388078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388078).length < 2 ^ (prefixWord ++ tailWord_3388078).sum := by decide
  have hdescent : baseEnd_3388078 < baseStart_3388078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388141 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3388141 : Nat := 118140960795 + 3388141 * 2 ^ 59
def prefixEnd_3388141 : Nat := 4983230072969 + 3 ^ 40 * 3388141 * 2
def baseEnd_3388141 : Nat := 1739744858205133616455729

theorem tailTrace_3388141 : CollatzResearch.WordTrace tailWord_3388141 prefixEnd_3388141 1739744858205133616455729 := by
  unfold tailWord_3388141
  simp only [CollatzResearch.WordTrace]
  refine ⟨123575654418351280259356277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82383769612234186839570851 123575654418351280259356277)
  ·
    refine ⟨11585217601720432524314651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123575654418351280259356277 11585217601720432524314651)
    ·
      refine ⟨17377826402580648786471977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11585217601720432524314651 17377826402580648786471977)
      ·
        refine ⟨13033369801935486589853983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17377826402580648786471977 13033369801935486589853983)
        ·
          refine ⟨19550054702903229884780975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13033369801935486589853983 19550054702903229884780975)
          ·
            refine ⟨29325082054354844827171463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19550054702903229884780975 29325082054354844827171463)
            ·
              refine ⟨43987623081532267240757195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29325082054354844827171463 43987623081532267240757195)
              ·
                refine ⟨65981434622298400861135793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43987623081532267240757195 65981434622298400861135793)
                ·
                  refine ⟨49486075966723800645851845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65981434622298400861135793 49486075966723800645851845)
                  ·
                    refine ⟨9278639243760712621097221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49486075966723800645851845 9278639243760712621097221)
                    ·
                      refine ⟨1739744858205133616455729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9278639243760712621097221 1739744858205133616455729)
                      ·
                        rfl

theorem cell23_3388141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3388141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388141 prefixEnd_3388141 := by exact prefixLift 3388141
  have htrace : WordTrace (prefixWord ++ tailWord_3388141) baseStart_3388141 baseEnd_3388141 := by
    simpa [prefixWord, tailWord_3388141, baseEnd_3388141] using wordTrace_append hprefix tailTrace_3388141
  have hstable : (prefixWord ++ tailWord_3388141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388141).length < 2 ^ (prefixWord ++ tailWord_3388141).sum := by decide
  have hdescent : baseEnd_3388141 < baseStart_3388141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388181 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 3, 5]
def baseStart_3388181 : Nat := 118140960795 + 3388181 * 2 ^ 59
def prefixEnd_3388181 : Nat := 4983230072969 + 3 ^ 40 * 3388181 * 2
def baseEnd_3388181 : Nat := 579921799143771153318515

theorem tailTrace_3388181 : CollatzResearch.WordTrace tailWord_3388181 prefixEnd_3388181 579921799143771153318515 := by
  unfold tailWord_3388181
  simp only [CollatzResearch.WordTrace]
  refine ⟨123577113338206367090812397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82384742225470911393874931 123577113338206367090812397)
  ·
    refine ⟨46341417501827387659054649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123577113338206367090812397 46341417501827387659054649)
    ·
      refine ⟨34756063126370540744290987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46341417501827387659054649 34756063126370540744290987)
      ·
        refine ⟨52134094689555811116436481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34756063126370540744290987 52134094689555811116436481)
        ·
          refine ⟨39100571017166858337327361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52134094689555811116436481 39100571017166858337327361)
          ·
            refine ⟨29325428262875143752995521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39100571017166858337327361 29325428262875143752995521)
            ·
              refine ⟨21994071197156357814746641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29325428262875143752995521 21994071197156357814746641)
              ·
                refine ⟨16495553397867268361059981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21994071197156357814746641 16495553397867268361059981)
                ·
                  refine ⟨6185832524200225635397493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16495553397867268361059981 6185832524200225635397493)
                  ·
                    refine ⟨579921799143771153318515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6185832524200225635397493 579921799143771153318515)
                    ·
                      rfl

theorem cell23_3388181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_3388181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388181 prefixEnd_3388181 := by exact prefixLift 3388181
  have htrace : WordTrace (prefixWord ++ tailWord_3388181) baseStart_3388181 baseEnd_3388181 := by
    simpa [prefixWord, tailWord_3388181, baseEnd_3388181] using wordTrace_append hprefix tailTrace_3388181
  have hstable : (prefixWord ++ tailWord_3388181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388181).length < 2 ^ (prefixWord ++ tailWord_3388181).sum := by decide
  have hdescent : baseEnd_3388181 < baseStart_3388181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388201 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 4]
def baseStart_3388201 : Nat := 118140960795 + 3388201 * 2 ^ 59
def prefixEnd_3388201 : Nat := 4983230072969 + 3 ^ 40 * 3388201 * 2
def baseEnd_3388201 : Nat := 1739775667044403381705453

theorem tailTrace_3388201 : CollatzResearch.WordTrace tailWord_3388201 prefixEnd_3388201 1739775667044403381705453 := by
  unfold tailWord_3388201
  simp only [CollatzResearch.WordTrace]
  refine ⟨123577842798133910506540457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82385228532089273671026971 123577842798133910506540457)
  ·
    refine ⟨92683382098600432879905343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123577842798133910506540457 92683382098600432879905343)
    ·
      refine ⟨139025073147900649319858015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92683382098600432879905343 139025073147900649319858015)
      ·
        refine ⟨208537609721850973979787023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139025073147900649319858015 208537609721850973979787023)
        ·
          refine ⟨312806414582776460969680535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208537609721850973979787023 312806414582776460969680535)
          ·
            refine ⟨469209621874164691454520803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312806414582776460969680535 469209621874164691454520803)
            ·
              refine ⟨703814432811247037181781205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469209621874164691454520803 703814432811247037181781205)
              ·
                refine ⟨16495650769013602433947997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 703814432811247037181781205 16495650769013602433947997)
                ·
                  refine ⟨6185869038380100912730499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16495650769013602433947997 6185869038380100912730499)
                  ·
                    refine ⟨9278803557570151369095749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6185869038380100912730499 9278803557570151369095749)
                    ·
                      refine ⟨1739775667044403381705453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9278803557570151369095749 1739775667044403381705453)
                      ·
                        rfl

theorem cell23_3388201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_3388201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388201 prefixEnd_3388201 := by exact prefixLift 3388201
  have htrace : WordTrace (prefixWord ++ tailWord_3388201) baseStart_3388201 baseEnd_3388201 := by
    simpa [prefixWord, tailWord_3388201, baseEnd_3388201] using wordTrace_append hprefix tailTrace_3388201
  have hstable : (prefixWord ++ tailWord_3388201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388201).length < 2 ^ (prefixWord ++ tailWord_3388201).sum := by decide
  have hdescent : baseEnd_3388201 < baseStart_3388201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388211 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 3, 6]
def baseStart_3388211 : Nat := 118140960795 + 3388211 * 2 ^ 59
def prefixEnd_3388211 : Nat := 4983230072969 + 3 ^ 40 * 3388211 * 2
def baseEnd_3388211 : Nat := 579926933950316114193469

theorem tailTrace_3388211 : CollatzResearch.WordTrace tailWord_3388211 prefixEnd_3388211 579926933950316114193469 := by
  unfold tailWord_3388211
  simp only [CollatzResearch.WordTrace]
  refine ⟨123578207528097682214404487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82385471685398454809602991 123578207528097682214404487)
  ·
    refine ⟨185367311292146523321606731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123578207528097682214404487 185367311292146523321606731)
    ·
      refine ⟨278050966938219784982410097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185367311292146523321606731 278050966938219784982410097)
      ·
        refine ⟨208538225203664838736807573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278050966938219784982410097 208538225203664838736807573)
        ·
          refine ⟨9775229306421789315787855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208538225203664838736807573 9775229306421789315787855)
          ·
            refine ⟨14662843959632683973681783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775229306421789315787855 14662843959632683973681783)
            ·
              refine ⟨21994265939449025960522675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14662843959632683973681783 21994265939449025960522675)
              ·
                refine ⟨32991398909173538940784013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994265939449025960522675 32991398909173538940784013)
                ·
                  refine ⟨12371774590940077102794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32991398909173538940784013 12371774590940077102794005)
                  ·
                    refine ⟨579926933950316114193469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12371774590940077102794005 579926933950316114193469)
                    ·
                      rfl

theorem cell23_3388211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 6].length) (baseStart_3388211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388211 prefixEnd_3388211 := by exact prefixLift 3388211
  have htrace : WordTrace (prefixWord ++ tailWord_3388211) baseStart_3388211 baseEnd_3388211 := by
    simpa [prefixWord, tailWord_3388211, baseEnd_3388211] using wordTrace_append hprefix tailTrace_3388211
  have hstable : (prefixWord ++ tailWord_3388211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388211).length < 2 ^ (prefixWord ++ tailWord_3388211).sum := by decide
  have hdescent : baseEnd_3388211 < baseStart_3388211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388231 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3388231 : Nat := 118140960795 + 3388231 * 2 ^ 59
def prefixEnd_3388231 : Nat := 4983230072969 + 3 ^ 40 * 3388231 * 2
def baseEnd_3388231 : Nat := 1739791071464038264330315

theorem tailTrace_3388231 : CollatzResearch.WordTrace tailWord_3388231 prefixEnd_3388231 1739791071464038264330315 := by
  unfold tailWord_3388231
  simp only [CollatzResearch.WordTrace]
  refine ⟨123578936988025225630132547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82385957992016817086755031 123578936988025225630132547)
  ·
    refine ⟨185368405482037838445198821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123578936988025225630132547 185368405482037838445198821)
    ·
      refine ⟨34756576027882094708474779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185368405482037838445198821 34756576027882094708474779)
      ·
        refine ⟨52134864041823142062712169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34756576027882094708474779 52134864041823142062712169)
        ·
          refine ⟨39101148031367356547034127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52134864041823142062712169 39101148031367356547034127)
          ·
            refine ⟨58651722047051034820551191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39101148031367356547034127 58651722047051034820551191)
            ·
              refine ⟨87977583070576552230826787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58651722047051034820551191 87977583070576552230826787)
              ·
                refine ⟨131966374605864828346240181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87977583070576552230826787 131966374605864828346240181)
                ·
                  refine ⟨12371847619299827657460017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131966374605864828346240181 12371847619299827657460017)
                  ·
                    refine ⟨9278885714474870743095013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12371847619299827657460017 9278885714474870743095013)
                    ·
                      refine ⟨1739791071464038264330315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9278885714474870743095013 1739791071464038264330315)
                      ·
                        rfl

theorem cell23_3388231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3388231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388231 prefixEnd_3388231 := by exact prefixLift 3388231
  have htrace : WordTrace (prefixWord ++ tailWord_3388231) baseStart_3388231 baseEnd_3388231 := by
    simpa [prefixWord, tailWord_3388231, baseEnd_3388231] using wordTrace_append hprefix tailTrace_3388231
  have hstable : (prefixWord ++ tailWord_3388231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388231).length < 2 ^ (prefixWord ++ tailWord_3388231).sum := by decide
  have hdescent : baseEnd_3388231 < baseStart_3388231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388252 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 5, 2, 2]
def baseStart_3388252 : Nat := 118140960795 + 3388252 * 2 ^ 59
def prefixEnd_3388252 : Nat := 4983230072969 + 3 ^ 40 * 3388252 * 2
def baseEnd_3388252 : Nat := 1739801854557782682167719

theorem tailTrace_3388252 : CollatzResearch.WordTrace tailWord_3388252 prefixEnd_3388252 1739801854557782682167719 := by
  unfold tailWord_3388252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61789851460474573108323505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82386468613966097477764673 61789851460474573108323505)
  ·
    refine ⟨46342388595355929831242629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61789851460474573108323505 46342388595355929831242629)
    ·
      refine ⟨8689197861629236843357993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46342388595355929831242629 8689197861629236843357993)
      ·
        refine ⟨6516898396221927632518495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8689197861629236843357993 6516898396221927632518495)
        ·
          refine ⟨9775347594332891448777743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6516898396221927632518495 9775347594332891448777743)
          ·
            refine ⟨14663021391499337173166615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9775347594332891448777743 14663021391499337173166615)
            ·
              refine ⟨21994532087249005759749923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14663021391499337173166615 21994532087249005759749923)
              ·
                refine ⟨32991798130873508639624885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21994532087249005759749923 32991798130873508639624885)
                ·
                  refine ⟨3092981074769391434964833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32991798130873508639624885 3092981074769391434964833)
                  ·
                    refine ⟨2319735806077043576223625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3092981074769391434964833 2319735806077043576223625)
                    ·
                      refine ⟨1739801854557782682167719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319735806077043576223625 1739801854557782682167719)
                      ·
                        rfl

theorem cell23_3388252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_3388252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388252 prefixEnd_3388252 := by exact prefixLift 3388252
  have htrace : WordTrace (prefixWord ++ tailWord_3388252) baseStart_3388252 baseEnd_3388252 := by
    simpa [prefixWord, tailWord_3388252, baseEnd_3388252] using wordTrace_append hprefix tailTrace_3388252
  have hstable : (prefixWord ++ tailWord_3388252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388252).length < 2 ^ (prefixWord ++ tailWord_3388252).sum := by decide
  have hdescent : baseEnd_3388252 < baseStart_3388252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388268 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 3]
def baseStart_3388268 : Nat := 118140960795 + 3388268 * 2 ^ 59
def prefixEnd_3388268 : Nat := 4983230072969 + 3 ^ 40 * 3388268 * 2
def baseEnd_3388268 : Nat := 1739810070248254619567645

theorem tailTrace_3388268 : CollatzResearch.WordTrace tailWord_3388268 prefixEnd_3388268 1739810070248254619567645 := by
  unfold tailWord_3388268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61790143244445590474614729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82386857659260787299486305 61790143244445590474614729)
  ·
    refine ⟨46342607433334192855961047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61790143244445590474614729 46342607433334192855961047)
    ·
      refine ⟨69513911150001289283941571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46342607433334192855961047 69513911150001289283941571)
      ·
        refine ⟨104270866725001933925912357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69513911150001289283941571 104270866725001933925912357)
        ·
          refine ⟨19550787510937862611108567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104270866725001933925912357 19550787510937862611108567)
          ·
            refine ⟨29326181266406793916662851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19550787510937862611108567 29326181266406793916662851)
            ·
              refine ⟨43989271899610190874994277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29326181266406793916662851 43989271899610190874994277)
              ·
                refine ⟨8247988481176910789061427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43989271899610190874994277 8247988481176910789061427)
                ·
                  refine ⟨12371982721765366183592141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8247988481176910789061427 12371982721765366183592141)
                  ·
                    refine ⟨4639493520662012318847053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12371982721765366183592141 4639493520662012318847053)
                    ·
                      refine ⟨1739810070248254619567645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4639493520662012318847053 1739810070248254619567645)
                      ·
                        rfl

theorem cell23_3388268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 3].length) (baseStart_3388268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388268 prefixEnd_3388268 := by exact prefixLift 3388268
  have htrace : WordTrace (prefixWord ++ tailWord_3388268) baseStart_3388268 baseEnd_3388268 := by
    simpa [prefixWord, tailWord_3388268, baseEnd_3388268] using wordTrace_append hprefix tailTrace_3388268
  have hstable : (prefixWord ++ tailWord_3388268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388268).length < 2 ^ (prefixWord ++ tailWord_3388268).sum := by decide
  have hdescent : baseEnd_3388268 < baseStart_3388268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388286 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_3388286 : Nat := 118140960795 + 3388286 * 2 ^ 59
def prefixEnd_3388286 : Nat := 4983230072969 + 3 ^ 40 * 3388286 * 2
def baseEnd_3388286 : Nat := 1739819312900035549142563

theorem tailTrace_3388286 : CollatzResearch.WordTrace tailWord_3388286 prefixEnd_3388286 1739819312900035549142563 := by
  unfold tailWord_3388286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15447617875353246252923089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82387295335217313348923141 15447617875353246252923089)
  ·
    refine ⟨11585713406514934689692317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15447617875353246252923089 11585713406514934689692317)
    ·
      refine ⟨4344642527443100508634619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11585713406514934689692317 4344642527443100508634619)
      ·
        refine ⟨6516963791164650762951929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344642527443100508634619 6516963791164650762951929)
        ·
          refine ⟨4887722843373488072213947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6516963791164650762951929 4887722843373488072213947)
          ·
            refine ⟨7331584265060232108320921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4887722843373488072213947 7331584265060232108320921)
            ·
              refine ⟨5498688198795174081240691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7331584265060232108320921 5498688198795174081240691)
              ·
                refine ⟨8248032298192761121861037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5498688198795174081240691 8248032298192761121861037)
                ·
                  refine ⟨3093012111822285420697889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8248032298192761121861037 3093012111822285420697889)
                  ·
                    refine ⟨2319759083866714065523417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093012111822285420697889 2319759083866714065523417)
                    ·
                      refine ⟨1739819312900035549142563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319759083866714065523417 1739819312900035549142563)
                      ·
                        rfl

theorem cell23_3388286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_3388286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388286 prefixEnd_3388286 := by exact prefixLift 3388286
  have htrace : WordTrace (prefixWord ++ tailWord_3388286) baseStart_3388286 baseEnd_3388286 := by
    simpa [prefixWord, tailWord_3388286, baseEnd_3388286] using wordTrace_append hprefix tailTrace_3388286
  have hstable : (prefixWord ++ tailWord_3388286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388286).length < 2 ^ (prefixWord ++ tailWord_3388286).sum := by decide
  have hdescent : baseEnd_3388286 < baseStart_3388286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388351 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3388351 : Nat := 118140960795 + 3388351 * 2 ^ 59
def prefixEnd_3388351 : Nat := 4983230072969 + 3 ^ 40 * 3388351 * 2
def baseEnd_3388351 : Nat := 1739852689142577794829763

theorem tailTrace_3388351 : CollatzResearch.WordTrace tailWord_3388351 prefixEnd_3388351 1739852689142577794829763 := by
  unfold tailWord_3388351
  simp only [CollatzResearch.WordTrace]
  refine ⟨123583313747590486124500907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82388875831726990749667271 123583313747590486124500907)
  ·
    refine ⟨185374970621385729186751361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123583313747590486124500907 185374970621385729186751361)
    ·
      refine ⟨139031227966039296890063521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185374970621385729186751361 139031227966039296890063521)
      ·
        refine ⟨104273420974529472667547641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139031227966039296890063521 104273420974529472667547641)
        ·
          refine ⟨78205065730897104500660731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104273420974529472667547641 78205065730897104500660731)
          ·
            refine ⟨117307598596345656750991097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78205065730897104500660731 117307598596345656750991097)
            ·
              refine ⟨87980698947259242563243323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117307598596345656750991097 87980698947259242563243323)
              ·
                refine ⟨131971048420888863844864985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87980698947259242563243323 131971048420888863844864985)
                ·
                  refine ⟨98978286315666647883648739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131971048420888863844864985 98978286315666647883648739)
                  ·
                    refine ⟨148467429473499971825473109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98978286315666647883648739 148467429473499971825473109)
                    ·
                      refine ⟨1739852689142577794829763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 148467429473499971825473109 1739852689142577794829763)
                      ·
                        rfl

theorem cell23_3388351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3388351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388351 prefixEnd_3388351 := by exact prefixLift 3388351
  have htrace : WordTrace (prefixWord ++ tailWord_3388351) baseStart_3388351 baseEnd_3388351 := by
    simpa [prefixWord, tailWord_3388351, baseEnd_3388351] using wordTrace_append hprefix tailTrace_3388351
  have hstable : (prefixWord ++ tailWord_3388351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388351).length < 2 ^ (prefixWord ++ tailWord_3388351).sum := by decide
  have hdescent : baseEnd_3388351 < baseStart_3388351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388359 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_3388359 : Nat := 118140960795 + 3388359 * 2 ^ 59
def prefixEnd_3388359 : Nat := 4983230072969 + 3 ^ 40 * 3388359 * 2
def baseEnd_3388359 : Nat := 1739856796987813763529727

theorem tailTrace_3388359 : CollatzResearch.WordTrace tailWord_3388359 prefixEnd_3388359 1739856796987813763529727 := by
  unfold tailWord_3388359
  simp only [CollatzResearch.WordTrace]
  refine ⟨123583605531561503490792131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82389070354374335660528087 123583605531561503490792131)
  ·
    refine ⟨185375408297342255236188197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123583605531561503490792131 185375408297342255236188197)
    ·
      refine ⟨34757889055751672856785287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185375408297342255236188197 34757889055751672856785287)
      ·
        refine ⟨52136833583627509285177931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34757889055751672856785287 52136833583627509285177931)
        ·
          refine ⟨78205250375441263927766897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52136833583627509285177931 78205250375441263927766897)
          ·
            refine ⟨58653937781580947945825173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78205250375441263927766897 58653937781580947945825173)
            ·
              refine ⟨2749403333511606934960555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58653937781580947945825173 2749403333511606934960555)
              ·
                refine ⟨4124105000267410402440833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749403333511606934960555 4124105000267410402440833)
                ·
                  refine ⟨3093078750200557801830625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4124105000267410402440833 3093078750200557801830625)
                  ·
                    refine ⟨2319809062650418351372969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3093078750200557801830625 2319809062650418351372969)
                    ·
                      refine ⟨1739856796987813763529727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319809062650418351372969 1739856796987813763529727)
                      ·
                        rfl

theorem cell23_3388359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_3388359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388359 prefixEnd_3388359 := by exact prefixLift 3388359
  have htrace : WordTrace (prefixWord ++ tailWord_3388359) baseStart_3388359 baseEnd_3388359 := by
    simpa [prefixWord, tailWord_3388359, baseEnd_3388359] using wordTrace_append hprefix tailTrace_3388359
  have hstable : (prefixWord ++ tailWord_3388359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388359).length < 2 ^ (prefixWord ++ tailWord_3388359).sum := by decide
  have hdescent : baseEnd_3388359 < baseStart_3388359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388472 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 6]
def baseStart_3388472 : Nat := 118140960795 + 3388472 * 2 ^ 59
def prefixEnd_3388472 : Nat := 4983230072969 + 3 ^ 40 * 3388472 * 2
def baseEnd_3388472 : Nat := 193323868922419091268523

theorem tailTrace_3388472 : CollatzResearch.WordTrace tailWord_3388472 prefixEnd_3388472 193323868922419091268523 := by
  unfold tailWord_3388472
  simp only [CollatzResearch.WordTrace]
  refine ⟨61793863490076061894827835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82391817986768082526437113 61793863490076061894827835)
  ·
    refine ⟨92690795235114092842241753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61793863490076061894827835 92690795235114092842241753)
    ·
      refine ⟨69518096426335569631681315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92690795235114092842241753 69518096426335569631681315)
      ·
        refine ⟨104277144639503354447521973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69518096426335569631681315 104277144639503354447521973)
        ·
          refine ⟨9775982309953439479455185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104277144639503354447521973 9775982309953439479455185)
          ·
            refine ⟨7331986732465079609591389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9775982309953439479455185 7331986732465079609591389)
            ·
              refine ⟨2749495024674404853596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7331986732465079609591389 2749495024674404853596771)
              ·
                refine ⟨4124242537011607280395157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749495024674404853596771 4124242537011607280395157)
                ·
                  refine ⟨193323868922419091268523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4124242537011607280395157 193323868922419091268523)
                  ·
                    rfl

theorem cell23_3388472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 6].length) (baseStart_3388472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388472 prefixEnd_3388472 := by exact prefixLift 3388472
  have htrace : WordTrace (prefixWord ++ tailWord_3388472) baseStart_3388472 baseEnd_3388472 := by
    simpa [prefixWord, tailWord_3388472, baseEnd_3388472] using wordTrace_append hprefix tailTrace_3388472
  have hstable : (prefixWord ++ tailWord_3388472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388472).length < 2 ^ (prefixWord ++ tailWord_3388472).sum := by decide
  have hdescent : baseEnd_3388472 < baseStart_3388472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388485 : List Nat := [1, 3, 1, 1, 1, 3, 3, 4, 1, 5]
def baseStart_3388485 : Nat := 118140960795 + 3388485 * 2 ^ 59
def prefixEnd_3388485 : Nat := 4983230072969 + 3 ^ 40 * 3388485 * 2
def baseEnd_3388485 : Nat := 579973831850093423518049

theorem tailTrace_3388485 : CollatzResearch.WordTrace tailWord_3388485 prefixEnd_3388485 579973831850093423518049 := by
  unfold tailWord_3388485
  simp only [CollatzResearch.WordTrace]
  refine ⟨123588201129105027009878909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82392134086070018006585939 123588201129105027009878909)
  ·
    refine ⟨46345575423414385128704591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123588201129105027009878909 46345575423414385128704591)
    ·
      refine ⟨69518363135121577693056887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46345575423414385128704591 69518363135121577693056887)
      ·
        refine ⟨104277544702682366539585331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69518363135121577693056887 104277544702682366539585331)
        ·
          refine ⟨156416317054023549809377997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104277544702682366539585331 156416317054023549809377997)
          ·
            refine ⟨58656118895258831178516749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156416317054023549809377997 58656118895258831178516749)
            ·
              refine ⟨21996044585722061691943781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58656118895258831178516749 21996044585722061691943781)
              ·
                refine ⟨4124258359822886567239459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21996044585722061691943781 4124258359822886567239459)
                ·
                  refine ⟨6186387539734329850859189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124258359822886567239459 6186387539734329850859189)
                  ·
                    refine ⟨579973831850093423518049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6186387539734329850859189 579973831850093423518049)
                    ·
                      rfl

theorem cell23_3388485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_3388485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388485 prefixEnd_3388485 := by exact prefixLift 3388485
  have htrace : WordTrace (prefixWord ++ tailWord_3388485) baseStart_3388485 baseEnd_3388485 := by
    simpa [prefixWord, tailWord_3388485, baseEnd_3388485] using wordTrace_append hprefix tailTrace_3388485
  have hstable : (prefixWord ++ tailWord_3388485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388485).length < 2 ^ (prefixWord ++ tailWord_3388485).sum := by decide
  have hdescent : baseEnd_3388485 < baseStart_3388485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388492 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3388492 : Nat := 118140960795 + 3388492 * 2 ^ 59
def prefixEnd_3388492 : Nat := 4983230072969 + 3 ^ 40 * 3388492 * 2
def baseEnd_3388492 : Nat := 1739925089914861743166615

theorem tailTrace_3388492 : CollatzResearch.WordTrace tailWord_3388492 prefixEnd_3388492 1739925089914861743166615 := by
  unfold tailWord_3388492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61794228220039833602691865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82392304293386444803589153 61794228220039833602691865)
  ·
    refine ⟨46345671165029875202018899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61794228220039833602691865 46345671165029875202018899)
    ·
      refine ⟨69518506747544812803028349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46345671165029875202018899 69518506747544812803028349)
      ·
        refine ⟨26069440030329304801135631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69518506747544812803028349 26069440030329304801135631)
        ·
          refine ⟨39104160045493957201703447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26069440030329304801135631 39104160045493957201703447)
          ·
            refine ⟨58656240068240935802555171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39104160045493957201703447 58656240068240935802555171)
            ·
              refine ⟨87984360102361403703832757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58656240068240935802555171 87984360102361403703832757)
              ·
                refine ⟨8248533759596381597234321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87984360102361403703832757 8248533759596381597234321)
                ·
                  refine ⟨6186400319697286197925741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8248533759596381597234321 6186400319697286197925741)
                  ·
                    refine ⟨2319900119886482324222153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6186400319697286197925741 2319900119886482324222153)
                    ·
                      refine ⟨1739925089914861743166615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319900119886482324222153 1739925089914861743166615)
                      ·
                        rfl

theorem cell23_3388492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3388492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388492 prefixEnd_3388492 := by exact prefixLift 3388492
  have htrace : WordTrace (prefixWord ++ tailWord_3388492) baseStart_3388492 baseEnd_3388492 := by
    simpa [prefixWord, tailWord_3388492, baseEnd_3388492] using wordTrace_append hprefix tailTrace_3388492
  have hstable : (prefixWord ++ tailWord_3388492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388492).length < 2 ^ (prefixWord ++ tailWord_3388492).sum := by decide
  have hdescent : baseEnd_3388492 < baseStart_3388492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388510 : List Nat := [4, 4, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_3388510 : Nat := 118140960795 + 3388510 * 2 ^ 59
def prefixEnd_3388510 : Nat := 4983230072969 + 3 ^ 40 * 3388510 * 2
def baseEnd_3388510 : Nat := 579978110855547557580511

theorem tailTrace_3388510 : CollatzResearch.WordTrace tailWord_3388510 prefixEnd_3388510 579978110855547557580511 := by
  unfold tailWord_3388510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15448639119251807034942373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82392741969342970853025989 15448639119251807034942373)
  ·
    refine ⟨2896619834859713819051695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15448639119251807034942373 2896619834859713819051695)
    ·
      refine ⟨4344929752289570728577543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2896619834859713819051695 4344929752289570728577543)
      ·
        refine ⟨6517394628434356092866315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4344929752289570728577543 6517394628434356092866315)
        ·
          refine ⟨9776091942651534139299473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6517394628434356092866315 9776091942651534139299473)
          ·
            refine ⟨7332068956988650604474605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9776091942651534139299473 7332068956988650604474605)
            ·
              refine ⟨2749525858870743976677977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7332068956988650604474605 2749525858870743976677977)
              ·
                refine ⟨2062144394153057982508483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749525858870743976677977 2062144394153057982508483)
                ·
                  refine ⟨3093216591229586973762725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062144394153057982508483 3093216591229586973762725)
                  ·
                    refine ⟨579978110855547557580511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093216591229586973762725 579978110855547557580511)
                    ·
                      rfl

theorem cell23_3388510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_3388510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388510 prefixEnd_3388510 := by exact prefixLift 3388510
  have htrace : WordTrace (prefixWord ++ tailWord_3388510) baseStart_3388510 baseEnd_3388510 := by
    simpa [prefixWord, tailWord_3388510, baseEnd_3388510] using wordTrace_append hprefix tailTrace_3388510
  have hstable : (prefixWord ++ tailWord_3388510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388510).length < 2 ^ (prefixWord ++ tailWord_3388510).sum := by decide
  have hdescent : baseEnd_3388510 < baseStart_3388510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388535 : List Nat := [1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_3388535 : Nat := 118140960795 + 3388535 * 2 ^ 59
def prefixEnd_3388535 : Nat := 4983230072969 + 3 ^ 40 * 3388535 * 2
def baseEnd_3388535 : Nat := 1739947169583005074928917

theorem tailTrace_3388535 : CollatzResearch.WordTrace tailWord_3388535 prefixEnd_3388535 1739947169583005074928917 := by
  unfold tailWord_3388535
  simp only [CollatzResearch.WordTrace]
  refine ⟨123590024778923885549199059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82393349852615923699466039 123590024778923885549199059)
  ·
    refine ⟨185385037168385828323798589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123590024778923885549199059 185385037168385828323798589)
    ·
      refine ⟨69519388938144685621424471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185385037168385828323798589 69519388938144685621424471)
      ·
        refine ⟨104279083407217028432136707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69519388938144685621424471 104279083407217028432136707)
        ·
          refine ⟨156418625110825542648205061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104279083407217028432136707 156418625110825542648205061)
          ·
            refine ⟨29328492208279789246538449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156418625110825542648205061 29328492208279789246538449)
            ·
              refine ⟨21996369156209841934903837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29328492208279789246538449 21996369156209841934903837)
              ·
                refine ⟨8248638433578690725588939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21996369156209841934903837 8248638433578690725588939)
                ·
                  refine ⟨12372957650368036088383409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8248638433578690725588939 12372957650368036088383409)
                  ·
                    refine ⟨9279718237776027066287557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12372957650368036088383409 9279718237776027066287557)
                    ·
                      refine ⟨1739947169583005074928917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9279718237776027066287557 1739947169583005074928917)
                      ·
                        rfl

theorem cell23_3388535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_3388535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388535 prefixEnd_3388535 := by exact prefixLift 3388535
  have htrace : WordTrace (prefixWord ++ tailWord_3388535) baseStart_3388535 baseEnd_3388535 := by
    simpa [prefixWord, tailWord_3388535, baseEnd_3388535] using wordTrace_append hprefix tailTrace_3388535
  have hstable : (prefixWord ++ tailWord_3388535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388535).length < 2 ^ (prefixWord ++ tailWord_3388535).sum := by decide
  have hdescent : baseEnd_3388535 < baseStart_3388535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388545 : List Nat := [1, 2, 4, 2, 2, 1, 2, 9]
def baseStart_3388545 : Nat := 118140960795 + 3388545 * 2 ^ 59
def prefixEnd_3388545 : Nat := 4983230072969 + 3 ^ 40 * 3388545 * 2
def baseEnd_3388545 : Nat := 64442677940353705029773

theorem tailTrace_3388545 : CollatzResearch.WordTrace tailWord_3388545 prefixEnd_3388545 64442677940353705029773 := by
  unfold tailWord_3388545
  simp only [CollatzResearch.WordTrace]
  refine ⟨123590389508887657257063089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82393593005925104838042059 123590389508887657257063089)
  ·
    refine ⟨92692792131665742942797317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123590389508887657257063089 92692792131665742942797317)
    ·
      refine ⟨17379898524687326801774497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92692792131665742942797317 17379898524687326801774497)
      ·
        refine ⟨13034923893515495101330873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17379898524687326801774497 13034923893515495101330873)
        ·
          refine ⟨9776192920136621325998155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13034923893515495101330873 9776192920136621325998155)
          ·
            refine ⟨14664289380204931988997233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776192920136621325998155 14664289380204931988997233)
            ·
              refine ⟨10998217035153698991747925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14664289380204931988997233 10998217035153698991747925)
              ·
                refine ⟨64442677940353705029773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10998217035153698991747925 64442677940353705029773)
                ·
                  rfl

theorem cell23_3388545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 9].length) (baseStart_3388545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388545 prefixEnd_3388545 := by exact prefixLift 3388545
  have htrace : WordTrace (prefixWord ++ tailWord_3388545) baseStart_3388545 baseEnd_3388545 := by
    simpa [prefixWord, tailWord_3388545, baseEnd_3388545] using wordTrace_append hprefix tailTrace_3388545
  have hstable : (prefixWord ++ tailWord_3388545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388545).length < 2 ^ (prefixWord ++ tailWord_3388545).sum := by decide
  have hdescent : baseEnd_3388545 < baseStart_3388545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388599 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_3388599 : Nat := 118140960795 + 3388599 * 2 ^ 59
def prefixEnd_3388599 : Nat := 4983230072969 + 3 ^ 40 * 3388599 * 2
def baseEnd_3388599 : Nat := 1739980032344892824528623

theorem tailTrace_3388599 : CollatzResearch.WordTrace tailWord_3388599 prefixEnd_3388599 1739980032344892824528623 := by
  unfold tailWord_3388599
  simp only [CollatzResearch.WordTrace]
  refine ⟨123592359050692024479528851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82394906033794682986352567 123592359050692024479528851)
  ·
    refine ⟨185388538576038036719293277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123592359050692024479528851 185388538576038036719293277)
    ·
      refine ⟨69520701966014263769734979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185388538576038036719293277 69520701966014263769734979)
      ·
        refine ⟨104281052949021395654602469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69520701966014263769734979 104281052949021395654602469)
        ·
          refine ⟨19552697427941511685237963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104281052949021395654602469 19552697427941511685237963)
          ·
            refine ⟨29329046141912267527856945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19552697427941511685237963 29329046141912267527856945)
            ·
              refine ⟨21996784606434200645892709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29329046141912267527856945 21996784606434200645892709)
              ·
                refine ⟨4124397113706412621104883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21996784606434200645892709 4124397113706412621104883)
                ·
                  refine ⟨6186595670559618931657325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124397113706412621104883 6186595670559618931657325)
                  ·
                    refine ⟨2319973376459857099371497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6186595670559618931657325 2319973376459857099371497)
                    ·
                      refine ⟨1739980032344892824528623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319973376459857099371497 1739980032344892824528623)
                      ·
                        rfl

theorem cell23_3388599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_3388599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388599 prefixEnd_3388599 := by exact prefixLift 3388599
  have htrace : WordTrace (prefixWord ++ tailWord_3388599) baseStart_3388599 baseEnd_3388599 := by
    simpa [prefixWord, tailWord_3388599, baseEnd_3388599] using wordTrace_append hprefix tailTrace_3388599
  have hstable : (prefixWord ++ tailWord_3388599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388599).length < 2 ^ (prefixWord ++ tailWord_3388599).sum := by decide
  have hdescent : baseEnd_3388599 < baseStart_3388599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388615 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3388615 : Nat := 118140960795 + 3388615 * 2 ^ 59
def prefixEnd_3388615 : Nat := 4983230072969 + 3 ^ 40 * 3388615 * 2
def baseEnd_3388615 : Nat := 1739988248035364761928549

theorem tailTrace_3388615 : CollatzResearch.WordTrace tailWord_3388615 prefixEnd_3388615 1739988248035364761928549 := by
  unfold tailWord_3388615
  simp only [CollatzResearch.WordTrace]
  refine ⟨123592942618634059212111299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82395295079089372808074199 123592942618634059212111299)
  ·
    refine ⟨185389413927951088818166949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123592942618634059212111299 185389413927951088818166949)
    ·
      refine ⟨34760515111490829153406303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185389413927951088818166949 34760515111490829153406303)
      ·
        refine ⟨52140772667236243730109455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34760515111490829153406303 52140772667236243730109455)
        ·
          refine ⟨78211159000854365595164183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52140772667236243730109455 78211159000854365595164183)
          ·
            refine ⟨117316738501281548392746275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78211159000854365595164183 117316738501281548392746275)
            ·
              refine ⟨175975107751922322589119413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117316738501281548392746275 175975107751922322589119413)
              ·
                refine ⟨16497666351742717742729945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175975107751922322589119413 16497666351742717742729945)
                ·
                  refine ⟨12373249763807038307047459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16497666351742717742729945 12373249763807038307047459)
                  ·
                    refine ⟨18559874645710557460571189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12373249763807038307047459 18559874645710557460571189)
                    ·
                      refine ⟨1739988248035364761928549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18559874645710557460571189 1739988248035364761928549)
                      ·
                        rfl

theorem cell23_3388615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3388615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388615 prefixEnd_3388615 := by exact prefixLift 3388615
  have htrace : WordTrace (prefixWord ++ tailWord_3388615) baseStart_3388615 baseEnd_3388615 := by
    simpa [prefixWord, tailWord_3388615, baseEnd_3388615] using wordTrace_append hprefix tailTrace_3388615
  have hstable : (prefixWord ++ tailWord_3388615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388615).length < 2 ^ (prefixWord ++ tailWord_3388615).sum := by decide
  have hdescent : baseEnd_3388615 < baseStart_3388615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388616 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_3388616 : Nat := 118140960795 + 3388616 * 2 ^ 59
def prefixEnd_3388616 : Nat := 4983230072969 + 3 ^ 40 * 3388616 * 2
def baseEnd_3388616 : Nat := 1739988761516019258016045

theorem tailTrace_3388616 : CollatzResearch.WordTrace tailWord_3388616 prefixEnd_3388616 1739988761516019258016045 := by
  unfold tailWord_3388616
  simp only [CollatzResearch.WordTrace]
  refine ⟨61796489545815218191448851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82395319394420290921931801 61796489545815218191448851)
  ·
    refine ⟨92694734318722827287173277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61796489545815218191448851 92694734318722827287173277)
    ·
      refine ⟨34760525369521060232689979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92694734318722827287173277 34760525369521060232689979)
      ·
        refine ⟨52140788054281590349034969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34760525369521060232689979 52140788054281590349034969)
        ·
          refine ⟨39105591040711192761776227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52140788054281590349034969 39105591040711192761776227)
          ·
            refine ⟨58658386561066789142664341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39105591040711192761776227 58658386561066789142664341)
            ·
              refine ⟨2749611870050005741062391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58658386561066789142664341 2749611870050005741062391)
              ·
                refine ⟨4124417805075008611593587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2749611870050005741062391 4124417805075008611593587)
                ·
                  refine ⟨6186626707612512917390381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124417805075008611593587 6186626707612512917390381)
                  ·
                    refine ⟨2319985015354692344021393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6186626707612512917390381 2319985015354692344021393)
                    ·
                      refine ⟨1739988761516019258016045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2319985015354692344021393 1739988761516019258016045)
                      ·
                        rfl

theorem cell23_3388616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_3388616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388616 prefixEnd_3388616 := by exact prefixLift 3388616
  have htrace : WordTrace (prefixWord ++ tailWord_3388616) baseStart_3388616 baseEnd_3388616 := by
    simpa [prefixWord, tailWord_3388616, baseEnd_3388616] using wordTrace_append hprefix tailTrace_3388616
  have hstable : (prefixWord ++ tailWord_3388616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388616).length < 2 ^ (prefixWord ++ tailWord_3388616).sum := by decide
  have hdescent : baseEnd_3388616 < baseStart_3388616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388665 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 1, 7]
def baseStart_3388665 : Nat := 118140960795 + 3388665 * 2 ^ 59
def prefixEnd_3388665 : Nat := 4983230072969 + 3 ^ 40 * 3388665 * 2
def baseEnd_3388665 : Nat := 580004640689363188767773

theorem tailTrace_3388665 : CollatzResearch.WordTrace tailWord_3388665 prefixEnd_3388665 580004640689363188767773 := by
  unfold tailWord_3388665
  simp only [CollatzResearch.WordTrace]
  refine ⟨123594766268452917751431449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82396510845635278500954299 123594766268452917751431449)
  ·
    refine ⟨92696074701339688313573587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123594766268452917751431449 92696074701339688313573587)
    ·
      refine ⟨139044112052009532470360381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92696074701339688313573587 139044112052009532470360381)
      ·
        refine ⟨52141542019503574676385143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139044112052009532470360381 52141542019503574676385143)
        ·
          refine ⟨78212313029255362014577715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52141542019503574676385143 78212313029255362014577715)
          ·
            refine ⟨117318469543883043021866573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78212313029255362014577715 117318469543883043021866573)
            ·
              refine ⟨43994426078956141133199965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117318469543883043021866573 43994426078956141133199965)
              ·
                refine ⟨16497909779608552924949987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43994426078956141133199965 16497909779608552924949987)
                ·
                  refine ⟨24746864669412829387424981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16497909779608552924949987 24746864669412829387424981)
                  ·
                    refine ⟨580004640689363188767773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24746864669412829387424981 580004640689363188767773)
                    ·
                      rfl

theorem cell23_3388665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 1, 7].length) (baseStart_3388665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388665 prefixEnd_3388665 := by exact prefixLift 3388665
  have htrace : WordTrace (prefixWord ++ tailWord_3388665) baseStart_3388665 baseEnd_3388665 := by
    simpa [prefixWord, tailWord_3388665, baseEnd_3388665] using wordTrace_append hprefix tailTrace_3388665
  have hstable : (prefixWord ++ tailWord_3388665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388665).length < 2 ^ (prefixWord ++ tailWord_3388665).sum := by decide
  have hdescent : baseEnd_3388665 < baseStart_3388665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388672 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2]
def baseStart_3388672 : Nat := 118140960795 + 3388672 * 2 ^ 59
def prefixEnd_3388672 : Nat := 4983230072969 + 3 ^ 40 * 3388672 * 2
def baseEnd_3388672 : Nat := 1740017516432671038915787

theorem tailTrace_3388672 : CollatzResearch.WordTrace tailWord_3388672 prefixEnd_3388672 1740017516432671038915787 := by
  unfold tailWord_3388672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61797510789713778973468135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82396681052951705297957513 61797510789713778973468135)
  ·
    refine ⟨92696266184570668460202203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61797510789713778973468135 92696266184570668460202203)
    ·
      refine ⟨139044399276856002690303305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92696266184570668460202203 139044399276856002690303305)
      ·
        refine ⟨104283299457642002017727479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139044399276856002690303305 104283299457642002017727479)
        ·
          refine ⟨156424949186463003026591219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104283299457642002017727479 156424949186463003026591219)
          ·
            refine ⟨234637423779694504539886829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156424949186463003026591219 234637423779694504539886829)
            ·
              refine ⟨87989033917385439202457561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234637423779694504539886829 87989033917385439202457561)
              ·
                refine ⟨65991775438039079401843171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87989033917385439202457561 65991775438039079401843171)
                ·
                  refine ⟨98987663157058619102764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65991775438039079401843171 98987663157058619102764757)
                  ·
                    refine ⟨2320023355243561385221049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 98987663157058619102764757 2320023355243561385221049)
                    ·
                      refine ⟨1740017516432671038915787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320023355243561385221049 1740017516432671038915787)
                      ·
                        rfl

theorem cell23_3388672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_3388672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388672 prefixEnd_3388672 := by exact prefixLift 3388672
  have htrace : WordTrace (prefixWord ++ tailWord_3388672) baseStart_3388672 baseEnd_3388672 := by
    simpa [prefixWord, tailWord_3388672, baseEnd_3388672] using wordTrace_append hprefix tailTrace_3388672
  have hstable : (prefixWord ++ tailWord_3388672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388672).length < 2 ^ (prefixWord ++ tailWord_3388672).sum := by decide
  have hdescent : baseEnd_3388672 < baseStart_3388672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388686 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 5]
def baseStart_3388686 : Nat := 118140960795 + 3388686 * 2 ^ 59
def prefixEnd_3388686 : Nat := 4983230072969 + 3 ^ 40 * 3388686 * 2
def baseEnd_3388686 : Nat := 193336078351314887126747

theorem tailTrace_3388686 : CollatzResearch.WordTrace tailWord_3388686 prefixEnd_3388686 193336078351314887126747 := by
  unfold tailWord_3388686
  simp only [CollatzResearch.WordTrace]
  refine ⟨15449441525172104792243239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82397021467584558891963941 15449441525172104792243239)
  ·
    refine ⟨23174162287758157188364859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15449441525172104792243239 23174162287758157188364859)
    ·
      refine ⟨34761243431637235782547289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23174162287758157188364859 34761243431637235782547289)
      ·
        refine ⟨26070932573727926836910467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34761243431637235782547289 26070932573727926836910467)
        ·
          refine ⟨39106398860591890255365701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26070932573727926836910467 39106398860591890255365701)
          ·
            refine ⟨7332449786360979422881069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39106398860591890255365701 7332449786360979422881069)
            ·
              refine ⟨2749668669885367283580401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7332449786360979422881069 2749668669885367283580401)
              ·
                refine ⟨2062251502414025462685301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749668669885367283580401 2062251502414025462685301)
                ·
                  refine ⟨193336078351314887126747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2062251502414025462685301 193336078351314887126747)
                  ·
                    rfl

theorem cell23_3388686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_3388686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388686 prefixEnd_3388686 := by exact prefixLift 3388686
  have htrace : WordTrace (prefixWord ++ tailWord_3388686) baseStart_3388686 baseEnd_3388686 := by
    simpa [prefixWord, tailWord_3388686, baseEnd_3388686] using wordTrace_append hprefix tailTrace_3388686
  have hstable : (prefixWord ++ tailWord_3388686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388686).length < 2 ^ (prefixWord ++ tailWord_3388686).sum := by decide
  have hdescent : baseEnd_3388686 < baseStart_3388686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388715 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6]
def baseStart_3388715 : Nat := 118140960795 + 3388715 * 2 ^ 59
def prefixEnd_3388715 : Nat := 4983230072969 + 3 ^ 40 * 3388715 * 2
def baseEnd_3388715 : Nat := 1740039596100814370678089

theorem tailTrace_3388715 : CollatzResearch.WordTrace tailWord_3388715 prefixEnd_3388715 1740039596100814370678089 := by
  unfold tailWord_3388715
  simp only [CollatzResearch.WordTrace]
  refine ⟨123596589918271776290751599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82397726612181184193834399 123596589918271776290751599)
  ·
    refine ⟨185394884877407664436127399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123596589918271776290751599 185394884877407664436127399)
    ·
      refine ⟨278092327316111496654191099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185394884877407664436127399 278092327316111496654191099)
      ·
        refine ⟨417138490974167244981286649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278092327316111496654191099 417138490974167244981286649)
        ·
          refine ⟨312853868230625433735964987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417138490974167244981286649 312853868230625433735964987)
          ·
            refine ⟨469280802345938150603947481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312853868230625433735964987 469280802345938150603947481)
            ·
              refine ⟨351960601759453612952960611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469280802345938150603947481 351960601759453612952960611)
              ·
                refine ⟨527940902639180419429440917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 351960601759453612952960611 527940902639180419429440917)
                ·
                  refine ⟨24747229811211582160755043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 527940902639180419429440917 24747229811211582160755043)
                  ·
                    refine ⟨37120844716817373241132565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24747229811211582160755043 37120844716817373241132565)
                    ·
                      refine ⟨1740039596100814370678089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37120844716817373241132565 1740039596100814370678089)
                      ·
                        rfl

theorem cell23_3388715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 6].length) (baseStart_3388715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388715 prefixEnd_3388715 := by exact prefixLift 3388715
  have htrace : WordTrace (prefixWord ++ tailWord_3388715) baseStart_3388715 baseEnd_3388715 := by
    simpa [prefixWord, tailWord_3388715, baseEnd_3388715] using wordTrace_append hprefix tailTrace_3388715
  have hstable : (prefixWord ++ tailWord_3388715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388715).length < 2 ^ (prefixWord ++ tailWord_3388715).sum := by decide
  have hdescent : baseEnd_3388715 < baseStart_3388715 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388803 : List Nat := [1, 1, 1, 3, 5, 1, 2, 4, 1, 1, 3]
def baseStart_3388803 : Nat := 118140960795 + 3388803 * 2 ^ 59
def prefixEnd_3388803 : Nat := 4983230072969 + 3 ^ 40 * 3388803 * 2
def baseEnd_3388803 : Nat := 1740084782398410026377685

theorem tailTrace_3388803 : CollatzResearch.WordTrace tailWord_3388803 prefixEnd_3388803 1740084782398410026377685 := by
  unfold tailWord_3388803
  simp only [CollatzResearch.WordTrace]
  refine ⟨123599799541952967319955063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82399866361301978213303375 123599799541952967319955063)
  ·
    refine ⟨185399699312929450979932595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123599799541952967319955063 185399699312929450979932595)
    ·
      refine ⟨278099548969394176469898893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185399699312929450979932595 278099548969394176469898893)
      ·
        refine ⟨104287330863522816176212085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278099548969394176469898893 104287330863522816176212085)
        ·
          refine ⟨9776937268455264016519883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104287330863522816176212085 9776937268455264016519883)
          ·
            refine ⟨14665405902682896024779825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9776937268455264016519883 14665405902682896024779825)
            ·
              refine ⟨10999054427012172018584869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14665405902682896024779825 10999054427012172018584869)
              ·
                refine ⟨2062322705064782253484663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10999054427012172018584869 2062322705064782253484663)
                ·
                  refine ⟨3093484057597173380226995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062322705064782253484663 3093484057597173380226995)
                  ·
                    refine ⟨4640226086395760070340493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3093484057597173380226995 4640226086395760070340493)
                    ·
                      refine ⟨1740084782398410026377685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4640226086395760070340493 1740084782398410026377685)
                      ·
                        rfl

theorem cell23_3388803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_3388803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388803 prefixEnd_3388803 := by exact prefixLift 3388803
  have htrace : WordTrace (prefixWord ++ tailWord_3388803) baseStart_3388803 baseEnd_3388803 := by
    simpa [prefixWord, tailWord_3388803, baseEnd_3388803] using wordTrace_append hprefix tailTrace_3388803
  have hstable : (prefixWord ++ tailWord_3388803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388803).length < 2 ^ (prefixWord ++ tailWord_3388803).sum := by decide
  have hdescent : baseEnd_3388803 < baseStart_3388803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388826 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4]
def baseStart_3388826 : Nat := 118140960795 + 3388826 * 2 ^ 59
def prefixEnd_3388826 : Nat := 4983230072969 + 3 ^ 40 * 3388826 * 2
def baseEnd_3388826 : Nat := 1740096592453463436390079

theorem tailTrace_3388826 : CollatzResearch.WordTrace tailWord_3388826 prefixEnd_3388826 1740096592453463436390079 := by
  unfold tailWord_3388826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30900159605217410562010583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82400425613913094832028221 30900159605217410562010583)
  ·
    refine ⟨46350239407826115843015875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30900159605217410562010583 46350239407826115843015875)
    ·
      refine ⟨69525359111739173764523813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46350239407826115843015875 69525359111739173764523813)
      ·
        refine ⟨13036004833451095080848215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69525359111739173764523813 13036004833451095080848215)
        ·
          refine ⟨19554007250176642621272323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036004833451095080848215 19554007250176642621272323)
          ·
            refine ⟨29331010875264963931908485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554007250176642621272323 29331010875264963931908485)
            ·
              refine ⟨5499564539112180737232841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29331010875264963931908485 5499564539112180737232841)
              ·
                refine ⟨4124673404334135552924631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5499564539112180737232841 4124673404334135552924631)
                ·
                  refine ⟨6187010106501203329386947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4124673404334135552924631 6187010106501203329386947)
                  ·
                    refine ⟨9280515159751804994080421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187010106501203329386947 9280515159751804994080421)
                    ·
                      refine ⟨1740096592453463436390079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9280515159751804994080421 1740096592453463436390079)
                      ·
                        rfl

theorem cell23_3388826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_3388826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388826 prefixEnd_3388826 := by exact prefixLift 3388826
  have htrace : WordTrace (prefixWord ++ tailWord_3388826) baseStart_3388826 baseEnd_3388826 := by
    simpa [prefixWord, tailWord_3388826, baseEnd_3388826] using wordTrace_append hprefix tailTrace_3388826
  have hstable : (prefixWord ++ tailWord_3388826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388826).length < 2 ^ (prefixWord ++ tailWord_3388826).sum := by decide
  have hdescent : baseEnd_3388826 < baseStart_3388826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388832 : List Nat := [2, 1, 1, 4, 1, 2, 3, 9]
def baseStart_3388832 : Nat := 118140960795 + 3388832 * 2 ^ 59
def prefixEnd_3388832 : Nat := 4983230072969 + 3 ^ 40 * 3388832 * 2
def baseEnd_3388832 : Nat := 64448136049532978256113

theorem tailTrace_3388832 : CollatzResearch.WordTrace tailWord_3388832 prefixEnd_3388832 64448136049532978256113 := by
  unfold tailWord_3388832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61800428629423952636380375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82400571505898603515173833 61800428629423952636380375)
  ·
    refine ⟨92700642944135928954570563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61800428629423952636380375 92700642944135928954570563)
    ·
      refine ⟨139050964416203893431855845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92700642944135928954570563 139050964416203893431855845)
      ·
        refine ⟨26072055828038230018472971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139050964416203893431855845 26072055828038230018472971)
        ·
          refine ⟨39108083742057345027709457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26072055828038230018472971 39108083742057345027709457)
          ·
            refine ⟨29331062806543008770782093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39108083742057345027709457 29331062806543008770782093)
            ·
              refine ⟨10999148552453628289043285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29331062806543008770782093 10999148552453628289043285)
              ·
                refine ⟨64448136049532978256113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10999148552453628289043285 64448136049532978256113)
                ·
                  rfl

theorem cell23_3388832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 9].length) (baseStart_3388832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388832 prefixEnd_3388832 := by exact prefixLift 3388832
  have htrace : WordTrace (prefixWord ++ tailWord_3388832) baseStart_3388832 baseEnd_3388832 := by
    simpa [prefixWord, tailWord_3388832, baseEnd_3388832] using wordTrace_append hprefix tailTrace_3388832
  have hstable : (prefixWord ++ tailWord_3388832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388832).length < 2 ^ (prefixWord ++ tailWord_3388832).sum := by decide
  have hdescent : baseEnd_3388832 < baseStart_3388832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3388839 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3388839 : Nat := 118140960795 + 3388839 * 2 ^ 59
def prefixEnd_3388839 : Nat := 4983230072969 + 3 ^ 40 * 3388839 * 2
def baseEnd_3388839 : Nat := 1740103267701971885527519

theorem tailTrace_3388839 : CollatzResearch.WordTrace tailWord_3388839 prefixEnd_3388839 1740103267701971885527519 := by
  unfold tailWord_3388839
  simp only [CollatzResearch.WordTrace]
  refine ⟨123601112569822545468265571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82400741713215030312177047 123601112569822545468265571)
  ·
    refine ⟨185401668854733818202398357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123601112569822545468265571 185401668854733818202398357)
    ·
      refine ⟨8690703227565647728237423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 185401668854733818202398357 8690703227565647728237423)
      ·
        refine ⟨13036054841348471592356135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8690703227565647728237423 13036054841348471592356135)
        ·
          refine ⟨19554082262022707388534203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13036054841348471592356135 19554082262022707388534203)
          ·
            refine ⟨29331123393034061082801305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19554082262022707388534203 29331123393034061082801305)
            ·
              refine ⟨21998342544775545812100979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29331123393034061082801305 21998342544775545812100979)
              ·
                refine ⟨32997513817163318718151469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21998342544775545812100979 32997513817163318718151469)
                ·
                  refine ⟨12374067681436244519306801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32997513817163318718151469 12374067681436244519306801)
                  ·
                    refine ⟨9280550761077183389480101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12374067681436244519306801 9280550761077183389480101)
                    ·
                      refine ⟨1740103267701971885527519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9280550761077183389480101 1740103267701971885527519)
                      ·
                        rfl

theorem cell23_3388839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3388839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3388839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3388839 prefixEnd_3388839 := by exact prefixLift 3388839
  have htrace : WordTrace (prefixWord ++ tailWord_3388839) baseStart_3388839 baseEnd_3388839 := by
    simpa [prefixWord, tailWord_3388839, baseEnd_3388839] using wordTrace_append hprefix tailTrace_3388839
  have hstable : (prefixWord ++ tailWord_3388839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3388839).length < 2 ^ (prefixWord ++ tailWord_3388839).sum := by decide
  have hdescent : baseEnd_3388839 < baseStart_3388839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3388839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389006 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3389006 : Nat := 118140960795 + 3389006 * 2 ^ 59
def prefixEnd_3389006 : Nat := 4983230072969 + 3 ^ 40 * 3389006 * 2
def baseEnd_3389006 : Nat := 1740189018971272732139251

theorem tailTrace_3389006 : CollatzResearch.WordTrace tailWord_3389006 prefixEnd_3389006 1740189018971272732139251 := by
  unfold tailWord_3389006
  simp only [CollatzResearch.WordTrace]
  refine ⟨15450900445027191623699359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82404802373478355326396581 15450900445027191623699359)
  ·
    refine ⟨23176350667540787435549039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15450900445027191623699359 23176350667540787435549039)
    ·
      refine ⟨34764526001311181153323559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23176350667540787435549039 34764526001311181153323559)
      ·
        refine ⟨52146789001966771729985339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34764526001311181153323559 52146789001966771729985339)
        ·
          refine ⟨78220183502950157594978009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52146789001966771729985339 78220183502950157594978009)
          ·
            refine ⟨58665137627212618196233507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78220183502950157594978009 58665137627212618196233507)
            ·
              refine ⟨87997706440818927294350261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58665137627212618196233507 87997706440818927294350261)
              ·
                refine ⟨8249784978826774433845337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87997706440818927294350261 8249784978826774433845337)
                ·
                  refine ⟨6187338734120080825384003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249784978826774433845337 6187338734120080825384003)
                  ·
                    refine ⟨9281008101180121238076005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187338734120080825384003 9281008101180121238076005)
                    ·
                      refine ⟨1740189018971272732139251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9281008101180121238076005 1740189018971272732139251)
                      ·
                        rfl

theorem cell23_3389006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3389006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389006 prefixEnd_3389006 := by exact prefixLift 3389006
  have htrace : WordTrace (prefixWord ++ tailWord_3389006) baseStart_3389006 baseEnd_3389006 := by
    simpa [prefixWord, tailWord_3389006, baseEnd_3389006] using wordTrace_append hprefix tailTrace_3389006
  have hstable : (prefixWord ++ tailWord_3389006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389006).length < 2 ^ (prefixWord ++ tailWord_3389006).sum := by decide
  have hdescent : baseEnd_3389006 < baseStart_3389006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389033 : List Nat := [1, 2, 1, 1, 1, 4, 2, 6, 1, 4]
def baseStart_3389033 : Nat := 118140960795 + 3389033 * 2 ^ 59
def prefixEnd_3389033 : Nat := 4983230072969 + 3 ^ 40 * 3389033 * 2
def baseEnd_3389033 : Nat := 580067627649648042167209

theorem tailTrace_3389033 : CollatzResearch.WordTrace tailWord_3389033 prefixEnd_3389033 580067627649648042167209 := by
  unfold tailWord_3389033
  simp only [CollatzResearch.WordTrace]
  refine ⟨123608188331119716600827753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82405458887413144400551835 123608188331119716600827753)
  ·
    refine ⟨92706141248339787450620815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123608188331119716600827753 92706141248339787450620815)
    ·
      refine ⟨139059211872509681175931223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92706141248339787450620815 139059211872509681175931223)
      ·
        refine ⟨208588817808764521763896835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139059211872509681175931223 208588817808764521763896835)
        ·
          refine ⟨312883226713146782645845253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208588817808764521763896835 312883226713146782645845253)
          ·
            refine ⟨58665605008715021746095985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312883226713146782645845253 58665605008715021746095985)
            ·
              refine ⟨43999203756536266309571989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58665605008715021746095985 43999203756536266309571989)
              ·
                refine ⟨2062462676087637483261187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43999203756536266309571989 2062462676087637483261187)
                ·
                  refine ⟨3093694014131456224891781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062462676087637483261187 3093694014131456224891781)
                  ·
                    refine ⟨580067627649648042167209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093694014131456224891781 580067627649648042167209)
                    ·
                      rfl

theorem cell23_3389033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 4].length) (baseStart_3389033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389033 prefixEnd_3389033 := by exact prefixLift 3389033
  have htrace : WordTrace (prefixWord ++ tailWord_3389033) baseStart_3389033 baseEnd_3389033 := by
    simpa [prefixWord, tailWord_3389033, baseEnd_3389033] using wordTrace_append hprefix tailTrace_3389033
  have hstable : (prefixWord ++ tailWord_3389033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389033).length < 2 ^ (prefixWord ++ tailWord_3389033).sum := by decide
  have hdescent : baseEnd_3389033 < baseStart_3389033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389060 : List Nat := [2, 3, 2, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_3389060 : Nat := 118140960795 + 3389060 * 2 ^ 59
def prefixEnd_3389060 : Nat := 4983230072969 + 3 ^ 40 * 3389060 * 2
def baseEnd_3389060 : Nat := 1740216746926615520864003

theorem tailTrace_3389060 : CollatzResearch.WordTrace tailWord_3389060 prefixEnd_3389060 1740216746926615520864003 := by
  unfold tailWord_3389060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61804586551010950106030317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82406115401347933474707089 61804586551010950106030317)
  ·
    refine ⟨23176719956629106289761369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61804586551010950106030317 23176719956629106289761369)
    ·
      refine ⟨17382539967471829717321027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23176719956629106289761369 17382539967471829717321027)
      ·
        refine ⟨26073809951207744575981541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17382539967471829717321027 26073809951207744575981541)
        ·
          refine ⟨4888839365851452107996539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26073809951207744575981541 4888839365851452107996539)
          ·
            refine ⟨7333259048777178161994809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888839365851452107996539 7333259048777178161994809)
            ·
              refine ⟨5499944286582883621496107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7333259048777178161994809 5499944286582883621496107)
              ·
                refine ⟨8249916429874325432244161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5499944286582883621496107 8249916429874325432244161)
                ·
                  refine ⟨6187437322405744074183121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8249916429874325432244161 6187437322405744074183121)
                  ·
                    refine ⟨4640577991804308055637341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6187437322405744074183121 4640577991804308055637341)
                    ·
                      refine ⟨1740216746926615520864003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4640577991804308055637341 1740216746926615520864003)
                      ·
                        rfl

theorem cell23_3389060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_3389060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389060 prefixEnd_3389060 := by exact prefixLift 3389060
  have htrace : WordTrace (prefixWord ++ tailWord_3389060) baseStart_3389060 baseEnd_3389060 := by
    simpa [prefixWord, tailWord_3389060, baseEnd_3389060] using wordTrace_append hprefix tailTrace_3389060
  have hstable : (prefixWord ++ tailWord_3389060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389060).length < 2 ^ (prefixWord ++ tailWord_3389060).sum := by decide
  have hdescent : baseEnd_3389060 < baseStart_3389060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389084 : List Nat := [2, 2, 3, 2, 3, 2, 2, 2, 1, 4]
def baseStart_3389084 : Nat := 118140960795 + 3389084 * 2 ^ 59
def prefixEnd_3389084 : Nat := 4983230072969 + 3 ^ 40 * 3389084 * 2
def baseEnd_3389084 : Nat := 580076356820774475654631

theorem tailTrace_3389084 : CollatzResearch.WordTrace tailWord_3389084 prefixEnd_3389084 580076356820774475654631 := by
  unfold tailWord_3389084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61805024226967476155467153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82406698969289968207289537 61805024226967476155467153)
  ·
    refine ⟨46353768170225607116600365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61805024226967476155467153 46353768170225607116600365)
    ·
      refine ⟨17382663063834602668725137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46353768170225607116600365 17382663063834602668725137)
      ·
        refine ⟨13036997297875952001543853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17382663063834602668725137 13036997297875952001543853)
        ·
          refine ⟨4888873986703482000578945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13036997297875952001543853 4888873986703482000578945)
          ·
            refine ⟨3666655490027611500434209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4888873986703482000578945 3666655490027611500434209)
            ·
              refine ⟨2749991617520708625325657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3666655490027611500434209 2749991617520708625325657)
              ·
                refine ⟨2062493713140531468994243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2749991617520708625325657 2062493713140531468994243)
                ·
                  refine ⟨3093740569710797203491365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062493713140531468994243 3093740569710797203491365)
                  ·
                    refine ⟨580076356820774475654631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093740569710797203491365 580076356820774475654631)
                    ·
                      rfl

theorem cell23_3389084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_3389084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389084 prefixEnd_3389084 := by exact prefixLift 3389084
  have htrace : WordTrace (prefixWord ++ tailWord_3389084) baseStart_3389084 baseEnd_3389084 := by
    simpa [prefixWord, tailWord_3389084, baseEnd_3389084] using wordTrace_append hprefix tailTrace_3389084
  have hstable : (prefixWord ++ tailWord_3389084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389084).length < 2 ^ (prefixWord ++ tailWord_3389084).sum := by decide
  have hdescent : baseEnd_3389084 < baseStart_3389084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389106 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3389106 : Nat := 118140960795 + 3389106 * 2 ^ 59
def prefixEnd_3389106 : Nat := 4983230072969 + 3 ^ 40 * 3389106 * 2
def baseEnd_3389106 : Nat := 580080122345574113629597

theorem tailTrace_3389106 : CollatzResearch.WordTrace tailWord_3389106 prefixEnd_3389106 580080122345574113629597 := by
  unfold tailWord_3389106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30902712714963812517058793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82407233906570166712156781 30902712714963812517058793)
  ·
    refine ⟨23177034536222859387794095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30902712714963812517058793 23177034536222859387794095)
    ·
      refine ⟨34765551804334289081691143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23177034536222859387794095 34765551804334289081691143)
      ·
        refine ⟨52148327706501433622536715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34765551804334289081691143 52148327706501433622536715)
        ·
          refine ⟨78222491559752150433805073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52148327706501433622536715 78222491559752150433805073)
          ·
            refine ⟨58666868669814112825353805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78222491559752150433805073 58666868669814112825353805)
            ·
              refine ⟨22000075751180292309507677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58666868669814112825353805 22000075751180292309507677)
              ·
                refine ⟨8250028406692609616065379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22000075751180292309507677 8250028406692609616065379)
                ·
                  refine ⟨12375042610038914424098069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250028406692609616065379 12375042610038914424098069)
                  ·
                    refine ⟨580080122345574113629597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12375042610038914424098069 580080122345574113629597)
                    ·
                      rfl

theorem cell23_3389106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3389106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389106 prefixEnd_3389106 := by exact prefixLift 3389106
  have htrace : WordTrace (prefixWord ++ tailWord_3389106) baseStart_3389106 baseEnd_3389106 := by
    simpa [prefixWord, tailWord_3389106, baseEnd_3389106] using wordTrace_append hprefix tailTrace_3389106
  have hstable : (prefixWord ++ tailWord_3389106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389106).length < 2 ^ (prefixWord ++ tailWord_3389106).sum := by decide
  have hdescent : baseEnd_3389106 < baseStart_3389106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389110 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3389110 : Nat := 118140960795 + 3389110 * 2 ^ 59
def prefixEnd_3389110 : Nat := 4983230072969 + 3 ^ 40 * 3389110 * 2
def baseEnd_3389110 : Nat := 580080806986446775079591

theorem tailTrace_3389110 : CollatzResearch.WordTrace tailWord_3389110 prefixEnd_3389110 580080806986446775079591 := by
  unfold tailWord_3389110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7725687296990047421961299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82407331167893839167587189 7725687296990047421961299)
  ·
    refine ⟨11588530945485071132941949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7725687296990047421961299 11588530945485071132941949)
    ·
      refine ⟨4345699104556901674853231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11588530945485071132941949 4345699104556901674853231)
      ·
        refine ⟨6518548656835352512279847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4345699104556901674853231 6518548656835352512279847)
        ·
          refine ⟨9777822985253028768419771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518548656835352512279847 9777822985253028768419771)
          ·
            refine ⟨14666734477879543152629657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9777822985253028768419771 14666734477879543152629657)
            ·
              refine ⟨11000050858409657364472243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14666734477879543152629657 11000050858409657364472243)
              ·
                refine ⟨16500076287614486046708365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000050858409657364472243 16500076287614486046708365)
                ·
                  refine ⟨6187528607855432267515637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16500076287614486046708365 6187528607855432267515637)
                  ·
                    refine ⟨580080806986446775079591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6187528607855432267515637 580080806986446775079591)
                    ·
                      rfl

theorem cell23_3389110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3389110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389110 prefixEnd_3389110 := by exact prefixLift 3389110
  have htrace : WordTrace (prefixWord ++ tailWord_3389110) baseStart_3389110 baseEnd_3389110 := by
    simpa [prefixWord, tailWord_3389110, baseEnd_3389110] using wordTrace_append hprefix tailTrace_3389110
  have hstable : (prefixWord ++ tailWord_3389110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389110).length < 2 ^ (prefixWord ++ tailWord_3389110).sum := by decide
  have hdescent : baseEnd_3389110 < baseStart_3389110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389130 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_3389130 : Nat := 118140960795 + 3389130 * 2 ^ 59
def prefixEnd_3389130 : Nat := 4983230072969 + 3 ^ 40 * 3389130 * 2
def baseEnd_3389130 : Nat := 1740252690572430246988681

theorem tailTrace_3389130 : CollatzResearch.WordTrace tailWord_3389130 prefixEnd_3389130 1740252690572430246988681 := by
  unfold tailWord_3389130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30902931552942075541777211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82407817474512201444739229 30902931552942075541777211)
  ·
    refine ⟨46354397329413113312665817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30902931552942075541777211 46354397329413113312665817)
    ·
      refine ⟨34765797997059834984499363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46354397329413113312665817 34765797997059834984499363)
      ·
        refine ⟨52148696995589752476749045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34765797997059834984499363 52148696995589752476749045)
        ·
          refine ⟨4888940343336539294695223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52148696995589752476749045 4888940343336539294695223)
          ·
            refine ⟨7333410515004808942042835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4888940343336539294695223 7333410515004808942042835)
            ·
              refine ⟨11000115772507213413064253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333410515004808942042835 11000115772507213413064253)
              ·
                refine ⟨4125043414690205029899095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11000115772507213413064253 4125043414690205029899095)
                ·
                  refine ⟨6187565122035307544848643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125043414690205029899095 6187565122035307544848643)
                  ·
                    refine ⟨9281347683052961317272965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6187565122035307544848643 9281347683052961317272965)
                    ·
                      refine ⟨1740252690572430246988681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9281347683052961317272965 1740252690572430246988681)
                      ·
                        rfl

theorem cell23_3389130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_3389130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389130 prefixEnd_3389130 := by exact prefixLift 3389130
  have htrace : WordTrace (prefixWord ++ tailWord_3389130) baseStart_3389130 baseEnd_3389130 := by
    simpa [prefixWord, tailWord_3389130, baseEnd_3389130] using wordTrace_append hprefix tailTrace_3389130
  have hstable : (prefixWord ++ tailWord_3389130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389130).length < 2 ^ (prefixWord ++ tailWord_3389130).sum := by decide
  have hdescent : baseEnd_3389130 < baseStart_3389130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389140 : List Nat := [2, 4, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3389140 : Nat := 118140960795 + 3389140 * 2 ^ 59
def prefixEnd_3389140 : Nat := 4983230072969 + 3 ^ 40 * 3389140 * 2
def baseEnd_3389140 : Nat := 580085941792991735954545

theorem tailTrace_3389140 : CollatzResearch.WordTrace tailWord_3389140 prefixEnd_3389140 580085941792991735954545 := by
  unfold tailWord_3389140
  simp only [CollatzResearch.WordTrace]
  refine ⟨61806045470866036937486437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82408060627821382583315249 61806045470866036937486437)
  ·
    refine ⟨11588633525787381925778707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61806045470866036937486437 11588633525787381925778707)
    ·
      refine ⟨17382950288681072888668061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11588633525787381925778707 17382950288681072888668061)
      ·
        refine ⟨6518606358255402333250523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17382950288681072888668061 6518606358255402333250523)
        ·
          refine ⟨9777909537383103499875785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6518606358255402333250523 9777909537383103499875785)
          ·
            refine ⟨7333432153037327624906839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9777909537383103499875785 7333432153037327624906839)
            ·
              refine ⟨11000148229555991437360259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333432153037327624906839 11000148229555991437360259)
              ·
                refine ⟨16500222344333987156040389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000148229555991437360259 16500222344333987156040389)
                ·
                  refine ⟨3093791689562622591757573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16500222344333987156040389 3093791689562622591757573)
                  ·
                    refine ⟨580085941792991735954545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3093791689562622591757573 580085941792991735954545)
                    ·
                      rfl

theorem cell23_3389140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3389140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389140 prefixEnd_3389140 := by exact prefixLift 3389140
  have htrace : WordTrace (prefixWord ++ tailWord_3389140) baseStart_3389140 baseEnd_3389140 := by
    simpa [prefixWord, tailWord_3389140, baseEnd_3389140] using wordTrace_append hprefix tailTrace_3389140
  have hstable : (prefixWord ++ tailWord_3389140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389140).length < 2 ^ (prefixWord ++ tailWord_3389140).sum := by decide
  have hdescent : baseEnd_3389140 < baseStart_3389140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389160 : List Nat := [2, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_3389160 : Nat := 118140960795 + 3389160 * 2 ^ 59
def prefixEnd_3389160 : Nat := 4983230072969 + 3 ^ 40 * 3389160 * 2
def baseEnd_3389160 : Nat := 1740268094992065129613543

theorem tailTrace_3389160 : CollatzResearch.WordTrace tailWord_3389160 prefixEnd_3389160 1740268094992065129613543 := by
  unfold tailWord_3389160
  simp only [CollatzResearch.WordTrace]
  refine ⟨61806410200829808645350467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82408546934439744860467289 61806410200829808645350467)
  ·
    refine ⟨92709615301244712968025701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61806410200829808645350467 92709615301244712968025701)
    ·
      refine ⟨17383052868983383681504819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92709615301244712968025701 17383052868983383681504819)
      ·
        refine ⟨26074579303475075522257229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383052868983383681504819 26074579303475075522257229)
        ·
          refine ⟨9777967238803153320846461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26074579303475075522257229 9777967238803153320846461)
          ·
            refine ⟨3666737714551182495317423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9777967238803153320846461 3666737714551182495317423)
            ·
              refine ⟨5500106571826773742976135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666737714551182495317423 5500106571826773742976135)
              ·
                refine ⟨8250159857740160614464203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500106571826773742976135 8250159857740160614464203)
                ·
                  refine ⟨12375239786610240921696305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250159857740160614464203 12375239786610240921696305)
                  ·
                    refine ⟨9281429839957680691272229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12375239786610240921696305 9281429839957680691272229)
                    ·
                      refine ⟨1740268094992065129613543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9281429839957680691272229 1740268094992065129613543)
                      ·
                        rfl

theorem cell23_3389160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_3389160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389160 prefixEnd_3389160 := by exact prefixLift 3389160
  have htrace : WordTrace (prefixWord ++ tailWord_3389160) baseStart_3389160 baseEnd_3389160 := by
    simpa [prefixWord, tailWord_3389160, baseEnd_3389160] using wordTrace_append hprefix tailTrace_3389160
  have hstable : (prefixWord ++ tailWord_3389160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389160).length < 2 ^ (prefixWord ++ tailWord_3389160).sum := by decide
  have hdescent : baseEnd_3389160 < baseStart_3389160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389163 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3]
def baseStart_3389163 : Nat := 118140960795 + 3389163 * 2 ^ 59
def prefixEnd_3389163 : Nat := 4983230072969 + 3 ^ 40 * 3389163 * 2
def baseEnd_3389163 : Nat := 1740269635434028617876029

theorem tailTrace_3389163 : CollatzResearch.WordTrace tailWord_3389163 prefixEnd_3389163 1740269635434028617876029 := by
  unfold tailWord_3389163
  simp only [CollatzResearch.WordTrace]
  refine ⟨123612929820648748803060143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82408619880432499202040095 123612929820648748803060143)
  ·
    refine ⟨185419394730973123204590215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123612929820648748803060143 185419394730973123204590215)
    ·
      refine ⟨278129092096459684806885323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185419394730973123204590215 278129092096459684806885323)
      ·
        refine ⟨417193638144689527210327985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278129092096459684806885323 417193638144689527210327985)
        ·
          refine ⟨312895228608517145407745989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417193638144689527210327985 312895228608517145407745989)
          ·
            refine ⟨58667855364096964763952373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 312895228608517145407745989 58667855364096964763952373)
            ·
              refine ⟨5500111440384090446620535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58667855364096964763952373 5500111440384090446620535)
              ·
                refine ⟨8250167160576135669930803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500111440384090446620535 8250167160576135669930803)
                ·
                  refine ⟨12375250740864203504896205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250167160576135669930803 12375250740864203504896205)
                  ·
                    refine ⟨4640719027824076314336077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375250740864203504896205 4640719027824076314336077)
                    ·
                      refine ⟨1740269635434028617876029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4640719027824076314336077 1740269635434028617876029)
                      ·
                        rfl

theorem cell23_3389163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 1, 3, 3].length) (baseStart_3389163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389163 prefixEnd_3389163 := by exact prefixLift 3389163
  have htrace : WordTrace (prefixWord ++ tailWord_3389163) baseStart_3389163 baseEnd_3389163 := by
    simpa [prefixWord, tailWord_3389163, baseEnd_3389163] using wordTrace_append hprefix tailTrace_3389163
  have hstable : (prefixWord ++ tailWord_3389163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389163).length < 2 ^ (prefixWord ++ tailWord_3389163).sum := by decide
  have hdescent : baseEnd_3389163 < baseStart_3389163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389196 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 4, 6]
def baseStart_3389196 : Nat := 118140960795 + 3389196 * 2 ^ 59
def prefixEnd_3389196 : Nat := 4983230072969 + 3 ^ 40 * 3389196 * 2
def baseEnd_3389196 : Nat := 580095526765208996254459

theorem tailTrace_3389196 : CollatzResearch.WordTrace tailWord_3389196 prefixEnd_3389196 580095526765208996254459 := by
  unfold tailWord_3389196
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807066714764597719505721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82409422286352796959340961 61807066714764597719505721)
  ·
    refine ⟨46355300036073448289629291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61807066714764597719505721 46355300036073448289629291)
    ·
      refine ⟨69532950054110172434443937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46355300036073448289629291 69532950054110172434443937)
      ·
        refine ⟨52149712540582629325832953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69532950054110172434443937 52149712540582629325832953)
        ·
          refine ⟨39112284405436971994374715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52149712540582629325832953 39112284405436971994374715)
          ·
            refine ⟨58668426608155457991562073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39112284405436971994374715 58668426608155457991562073)
            ·
              refine ⟨44001319956116593493671555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58668426608155457991562073 44001319956116593493671555)
              ·
                refine ⟨66001979934174890240507333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44001319956116593493671555 66001979934174890240507333)
                ·
                  refine ⟨12375371237657791920095125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66001979934174890240507333 12375371237657791920095125)
                  ·
                    refine ⟨580095526765208996254459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12375371237657791920095125 580095526765208996254459)
                    ·
                      rfl

theorem cell23_3389196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_3389196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389196 prefixEnd_3389196 := by exact prefixLift 3389196
  have htrace : WordTrace (prefixWord ++ tailWord_3389196) baseStart_3389196 baseEnd_3389196 := by
    simpa [prefixWord, tailWord_3389196, baseEnd_3389196] using wordTrace_append hprefix tailTrace_3389196
  have hstable : (prefixWord ++ tailWord_3389196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389196).length < 2 ^ (prefixWord ++ tailWord_3389196).sum := by decide
  have hdescent : baseEnd_3389196 < baseStart_3389196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389203 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 5, 4, 2]
def baseStart_3389203 : Nat := 118140960795 + 3389203 * 2 ^ 59
def prefixEnd_3389203 : Nat := 4983230072969 + 3 ^ 40 * 3389203 * 2
def baseEnd_3389203 : Nat := 1740290174660208461375845

theorem tailTrace_3389203 : CollatzResearch.WordTrace tailWord_3389203 prefixEnd_3389203 1740290174660208461375845 := by
  unfold tailWord_3389203
  simp only [CollatzResearch.WordTrace]
  refine ⟨123614388740503835634516263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82409592493669223756344175 123614388740503835634516263)
  ·
    refine ⟨185421583110755753451774395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123614388740503835634516263 185421583110755753451774395)
    ·
      refine ⟨278132374666133630177661593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185421583110755753451774395 278132374666133630177661593)
      ·
        refine ⟨208599280999600222633246195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278132374666133630177661593 208599280999600222633246195)
        ·
          refine ⟨312898921499400333949869293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208599280999600222633246195 312898921499400333949869293)
          ·
            refine ⟨117337095562275125231200985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312898921499400333949869293 117337095562275125231200985)
            ·
              refine ⟨88002821671706343923400739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117337095562275125231200985 88002821671706343923400739)
              ·
                refine ⟨132004232507559515885101109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88002821671706343923400739 132004232507559515885101109)
                ·
                  refine ⟨12375396797583704614228229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 132004232507559515885101109 12375396797583704614228229)
                  ·
                    refine ⟨2320386899546944615167793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12375396797583704614228229 2320386899546944615167793)
                    ·
                      refine ⟨1740290174660208461375845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320386899546944615167793 1740290174660208461375845)
                      ·
                        rfl

theorem cell23_3389203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 4, 2].length) (baseStart_3389203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389203 prefixEnd_3389203 := by exact prefixLift 3389203
  have htrace : WordTrace (prefixWord ++ tailWord_3389203) baseStart_3389203 baseEnd_3389203 := by
    simpa [prefixWord, tailWord_3389203, baseEnd_3389203] using wordTrace_append hprefix tailTrace_3389203
  have hstable : (prefixWord ++ tailWord_3389203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389203).length < 2 ^ (prefixWord ++ tailWord_3389203).sum := by decide
  have hdescent : baseEnd_3389203 < baseStart_3389203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389224 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_3389224 : Nat := 118140960795 + 3389224 * 2 ^ 59
def prefixEnd_3389224 : Nat := 4983230072969 + 3 ^ 40 * 3389224 * 2
def baseEnd_3389224 : Nat := 1740300957753952879213249

theorem tailTrace_3389224 : CollatzResearch.WordTrace tailWord_3389224 prefixEnd_3389224 1740300957753952879213249 := by
  unfold tailWord_3389224
  simp only [CollatzResearch.WordTrace]
  refine ⟨61807577336713878110515363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82410103115618504147353817 61807577336713878110515363)
  ·
    refine ⟨92711366005070817165773045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61807577336713878110515363 92711366005070817165773045)
    ·
      refine ⟨8691690562975389109291223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92711366005070817165773045 8691690562975389109291223)
      ·
        refine ⟨13037535844463083663936835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8691690562975389109291223 13037535844463083663936835)
        ·
          refine ⟨19556303766694625495905253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13037535844463083663936835 19556303766694625495905253)
          ·
            refine ⟨3666806956255242280482235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19556303766694625495905253 3666806956255242280482235)
            ·
              refine ⟨5500210434382863420723353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3666806956255242280482235 5500210434382863420723353)
              ·
                refine ⟨4125157825787147565542515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5500210434382863420723353 4125157825787147565542515)
                ·
                  refine ⟨6187736738680721348313773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125157825787147565542515 6187736738680721348313773)
                  ·
                    refine ⟨2320401277005270505617665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6187736738680721348313773 2320401277005270505617665)
                    ·
                      refine ⟨1740300957753952879213249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320401277005270505617665 1740300957753952879213249)
                      ·
                        rfl

theorem cell23_3389224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_3389224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389224 prefixEnd_3389224 := by exact prefixLift 3389224
  have htrace : WordTrace (prefixWord ++ tailWord_3389224) baseStart_3389224 baseEnd_3389224 := by
    simpa [prefixWord, tailWord_3389224, baseEnd_3389224] using wordTrace_append hprefix tailTrace_3389224
  have hstable : (prefixWord ++ tailWord_3389224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389224).length < 2 ^ (prefixWord ++ tailWord_3389224).sum := by decide
  have hdescent : baseEnd_3389224 < baseStart_3389224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389237 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_3389237 : Nat := 118140960795 + 3389237 * 2 ^ 59
def prefixEnd_3389237 : Nat := 4983230072969 + 3 ^ 40 * 3389237 * 2
def baseEnd_3389237 : Nat := 1740307633002461328350689

theorem tailTrace_3389237 : CollatzResearch.WordTrace tailWord_3389237 prefixEnd_3389237 1740307633002461328350689 := by
  unfold tailWord_3389237
  simp only [CollatzResearch.WordTrace]
  refine ⟨123615628822380659441253965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82410419214920439627502643 123615628822380659441253965)
  ·
    refine ⟨46355860808392747290470237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123615628822380659441253965 46355860808392747290470237)
    ·
      refine ⟨17383447803147280233926339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46355860808392747290470237 17383447803147280233926339)
      ·
        refine ⟨26075171704720920350889509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17383447803147280233926339 26075171704720920350889509)
        ·
          refine ⟨4889094694635172565791783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26075171704720920350889509 4889094694635172565791783)
          ·
            refine ⟨7333642041952758848687675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889094694635172565791783 7333642041952758848687675)
            ·
              refine ⟨11000463062929138273031513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7333642041952758848687675 11000463062929138273031513)
              ·
                refine ⟨8250347297196853704773635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11000463062929138273031513 8250347297196853704773635)
                ·
                  refine ⟨12375520945795280557160453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250347297196853704773635 12375520945795280557160453)
                  ·
                    refine ⟨2320410177336615104467585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12375520945795280557160453 2320410177336615104467585)
                    ·
                      refine ⟨1740307633002461328350689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320410177336615104467585 1740307633002461328350689)
                      ·
                        rfl

theorem cell23_3389237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_3389237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389237 prefixEnd_3389237 := by exact prefixLift 3389237
  have htrace : WordTrace (prefixWord ++ tailWord_3389237) baseStart_3389237 baseEnd_3389237 := by
    simpa [prefixWord, tailWord_3389237, baseEnd_3389237] using wordTrace_append hprefix tailTrace_3389237
  have hstable : (prefixWord ++ tailWord_3389237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389237).length < 2 ^ (prefixWord ++ tailWord_3389237).sum := by decide
  have hdescent : baseEnd_3389237 < baseStart_3389237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389241 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3389241 : Nat := 118140960795 + 3389241 * 2 ^ 59
def prefixEnd_3389241 : Nat := 4983230072969 + 3 ^ 40 * 3389241 * 2
def baseEnd_3389241 : Nat := 1740309686925079312700671

theorem tailTrace_3389241 : CollatzResearch.WordTrace tailWord_3389241 prefixEnd_3389241 1740309686925079312700671 := by
  unfold tailWord_3389241
  simp only [CollatzResearch.WordTrace]
  refine ⟨123615774714366168124399577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82410516476244112082933051 123615774714366168124399577)
  ·
    refine ⟨92711831035774626093299683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123615774714366168124399577 92711831035774626093299683)
    ·
      refine ⟨139067746553661939139949525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92711831035774626093299683 139067746553661939139949525)
      ·
        refine ⟨3259400309851451698592567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 139067746553661939139949525 3259400309851451698592567)
        ·
          refine ⟨4889100464777177547888851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259400309851451698592567 4889100464777177547888851)
          ·
            refine ⟨7333650697165766321833277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889100464777177547888851 7333650697165766321833277)
            ·
              refine ⟨2750119011437162370687479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7333650697165766321833277 2750119011437162370687479)
              ·
                refine ⟨4125178517155743556031219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750119011437162370687479 4125178517155743556031219)
                ·
                  refine ⟨6187767775733615334046829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125178517155743556031219 6187767775733615334046829)
                  ·
                    refine ⟨2320412915900105750267561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6187767775733615334046829 2320412915900105750267561)
                    ·
                      refine ⟨1740309686925079312700671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320412915900105750267561 1740309686925079312700671)
                      ·
                        rfl

theorem cell23_3389241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3389241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389241 prefixEnd_3389241 := by exact prefixLift 3389241
  have htrace : WordTrace (prefixWord ++ tailWord_3389241) baseStart_3389241 baseEnd_3389241 := by
    simpa [prefixWord, tailWord_3389241, baseEnd_3389241] using wordTrace_append hprefix tailTrace_3389241
  have hstable : (prefixWord ++ tailWord_3389241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389241).length < 2 ^ (prefixWord ++ tailWord_3389241).sum := by decide
  have hdescent : baseEnd_3389241 < baseStart_3389241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389253 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_3389253 : Nat := 118140960795 + 3389253 * 2 ^ 59
def prefixEnd_3389253 : Nat := 4983230072969 + 3 ^ 40 * 3389253 * 2
def baseEnd_3389253 : Nat := 1740315848692933265750615

theorem tailTrace_3389253 : CollatzResearch.WordTrace tailWord_3389253 prefixEnd_3389253 1740315848692933265750615 := by
  unfold tailWord_3389253
  simp only [CollatzResearch.WordTrace]
  refine ⟨123616212390322694173836413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82410808260215129449224275 123616212390322694173836413)
  ·
    refine ⟨46356079646371010315188655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123616212390322694173836413 46356079646371010315188655)
    ·
      refine ⟨69534119469556515472782983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46356079646371010315188655 69534119469556515472782983)
      ·
        refine ⟨104301179204334773209174475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69534119469556515472782983 104301179204334773209174475)
        ·
          refine ⟨156451768806502159813761713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104301179204334773209174475 156451768806502159813761713)
          ·
            refine ⟨117338826604876619860321285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156451768806502159813761713 117338826604876619860321285)
            ·
              refine ⟨22001029988414366223810241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117338826604876619860321285 22001029988414366223810241)
              ·
                refine ⟨16500772491310774667857681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22001029988414366223810241 16500772491310774667857681)
                ·
                  refine ⟨12375579368483081000893261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16500772491310774667857681 12375579368483081000893261)
                  ·
                    refine ⟨4640842263181155375334973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12375579368483081000893261 4640842263181155375334973)
                    ·
                      refine ⟨1740315848692933265750615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4640842263181155375334973 1740315848692933265750615)
                      ·
                        rfl

theorem cell23_3389253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_3389253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389253 prefixEnd_3389253 := by exact prefixLift 3389253
  have htrace : WordTrace (prefixWord ++ tailWord_3389253) baseStart_3389253 baseEnd_3389253 := by
    simpa [prefixWord, tailWord_3389253, baseEnd_3389253] using wordTrace_append hprefix tailTrace_3389253
  have hstable : (prefixWord ++ tailWord_3389253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389253).length < 2 ^ (prefixWord ++ tailWord_3389253).sum := by decide
  have hdescent : baseEnd_3389253 < baseStart_3389253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389370 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2]
def baseStart_3389370 : Nat := 118140960795 + 3389370 * 2 ^ 59
def prefixEnd_3389370 : Nat := 4983230072969 + 3 ^ 40 * 3389370 * 2
def baseEnd_3389370 : Nat := 1740375925929509307987577

theorem tailTrace_3389370 : CollatzResearch.WordTrace tailWord_3389370 prefixEnd_3389370 1740375925929509307987577 := by
  unfold tailWord_3389370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30905119932724705788961391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82413653153932548770563709 30905119932724705788961391)
  ·
    refine ⟨46357679899087058683442087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30905119932724705788961391 46357679899087058683442087)
    ·
      refine ⟨69536519848630588025163131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46357679899087058683442087 69536519848630588025163131)
      ·
        refine ⟨104304779772945882037744697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69536519848630588025163131 104304779772945882037744697)
        ·
          refine ⟨78228584829709411528308523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104304779772945882037744697 78228584829709411528308523)
          ·
            refine ⟨117342877244564117292462785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78228584829709411528308523 117342877244564117292462785)
            ·
              refine ⟨88007157933423087969347089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117342877244564117292462785 88007157933423087969347089)
              ·
                refine ⟨66005368450067315977010317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88007157933423087969347089 66005368450067315977010317)
                ·
                  refine ⟨24752013168775243491378869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66005368450067315977010317 24752013168775243491378869)
                  ·
                    refine ⟨2320501234572679077316769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24752013168775243491378869 2320501234572679077316769)
                    ·
                      refine ⟨1740375925929509307987577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320501234572679077316769 1740375925929509307987577)
                      ·
                        rfl

theorem cell23_3389370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2].length) (baseStart_3389370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389370 prefixEnd_3389370 := by exact prefixLift 3389370
  have htrace : WordTrace (prefixWord ++ tailWord_3389370) baseStart_3389370 baseEnd_3389370 := by
    simpa [prefixWord, tailWord_3389370, baseEnd_3389370] using wordTrace_append hprefix tailTrace_3389370
  have hstable : (prefixWord ++ tailWord_3389370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389370).length < 2 ^ (prefixWord ++ tailWord_3389370).sum := by decide
  have hdescent : baseEnd_3389370 < baseStart_3389370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389383 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3389383 : Nat := 118140960795 + 3389383 * 2 ^ 59
def prefixEnd_3389383 : Nat := 4983230072969 + 3 ^ 40 * 3389383 * 2
def baseEnd_3389383 : Nat := 1740382601178017757125017

theorem tailTrace_3389383 : CollatzResearch.WordTrace tailWord_3389383 prefixEnd_3389383 1740382601178017757125017 := by
  unfold tailWord_3389383
  simp only [CollatzResearch.WordTrace]
  refine ⟨123620953879851726376068803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82413969253234484250712535 123620953879851726376068803)
  ·
    refine ⟨185431430819777589564103205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123620953879851726376068803 185431430819777589564103205)
    ·
      refine ⟨34768393278708298043269351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185431430819777589564103205 34768393278708298043269351)
      ·
        refine ⟨52152589918062447064904027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34768393278708298043269351 52152589918062447064904027)
        ·
          refine ⟨78228884877093670597356041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52152589918062447064904027 78228884877093670597356041)
          ·
            refine ⟨58671663657820252948017031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78228884877093670597356041 58671663657820252948017031)
            ·
              refine ⟨88007495486730379422025547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58671663657820252948017031 88007495486730379422025547)
              ·
                refine ⟨132011243230095569133038321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88007495486730379422025547 132011243230095569133038321)
                ·
                  refine ⟨99008432422571676849778741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132011243230095569133038321 99008432422571676849778741)
                  ·
                    refine ⟨9282040539616094704666757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99008432422571676849778741 9282040539616094704666757)
                    ·
                      refine ⟨1740382601178017757125017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9282040539616094704666757 1740382601178017757125017)
                      ·
                        rfl

theorem cell23_3389383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3389383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389383 prefixEnd_3389383 := by exact prefixLift 3389383
  have htrace : WordTrace (prefixWord ++ tailWord_3389383) baseStart_3389383 baseEnd_3389383 := by
    simpa [prefixWord, tailWord_3389383, baseEnd_3389383] using wordTrace_append hprefix tailTrace_3389383
  have hstable : (prefixWord ++ tailWord_3389383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389383).length < 2 ^ (prefixWord ++ tailWord_3389383).sum := by decide
  have hdescent : baseEnd_3389383 < baseStart_3389383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389397 : List Nat := [1, 3, 2, 3, 2, 1, 3, 2, 1, 5]
def baseStart_3389397 : Nat := 118140960795 + 3389397 * 2 ^ 59
def prefixEnd_3389397 : Nat := 4983230072969 + 3 ^ 40 * 3389397 * 2
def baseEnd_3389397 : Nat := 580129929969060234116651

theorem tailTrace_3389397 : CollatzResearch.WordTrace tailWord_3389397 prefixEnd_3389397 580129929969060234116651 := by
  unfold tailWord_3389397
  simp only [CollatzResearch.WordTrace]
  refine ⟨123621464501801006767078445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82414309667867337844718963 123621464501801006767078445)
  ·
    refine ⟨46358049188175377537654417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123621464501801006767078445 46358049188175377537654417)
    ·
      refine ⟨34768536891131533153240813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46358049188175377537654417 34768536891131533153240813)
      ·
        refine ⟨13038201334174324932465305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34768536891131533153240813 13038201334174324932465305)
        ·
          refine ⟨9778651000630743699348979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13038201334174324932465305 9778651000630743699348979)
          ·
            refine ⟨14667976500946115549023469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9778651000630743699348979 14667976500946115549023469)
            ·
              refine ⟨5500491187854793330883801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14667976500946115549023469 5500491187854793330883801)
              ·
                refine ⟨4125368390891094998162851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5500491187854793330883801 4125368390891094998162851)
                ·
                  refine ⟨6188052586336642497244277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4125368390891094998162851 6188052586336642497244277)
                  ·
                    refine ⟨580129929969060234116651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188052586336642497244277 580129929969060234116651)
                    ·
                      rfl

theorem cell23_3389397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_3389397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389397 prefixEnd_3389397 := by exact prefixLift 3389397
  have htrace : WordTrace (prefixWord ++ tailWord_3389397) baseStart_3389397 baseEnd_3389397 := by
    simpa [prefixWord, tailWord_3389397, baseEnd_3389397] using wordTrace_append hprefix tailTrace_3389397
  have hstable : (prefixWord ++ tailWord_3389397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389397).length < 2 ^ (prefixWord ++ tailWord_3389397).sum := by decide
  have hdescent : baseEnd_3389397 < baseStart_3389397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389400 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3389400 : Nat := 118140960795 + 3389400 * 2 ^ 59
def prefixEnd_3389400 : Nat := 4983230072969 + 3 ^ 40 * 3389400 * 2
def baseEnd_3389400 : Nat := 1740391330349144190612439

theorem tailTrace_3389400 : CollatzResearch.WordTrace tailWord_3389400 prefixEnd_3389400 1740391330349144190612439 := by
  unfold tailWord_3389400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61810786960395069139718827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82414382613860092186291769 61810786960395069139718827)
  ·
    refine ⟨92716180440592603709578241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61810786960395069139718827 92716180440592603709578241)
    ·
      refine ⟨69537135330444452782183681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92716180440592603709578241 69537135330444452782183681)
      ·
        refine ⟨52152851497833339586637761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69537135330444452782183681 52152851497833339586637761)
        ·
          refine ⟨39114638623375004689978321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52152851497833339586637761 39114638623375004689978321)
          ·
            refine ⟨29335978967531253517483741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39114638623375004689978321 29335978967531253517483741)
            ·
              refine ⟨11000992112824220069056403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29335978967531253517483741 11000992112824220069056403)
              ·
                refine ⟨16501488169236330103584605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11000992112824220069056403 16501488169236330103584605)
                ·
                  refine ⟨6188058063463623788844227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16501488169236330103584605 6188058063463623788844227)
                  ·
                    refine ⟨9282087095195435683266341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6188058063463623788844227 9282087095195435683266341)
                    ·
                      refine ⟨1740391330349144190612439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9282087095195435683266341 1740391330349144190612439)
                      ·
                        rfl

theorem cell23_3389400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3389400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389400 prefixEnd_3389400 := by exact prefixLift 3389400
  have htrace : WordTrace (prefixWord ++ tailWord_3389400) baseStart_3389400 baseEnd_3389400 := by
    simpa [prefixWord, tailWord_3389400, baseEnd_3389400] using wordTrace_append hprefix tailTrace_3389400
  have hstable : (prefixWord ++ tailWord_3389400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389400).length < 2 ^ (prefixWord ++ tailWord_3389400).sum := by decide
  have hdescent : baseEnd_3389400 < baseStart_3389400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389443 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6]
def baseStart_3389443 : Nat := 118140960795 + 3389443 * 2 ^ 59
def prefixEnd_3389443 : Nat := 4983230072969 + 3 ^ 40 * 3389443 * 2
def baseEnd_3389443 : Nat := 1740413410017287522374741

theorem tailTrace_3389443 : CollatzResearch.WordTrace tailWord_3389443 prefixEnd_3389443 1740413410017287522374741 := by
  unfold tailWord_3389443
  simp only [CollatzResearch.WordTrace]
  refine ⟨123623142259634356623252983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82415428173089571082168655 123623142259634356623252983)
  ·
    refine ⟨185434713389451534934879475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123623142259634356623252983 185434713389451534934879475)
    ·
      refine ⟨278152070084177302402319213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185434713389451534934879475 278152070084177302402319213)
      ·
        refine ⟨104307026281566488400869705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278152070084177302402319213 104307026281566488400869705)
        ·
          refine ⟨78230269711174866300652279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104307026281566488400869705 78230269711174866300652279)
          ·
            refine ⟨117345404566762299450978419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78230269711174866300652279 117345404566762299450978419)
            ·
              refine ⟨176018106850143449176467629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117345404566762299450978419 176018106850143449176467629)
              ·
                refine ⟨66006790068803793441175361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176018106850143449176467629 66006790068803793441175361)
                ·
                  refine ⟨49505092551602845080881521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66006790068803793441175361 49505092551602845080881521)
                  ·
                    refine ⟨37128819413702133810661141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49505092551602845080881521 37128819413702133810661141)
                    ·
                      refine ⟨1740413410017287522374741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37128819413702133810661141 1740413410017287522374741)
                      ·
                        rfl

theorem cell23_3389443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_3389443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389443 prefixEnd_3389443 := by exact prefixLift 3389443
  have htrace : WordTrace (prefixWord ++ tailWord_3389443) baseStart_3389443 baseEnd_3389443 := by
    simpa [prefixWord, tailWord_3389443, baseEnd_3389443] using wordTrace_append hprefix tailTrace_3389443
  have hstable : (prefixWord ++ tailWord_3389443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389443).length < 2 ^ (prefixWord ++ tailWord_3389443).sum := by decide
  have hdescent : baseEnd_3389443 < baseStart_3389443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389444 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_3389444 : Nat := 118140960795 + 3389444 * 2 ^ 59
def prefixEnd_3389444 : Nat := 4983230072969 + 3 ^ 40 * 3389444 * 2
def baseEnd_3389444 : Nat := 580137974499314006154079

theorem tailTrace_3389444 : CollatzResearch.WordTrace tailWord_3389444 prefixEnd_3389444 580137974499314006154079 := by
  unfold tailWord_3389444
  simp only [CollatzResearch.WordTrace]
  refine ⟨61811589366315366897019693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82415452488420489196026257 61811589366315366897019693)
  ·
    refine ⟨23179346012368262586382385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61811589366315366897019693 23179346012368262586382385)
    ·
      refine ⟨17384509509276196939786789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23179346012368262586382385 17384509509276196939786789)
      ·
        refine ⟨3259595532989286926210023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17384509509276196939786789 3259595532989286926210023)
        ·
          refine ⟨4889393299483930389315035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3259595532989286926210023 4889393299483930389315035)
          ·
            refine ⟨7334089949225895583972553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4889393299483930389315035 7334089949225895583972553)
            ·
              refine ⟨5500567461919421687979415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7334089949225895583972553 5500567461919421687979415)
              ·
                refine ⟨8250851192879132531969123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500567461919421687979415 8250851192879132531969123)
                ·
                  refine ⟨12376276789318698797953685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250851192879132531969123 12376276789318698797953685)
                  ·
                    refine ⟨580137974499314006154079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12376276789318698797953685 580137974499314006154079)
                    ·
                      rfl

theorem cell23_3389444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_3389444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389444 prefixEnd_3389444 := by exact prefixLift 3389444
  have htrace : WordTrace (prefixWord ++ tailWord_3389444) baseStart_3389444 baseEnd_3389444 := by
    simpa [prefixWord, tailWord_3389444, baseEnd_3389444] using wordTrace_append hprefix tailTrace_3389444
  have hstable : (prefixWord ++ tailWord_3389444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389444).length < 2 ^ (prefixWord ++ tailWord_3389444).sum := by decide
  have hdescent : baseEnd_3389444 < baseStart_3389444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389447 : List Nat := [1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3389447 : Nat := 118140960795 + 3389447 * 2 ^ 59
def prefixEnd_3389447 : Nat := 4983230072969 + 3 ^ 40 * 3389447 * 2
def baseEnd_3389447 : Nat := 1740415463939905506724723

theorem tailTrace_3389447 : CollatzResearch.WordTrace tailWord_3389447 prefixEnd_3389447 1740415463939905506724723 := by
  unfold tailWord_3389447
  simp only [CollatzResearch.WordTrace]
  refine ⟨123623288151619865306398595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82415525434413243537599063 123623288151619865306398595)
  ·
    refine ⟨185434932227429797959597893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123623288151619865306398595 185434932227429797959597893)
    ·
      refine ⟨34769049792643087117424605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185434932227429797959597893 34769049792643087117424605)
      ·
        refine ⟨13038393672241157669034227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34769049792643087117424605 13038393672241157669034227)
        ·
          refine ⟨19557590508361736503551341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038393672241157669034227 19557590508361736503551341)
          ·
            refine ⟨7334096440635651188831753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19557590508361736503551341 7334096440635651188831753)
            ·
              refine ⟨5500572330476738391623815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7334096440635651188831753 5500572330476738391623815)
              ·
                refine ⟨8250858495715107587435723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500572330476738391623815 8250858495715107587435723)
                ·
                  refine ⟨12376287743572661381153585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8250858495715107587435723 12376287743572661381153585)
                  ·
                    refine ⟨9282215807679496035865189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12376287743572661381153585 9282215807679496035865189)
                    ·
                      refine ⟨1740415463939905506724723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9282215807679496035865189 1740415463939905506724723)
                      ·
                        rfl

theorem cell23_3389447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3389447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389447 prefixEnd_3389447 := by exact prefixLift 3389447
  have htrace : WordTrace (prefixWord ++ tailWord_3389447) baseStart_3389447 baseEnd_3389447 := by
    simpa [prefixWord, tailWord_3389447, baseEnd_3389447] using wordTrace_append hprefix tailTrace_3389447
  have hstable : (prefixWord ++ tailWord_3389447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389447).length < 2 ^ (prefixWord ++ tailWord_3389447).sum := by decide
  have hdescent : baseEnd_3389447 < baseStart_3389447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389468 : List Nat := [2, 2, 3, 1, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3389468 : Nat := 118140960795 + 3389468 * 2 ^ 59
def prefixEnd_3389468 : Nat := 4983230072969 + 3 ^ 40 * 3389468 * 2
def baseEnd_3389468 : Nat := 1740426247033649924562127

theorem tailTrace_3389468 : CollatzResearch.WordTrace tailWord_3389468 prefixEnd_3389468 1740426247033649924562127 := by
  unfold tailWord_3389468
  simp only [CollatzResearch.WordTrace]
  refine ⟨61812027042271892946456529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82416036056362523928608705 61812027042271892946456529)
  ·
    refine ⟨46359020281703919709842397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61812027042271892946456529 46359020281703919709842397)
    ·
      refine ⟨17384632605638969891190899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46359020281703919709842397 17384632605638969891190899)
      ·
        refine ⟨26076948908458454836786349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17384632605638969891190899 26076948908458454836786349)
        ·
          refine ⟨9778855840671920563794881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26076948908458454836786349 9778855840671920563794881)
          ·
            refine ⟨7334141880503940422846161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9778855840671920563794881 7334141880503940422846161)
            ·
              refine ⟨5500606410377955317134621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7334141880503940422846161 5500606410377955317134621)
              ·
                refine ⟨2062727403891733243925483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5500606410377955317134621 2062727403891733243925483)
                ·
                  refine ⟨3094091105837599865888225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062727403891733243925483 3094091105837599865888225)
                  ·
                    refine ⟨2320568329378199899416169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094091105837599865888225 2320568329378199899416169)
                    ·
                      refine ⟨1740426247033649924562127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320568329378199899416169 1740426247033649924562127)
                      ·
                        rfl

theorem cell23_3389468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3389468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389468 prefixEnd_3389468 := by exact prefixLift 3389468
  have htrace : WordTrace (prefixWord ++ tailWord_3389468) baseStart_3389468 baseEnd_3389468 := by
    simpa [prefixWord, tailWord_3389468, baseEnd_3389468] using wordTrace_append hprefix tailTrace_3389468
  have hstable : (prefixWord ++ tailWord_3389468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389468).length < 2 ^ (prefixWord ++ tailWord_3389468).sum := by decide
  have hdescent : baseEnd_3389468 < baseStart_3389468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389500 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 2, 6]
def baseStart_3389500 : Nat := 118140960795 + 3389500 * 2 ^ 59
def prefixEnd_3389500 : Nat := 4983230072969 + 3 ^ 40 * 3389500 * 2
def baseEnd_3389500 : Nat := 580147559471531266453993

theorem tailTrace_3389500 : CollatzResearch.WordTrace tailWord_3389500 prefixEnd_3389500 580147559471531266453993 := by
  unfold tailWord_3389500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61812610610213927679038977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82416814146951903572051969 61812610610213927679038977)
  ·
    refine ⟨46359457957660445759279233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61812610610213927679038977 46359457957660445759279233)
    ·
      refine ⟨34769593468245334319459425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46359457957660445759279233 34769593468245334319459425)
      ·
        refine ⟨26077195101184000739594569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34769593468245334319459425 26077195101184000739594569)
        ·
          refine ⟨19557896325888000554695927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26077195101184000739594569 19557896325888000554695927)
          ·
            refine ⟨29336844488832000832043891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557896325888000554695927 29336844488832000832043891)
            ·
              refine ⟨44005266733248001248065837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29336844488832000832043891 44005266733248001248065837)
              ·
                refine ⟨16501975024968000468024689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44005266733248001248065837 16501975024968000468024689)
                ·
                  refine ⟨12376481268726000351018517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16501975024968000468024689 12376481268726000351018517)
                  ·
                    refine ⟨580147559471531266453993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12376481268726000351018517 580147559471531266453993)
                    ·
                      rfl

theorem cell23_3389500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_3389500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389500 prefixEnd_3389500 := by exact prefixLift 3389500
  have htrace : WordTrace (prefixWord ++ tailWord_3389500) baseStart_3389500 baseEnd_3389500 := by
    simpa [prefixWord, tailWord_3389500, baseEnd_3389500] using wordTrace_append hprefix tailTrace_3389500
  have hstable : (prefixWord ++ tailWord_3389500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389500).length < 2 ^ (prefixWord ++ tailWord_3389500).sum := by decide
  have hdescent : baseEnd_3389500 < baseStart_3389500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389501 : List Nat := [1, 4, 1, 3, 1, 1, 5, 1, 2, 1, 3]
def baseStart_3389501 : Nat := 118140960795 + 3389501 * 2 ^ 59
def prefixEnd_3389501 : Nat := 4983230072969 + 3 ^ 40 * 3389501 * 2
def baseEnd_3389501 : Nat := 1740443191895248295449475

theorem tailTrace_3389501 : CollatzResearch.WordTrace tailWord_3389501 prefixEnd_3389501 1740443191895248295449475 := by
  unfold tailWord_3389501
  simp only [CollatzResearch.WordTrace]
  refine ⟨123625257693424232528864357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82416838462282821685909571 123625257693424232528864357)
  ·
    refine ⟨23179735817517043599162067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123625257693424232528864357 23179735817517043599162067)
    ·
      refine ⟨34769603726275565398743101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23179735817517043599162067 34769603726275565398743101)
      ·
        refine ⟨13038601397353337024528663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34769603726275565398743101 13038601397353337024528663)
        ·
          refine ⟨19557902096030005536792995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038601397353337024528663 19557902096030005536792995)
          ·
            refine ⟨29336853144045008305189493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19557902096030005536792995 29336853144045008305189493)
            ·
              refine ⟨2750329982254219528611515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29336853144045008305189493 2750329982254219528611515)
              ·
                refine ⟨4125494973381329292917273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750329982254219528611515 4125494973381329292917273)
                ·
                  refine ⟨3094121230035996969687955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125494973381329292917273 3094121230035996969687955)
                  ·
                    refine ⟨4641181845053995454531933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3094121230035996969687955 4641181845053995454531933)
                    ·
                      refine ⟨1740443191895248295449475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4641181845053995454531933 1740443191895248295449475)
                      ·
                        rfl

theorem cell23_3389501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_3389501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389501 prefixEnd_3389501 := by exact prefixLift 3389501
  have htrace : WordTrace (prefixWord ++ tailWord_3389501) baseStart_3389501 baseEnd_3389501 := by
    simpa [prefixWord, tailWord_3389501, baseEnd_3389501] using wordTrace_append hprefix tailTrace_3389501
  have hstable : (prefixWord ++ tailWord_3389501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389501).length < 2 ^ (prefixWord ++ tailWord_3389501).sum := by decide
  have hdescent : baseEnd_3389501 < baseStart_3389501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389507 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 1, 4, 2]
def baseStart_3389507 : Nat := 118140960795 + 3389507 * 2 ^ 59
def prefixEnd_3389507 : Nat := 4983230072969 + 3 ^ 40 * 3389507 * 2
def baseEnd_3389507 : Nat := 1740446272779175271974447

theorem tailTrace_3389507 : CollatzResearch.WordTrace tailWord_3389507 prefixEnd_3389507 1740446272779175271974447 := by
  unfold tailWord_3389507
  simp only [CollatzResearch.WordTrace]
  refine ⟨123625476531402495553582775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82416984354268330369055183 123625476531402495553582775)
  ·
    refine ⟨185438214797103743330374163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123625476531402495553582775 185438214797103743330374163)
    ·
      refine ⟨278157322195655614995561245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185438214797103743330374163 278157322195655614995561245)
      ·
        refine ⟨104308995823370855623335467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 278157322195655614995561245 104308995823370855623335467)
        ·
          refine ⟨156463493735056283435003201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104308995823370855623335467 156463493735056283435003201)
          ·
            refine ⟨117347620301292212576252401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156463493735056283435003201 117347620301292212576252401)
            ·
              refine ⟨88010715225969159432189301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 117347620301292212576252401 88010715225969159432189301)
              ·
                refine ⟨8251004552434608696767747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88010715225969159432189301 8251004552434608696767747)
                ·
                  refine ⟨12376506828651913045151621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8251004552434608696767747 12376506828651913045151621)
                  ·
                    refine ⟨2320595030372233695965929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12376506828651913045151621 2320595030372233695965929)
                    ·
                      refine ⟨1740446272779175271974447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320595030372233695965929 1740446272779175271974447)
                      ·
                        rfl

theorem cell23_3389507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_3389507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389507 prefixEnd_3389507 := by exact prefixLift 3389507
  have htrace : WordTrace (prefixWord ++ tailWord_3389507) baseStart_3389507 baseEnd_3389507 := by
    simpa [prefixWord, tailWord_3389507, baseEnd_3389507] using wordTrace_append hprefix tailTrace_3389507
  have hstable : (prefixWord ++ tailWord_3389507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389507).length < 2 ^ (prefixWord ++ tailWord_3389507).sum := by decide
  have hdescent : baseEnd_3389507 < baseStart_3389507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389558 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2]
def baseStart_3389558 : Nat := 118140960795 + 3389558 * 2 ^ 59
def prefixEnd_3389558 : Nat := 4983230072969 + 3 ^ 40 * 3389558 * 2
def baseEnd_3389558 : Nat := 1740472460292554572436713

theorem tailTrace_3389558 : CollatzResearch.WordTrace tailWord_3389558 prefixEnd_3389558 1740472460292554572436713 := by
  unfold tailWord_3389558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7726708540888608203980583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82418224436145154175792885 7726708540888608203980583)
  ·
    refine ⟨11590062811332912305970875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7726708540888608203980583 11590062811332912305970875)
    ·
      refine ⟨17385094216999368458956313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11590062811332912305970875 17385094216999368458956313)
      ·
        refine ⟨13038820662749526344217235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17385094216999368458956313 13038820662749526344217235)
        ·
          refine ⟨19558230994124289516325853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13038820662749526344217235 19558230994124289516325853)
          ·
            refine ⟨7334336622796608568622195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19558230994124289516325853 7334336622796608568622195)
            ·
              refine ⟨11001504934194912852933293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7334336622796608568622195 11001504934194912852933293)
              ·
                refine ⟨4125564350323092319849985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11001504934194912852933293 4125564350323092319849985)
                ·
                  refine ⟨3094173262742319239887489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4125564350323092319849985 3094173262742319239887489)
                  ·
                    refine ⟨2320629947056739429915617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094173262742319239887489 2320629947056739429915617)
                    ·
                      refine ⟨1740472460292554572436713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320629947056739429915617 1740472460292554572436713)
                      ·
                        rfl

theorem cell23_3389558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_3389558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389558 prefixEnd_3389558 := by exact prefixLift 3389558
  have htrace : WordTrace (prefixWord ++ tailWord_3389558) baseStart_3389558 baseEnd_3389558 := by
    simpa [prefixWord, tailWord_3389558, baseEnd_3389558] using wordTrace_append hprefix tailTrace_3389558
  have hstable : (prefixWord ++ tailWord_3389558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389558).length < 2 ^ (prefixWord ++ tailWord_3389558).sum := by decide
  have hdescent : baseEnd_3389558 < baseStart_3389558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389560 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 6, 5]
def baseStart_3389560 : Nat := 118140960795 + 3389560 * 2 ^ 59
def prefixEnd_3389560 : Nat := 4983230072969 + 3 ^ 40 * 3389560 * 2
def baseEnd_3389560 : Nat := 580157829084621188203901

theorem tailTrace_3389560 : CollatzResearch.WordTrace tailWord_3389560 prefixEnd_3389560 580157829084621188203901 := by
  unfold tailWord_3389560
  simp only [CollatzResearch.WordTrace]
  refine ⟨61813704800105242802631067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82418273066806990403508089 61813704800105242802631067)
  ·
    refine ⟨92720557200157864203946601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61813704800105242802631067 92720557200157864203946601)
    ·
      refine ⟨69540417900118398152959951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92720557200157864203946601 69540417900118398152959951)
      ·
        refine ⟨104310626850177597229439927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69540417900118398152959951 104310626850177597229439927)
        ·
          refine ⟨156465940275266395844159891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104310626850177597229439927 156465940275266395844159891)
          ·
            refine ⟨234698910412899593766239837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156465940275266395844159891 234698910412899593766239837)
            ·
              refine ⟨88012091404837347662339939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234698910412899593766239837 88012091404837347662339939)
              ·
                refine ⟨132018137107256021493509909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88012091404837347662339939 132018137107256021493509909)
                ·
                  refine ⟨6188350176902626007508277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 132018137107256021493509909 6188350176902626007508277)
                  ·
                    refine ⟨580157829084621188203901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188350176902626007508277 580157829084621188203901)
                    ·
                      rfl

theorem cell23_3389560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_3389560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389560 prefixEnd_3389560 := by exact prefixLift 3389560
  have htrace : WordTrace (prefixWord ++ tailWord_3389560) baseStart_3389560 baseEnd_3389560 := by
    simpa [prefixWord, tailWord_3389560, baseEnd_3389560] using wordTrace_append hprefix tailTrace_3389560
  have hstable : (prefixWord ++ tailWord_3389560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389560).length < 2 ^ (prefixWord ++ tailWord_3389560).sum := by decide
  have hdescent : baseEnd_3389560 < baseStart_3389560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389577 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 2, 5]
def baseStart_3389577 : Nat := 118140960795 + 3389577 * 2 ^ 59
def prefixEnd_3389577 : Nat := 4983230072969 + 3 ^ 40 * 3389577 * 2
def baseEnd_3389577 : Nat := 580160738808329999366375

theorem tailTrace_3389577 : CollatzResearch.WordTrace tailWord_3389577 prefixEnd_3389577 580160738808329999366375 := by
  unfold tailWord_3389577
  simp only [CollatzResearch.WordTrace]
  refine ⟨123628029641148897508630985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82418686427432598339087323 123628029641148897508630985)
  ·
    refine ⟨92721022230861673131473239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123628029641148897508630985 92721022230861673131473239)
    ·
      refine ⟨139081533346292509697209859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92721022230861673131473239 139081533346292509697209859)
      ·
        refine ⟨208622300019438764545814789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139081533346292509697209859 208622300019438764545814789)
        ·
          refine ⟨39116681253644768352340273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208622300019438764545814789 39116681253644768352340273)
          ·
            refine ⟨29337510940233576264255205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39116681253644768352340273 29337510940233576264255205)
            ·
              refine ⟨5500783301293795549547851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29337510940233576264255205 5500783301293795549547851)
              ·
                refine ⟨8251174951940693324321777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5500783301293795549547851 8251174951940693324321777)
                ·
                  refine ⟨6188381213955519993241333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8251174951940693324321777 6188381213955519993241333)
                  ·
                    refine ⟨580160738808329999366375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188381213955519993241333 580160738808329999366375)
                    ·
                      rfl

theorem cell23_3389577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 2, 5].length) (baseStart_3389577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389577 prefixEnd_3389577 := by exact prefixLift 3389577
  have htrace : WordTrace (prefixWord ++ tailWord_3389577) baseStart_3389577 baseEnd_3389577 := by
    simpa [prefixWord, tailWord_3389577, baseEnd_3389577] using wordTrace_append hprefix tailTrace_3389577
  have hstable : (prefixWord ++ tailWord_3389577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389577).length < 2 ^ (prefixWord ++ tailWord_3389577).sum := by decide
  have hdescent : baseEnd_3389577 < baseStart_3389577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389671 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 6]
def baseStart_3389671 : Nat := 118140960795 + 3389671 * 2 ^ 59
def prefixEnd_3389671 : Nat := 4983230072969 + 3 ^ 40 * 3389671 * 2
def baseEnd_3389671 : Nat := 193392275956279181147077

theorem tailTrace_3389671 : CollatzResearch.WordTrace tailWord_3389671 prefixEnd_3389671 193392275956279181147077 := by
  unfold tailWord_3389671
  simp only [CollatzResearch.WordTrace]
  refine ⟨123631458102808351562552867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82420972068538901041701911 123631458102808351562552867)
  ·
    refine ⟨185447187154212527343829301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123631458102808351562552867 185447187154212527343829301)
    ·
      refine ⟨17385673795707424438483997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185447187154212527343829301 17385673795707424438483997)
      ·
        refine ⟨6519627673390284164431499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17385673795707424438483997 6519627673390284164431499)
        ·
          refine ⟨9779441510085426246647249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6519627673390284164431499 9779441510085426246647249)
          ·
            refine ⟨7334581132564069684985437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9779441510085426246647249 7334581132564069684985437)
            ·
              refine ⟨2750467924711526131869539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7334581132564069684985437 2750467924711526131869539)
              ·
                refine ⟨4125701887067289197804309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750467924711526131869539 4125701887067289197804309)
                ·
                  refine ⟨193392275956279181147077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4125701887067289197804309 193392275956279181147077)
                  ·
                    rfl

theorem cell23_3389671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 6].length) (baseStart_3389671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389671 prefixEnd_3389671 := by exact prefixLift 3389671
  have htrace : WordTrace (prefixWord ++ tailWord_3389671) baseStart_3389671 baseEnd_3389671 := by
    simpa [prefixWord, tailWord_3389671, baseEnd_3389671] using wordTrace_append hprefix tailTrace_3389671
  have hstable : (prefixWord ++ tailWord_3389671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389671).length < 2 ^ (prefixWord ++ tailWord_3389671).sum := by decide
  have hdescent : baseEnd_3389671 < baseStart_3389671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389674 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_3389674 : Nat := 118140960795 + 3389674 * 2 ^ 59
def prefixEnd_3389674 : Nat := 4983230072969 + 3 ^ 40 * 3389674 * 2
def baseEnd_3389674 : Nat := 1740532024048476118586179

theorem tailTrace_3389674 : CollatzResearch.WordTrace tailWord_3389674 prefixEnd_3389674 1740532024048476118586179 := by
  unfold tailWord_3389674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30907891880449370768728019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82421045014531655383274717 30907891880449370768728019)
  ·
    refine ⟨46361837820674056153092029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30907891880449370768728019 46361837820674056153092029)
    ·
      refine ⟨17385689182752771057409511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46361837820674056153092029 17385689182752771057409511)
      ·
        refine ⟨26078533774129156586114267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385689182752771057409511 26078533774129156586114267)
        ·
          refine ⟨39117800661193734879171401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26078533774129156586114267 39117800661193734879171401)
          ·
            refine ⟨29338350495895301159378551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39117800661193734879171401 29338350495895301159378551)
            ·
              refine ⟨44007525743842951739067827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29338350495895301159378551 44007525743842951739067827)
              ·
                refine ⟨66011288615764427608601741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44007525743842951739067827 66011288615764427608601741)
                ·
                  refine ⟨24754233230911660353225653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66011288615764427608601741 24754233230911660353225653)
                  ·
                    refine ⟨2320709365397968158114905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24754233230911660353225653 2320709365397968158114905)
                    ·
                      refine ⟨1740532024048476118586179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320709365397968158114905 1740532024048476118586179)
                      ·
                        rfl

theorem cell23_3389674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_3389674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389674 prefixEnd_3389674 := by exact prefixLift 3389674
  have htrace : WordTrace (prefixWord ++ tailWord_3389674) baseStart_3389674 baseEnd_3389674 := by
    simpa [prefixWord, tailWord_3389674, baseEnd_3389674] using wordTrace_append hprefix tailTrace_3389674
  have hstable : (prefixWord ++ tailWord_3389674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389674).length < 2 ^ (prefixWord ++ tailWord_3389674).sum := by decide
  have hdescent : baseEnd_3389674 < baseStart_3389674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389697 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 3, 6]
def baseStart_3389697 : Nat := 118140960795 + 3389697 * 2 ^ 59
def prefixEnd_3389697 : Nat := 4983230072969 + 3 ^ 40 * 3389697 * 2
def baseEnd_3389697 : Nat := 580181278034509842866191

theorem tailTrace_3389697 : CollatzResearch.WordTrace tailWord_3389697 prefixEnd_3389697 580181278034509842866191 := by
  unfold tailWord_3389697
  simp only [CollatzResearch.WordTrace]
  refine ⟨123632406400714158002999345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82421604267142772001999563 123632406400714158002999345)
  ·
    refine ⟨92724304800535618502249509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123632406400714158002999345 92724304800535618502249509)
    ·
      refine ⟨17385807150100428469171783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92724304800535618502249509 17385807150100428469171783)
      ·
        refine ⟨26078710725150642703757675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385807150100428469171783 26078710725150642703757675)
        ·
          refine ⟨39118066087725964055636513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26078710725150642703757675 39118066087725964055636513)
          ·
            refine ⟨29338549565794473041727385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39118066087725964055636513 29338549565794473041727385)
            ·
              refine ⟨22003912174345854781295539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29338549565794473041727385 22003912174345854781295539)
              ·
                refine ⟨33005868261518782171943309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22003912174345854781295539 33005868261518782171943309)
                ·
                  refine ⟨12377200598069543314478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33005868261518782171943309 12377200598069543314478741)
                  ·
                    refine ⟨580181278034509842866191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12377200598069543314478741 580181278034509842866191)
                    ·
                      rfl

theorem cell23_3389697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_3389697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389697 prefixEnd_3389697 := by exact prefixLift 3389697
  have htrace : WordTrace (prefixWord ++ tailWord_3389697) baseStart_3389697 baseEnd_3389697 := by
    simpa [prefixWord, tailWord_3389697, baseEnd_3389697] using wordTrace_append hprefix tailTrace_3389697
  have hstable : (prefixWord ++ tailWord_3389697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389697).length < 2 ^ (prefixWord ++ tailWord_3389697).sum := by decide
  have hdescent : baseEnd_3389697 < baseStart_3389697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389717 : List Nat := [1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_3389717 : Nat := 118140960795 + 3389717 * 2 ^ 59
def prefixEnd_3389717 : Nat := 4983230072969 + 3 ^ 40 * 3389717 * 2
def baseEnd_3389717 : Nat := 1740554103716619450348481

theorem tailTrace_3389717 : CollatzResearch.WordTrace tailWord_3389717 prefixEnd_3389717 1740554103716619450348481 := by
  unfold tailWord_3389717
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633135860641701418727405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82422090573761134279151603 123633135860641701418727405)
  ·
    refine ⟨46362425947740638032022777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123633135860641701418727405 46362425947740638032022777)
    ·
      refine ⟨34771819460805478524017083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46362425947740638032022777 34771819460805478524017083)
      ·
        refine ⟨52157729191208217786025625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34771819460805478524017083 52157729191208217786025625)
        ·
          refine ⟨39118296893406163339519219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52157729191208217786025625 39118296893406163339519219)
          ·
            refine ⟨58677445340109245009278829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118296893406163339519219 58677445340109245009278829)
            ·
              refine ⟨22004042002540966878479561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58677445340109245009278829 22004042002540966878479561)
              ·
                refine ⟨16503031501905725158859671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22004042002540966878479561 16503031501905725158859671)
                ·
                  refine ⟨24754547252858587738289507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16503031501905725158859671 24754547252858587738289507)
                  ·
                    refine ⟨37131820879287881607434261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24754547252858587738289507 37131820879287881607434261)
                    ·
                      refine ⟨1740554103716619450348481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37131820879287881607434261 1740554103716619450348481)
                      ·
                        rfl

theorem cell23_3389717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_3389717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389717 prefixEnd_3389717 := by exact prefixLift 3389717
  have htrace : WordTrace (prefixWord ++ tailWord_3389717) baseStart_3389717 baseEnd_3389717 := by
    simpa [prefixWord, tailWord_3389717, baseEnd_3389717] using wordTrace_append hprefix tailTrace_3389717
  have hstable : (prefixWord ++ tailWord_3389717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389717).length < 2 ^ (prefixWord ++ tailWord_3389717).sum := by decide
  have hdescent : baseEnd_3389717 < baseStart_3389717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389724 : List Nat := [2, 2, 3, 1, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3389724 : Nat := 118140960795 + 3389724 * 2 ^ 59
def prefixEnd_3389724 : Nat := 4983230072969 + 3 ^ 40 * 3389724 * 2
def baseEnd_3389724 : Nat := 1740557698081200922960949

theorem tailTrace_3389724 : CollatzResearch.WordTrace tailWord_3389724 prefixEnd_3389724 1740557698081200922960949 := by
  unfold tailWord_3389724
  simp only [CollatzResearch.WordTrace]
  refine ⟨61816695585808170807116113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82422260781077561076154817 61816695585808170807116113)
  ·
    refine ⟨46362521689356128105337085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61816695585808170807116113 46362521689356128105337085)
    ·
      refine ⟨17385945633508548039501407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46362521689356128105337085 17385945633508548039501407)
      ·
        refine ⟨26078918450262822059252111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17385945633508548039501407 26078918450262822059252111)
        ·
          refine ⟨39118377675394233088878167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26078918450262822059252111 39118377675394233088878167)
          ·
            refine ⟨58677566513091349633317251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39118377675394233088878167 58677566513091349633317251)
            ·
              refine ⟨88016349769637024449975877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58677566513091349633317251 88016349769637024449975877)
              ·
                refine ⟨16503065581806942084370477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88016349769637024449975877 16503065581806942084370477)
                ·
                  refine ⟨6188649593177603281638929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16503065581806942084370477 6188649593177603281638929)
                  ·
                    refine ⟨4641487194883202461229197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6188649593177603281638929 4641487194883202461229197)
                    ·
                      refine ⟨1740557698081200922960949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4641487194883202461229197 1740557698081200922960949)
                      ·
                        rfl

theorem cell23_3389724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3389724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389724 prefixEnd_3389724 := by exact prefixLift 3389724
  have htrace : WordTrace (prefixWord ++ tailWord_3389724) baseStart_3389724 baseEnd_3389724 := by
    simpa [prefixWord, tailWord_3389724, baseEnd_3389724] using wordTrace_append hprefix tailTrace_3389724
  have hstable : (prefixWord ++ tailWord_3389724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389724).length < 2 ^ (prefixWord ++ tailWord_3389724).sum := by decide
  have hdescent : baseEnd_3389724 < baseStart_3389724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389727 : List Nat := [1, 1, 2, 4, 3, 1, 1, 10]
def baseStart_3389727 : Nat := 118140960795 + 3389727 * 2 ^ 59
def prefixEnd_3389727 : Nat := 4983230072969 + 3 ^ 40 * 3389727 * 2
def baseEnd_3389727 : Nat := 64465156982339422637905

theorem tailTrace_3389727 : CollatzResearch.WordTrace tailWord_3389727 prefixEnd_3389727 64465156982339422637905 := by
  unfold tailWord_3389727
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633500590605473126591435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82422333727070315417727623 123633500590605473126591435)
  ·
    refine ⟨185450250885908209689887153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123633500590605473126591435 185450250885908209689887153)
    ·
      refine ⟨139087688164431157267415365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185450250885908209689887153 139087688164431157267415365)
      ·
        refine ⟨26078941530830841987640381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139087688164431157267415365 26078941530830841987640381)
        ·
          refine ⟨9779603074061565745365143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26078941530830841987640381 9779603074061565745365143)
          ·
            refine ⟨14669404611092348618047715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9779603074061565745365143 14669404611092348618047715)
            ·
              refine ⟨22004106916638522927071573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14669404611092348618047715 22004106916638522927071573)
              ·
                refine ⟨64465156982339422637905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22004106916638522927071573 64465156982339422637905)
                ·
                  rfl

theorem cell23_3389727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 10].length) (baseStart_3389727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389727 prefixEnd_3389727 := by exact prefixLift 3389727
  have htrace : WordTrace (prefixWord ++ tailWord_3389727) baseStart_3389727 baseEnd_3389727 := by
    simpa [prefixWord, tailWord_3389727, baseEnd_3389727] using wordTrace_append hprefix tailTrace_3389727
  have hstable : (prefixWord ++ tailWord_3389727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389727).length < 2 ^ (prefixWord ++ tailWord_3389727).sum := by decide
  have hdescent : baseEnd_3389727 < baseStart_3389727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389737 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 3]
def baseStart_3389737 : Nat := 118140960795 + 3389737 * 2 ^ 59
def prefixEnd_3389737 : Nat := 4983230072969 + 3 ^ 40 * 3389737 * 2
def baseEnd_3389737 : Nat := 1740564373329709372098389

theorem tailTrace_3389737 : CollatzResearch.WordTrace tailWord_3389737 prefixEnd_3389737 1740564373329709372098389 := by
  unfold tailWord_3389737
  simp only [CollatzResearch.WordTrace]
  refine ⟨123633865320569244834455465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82422576880379496556303643 123633865320569244834455465)
  ·
    refine ⟨92725398990426933625841599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123633865320569244834455465 92725398990426933625841599)
    ·
      refine ⟨139088098485640400438762399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92725398990426933625841599 139088098485640400438762399)
      ·
        refine ⟨208632147728460600658143599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139088098485640400438762399 208632147728460600658143599)
        ·
          refine ⟨312948221592690900987215399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208632147728460600658143599 312948221592690900987215399)
          ·
            refine ⟨469422332389036351480823099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312948221592690900987215399 469422332389036351480823099)
            ·
              refine ⟨704133498583554527221234649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 469422332389036351480823099 704133498583554527221234649)
              ·
                refine ⟨528100123937665895415925987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704133498583554527221234649 528100123937665895415925987)
                ·
                  refine ⟨792150185906498843123888981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 528100123937665895415925987 792150185906498843123888981)
                  ·
                    refine ⟨4641504995545891658929037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 792150185906498843123888981 4641504995545891658929037)
                    ·
                      refine ⟨1740564373329709372098389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4641504995545891658929037 1740564373329709372098389)
                      ·
                        rfl

theorem cell23_3389737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_3389737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389737 prefixEnd_3389737 := by exact prefixLift 3389737
  have htrace : WordTrace (prefixWord ++ tailWord_3389737) baseStart_3389737 baseEnd_3389737 := by
    simpa [prefixWord, tailWord_3389737, baseEnd_3389737] using wordTrace_append hprefix tailTrace_3389737
  have hstable : (prefixWord ++ tailWord_3389737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389737).length < 2 ^ (prefixWord ++ tailWord_3389737).sum := by decide
  have hdescent : baseEnd_3389737 < baseStart_3389737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389754 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3]
def baseStart_3389754 : Nat := 118140960795 + 3389754 * 2 ^ 59
def prefixEnd_3389754 : Nat := 4983230072969 + 3 ^ 40 * 3389754 * 2
def baseEnd_3389754 : Nat := 1740573102500835805585811

theorem tailTrace_3389754 : CollatzResearch.WordTrace tailWord_3389754 prefixEnd_3389754 1740573102500835805585811 := by
  unfold tailWord_3389754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30908621340376914184456079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82422990241005104491882877 30908621340376914184456079)
  ·
    refine ⟨46362932010565371276684119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30908621340376914184456079 46362932010565371276684119)
    ·
      refine ⟨69544398015848056915026179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46362932010565371276684119 69544398015848056915026179)
      ·
        refine ⟨104316597023772085372539269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69544398015848056915026179 104316597023772085372539269)
        ·
          refine ⟨19559361941957266007351113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104316597023772085372539269 19559361941957266007351113)
          ·
            refine ⟨14669521456467949505513335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19559361941957266007351113 14669521456467949505513335)
            ·
              refine ⟨22004282184701924258270003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14669521456467949505513335 22004282184701924258270003)
              ·
                refine ⟨33006423277052886387405005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22004282184701924258270003 33006423277052886387405005)
                ·
                  refine ⟨12377408728894832395276877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33006423277052886387405005 12377408728894832395276877)
                  ·
                    refine ⟨4641528273335562148228829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12377408728894832395276877 4641528273335562148228829)
                    ·
                      refine ⟨1740573102500835805585811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4641528273335562148228829 1740573102500835805585811)
                      ·
                        rfl

theorem cell23_3389754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3].length) (baseStart_3389754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389754 prefixEnd_3389754 := by exact prefixLift 3389754
  have htrace : WordTrace (prefixWord ++ tailWord_3389754) baseStart_3389754 baseEnd_3389754 := by
    simpa [prefixWord, tailWord_3389754, baseEnd_3389754] using wordTrace_append hprefix tailTrace_3389754
  have hstable : (prefixWord ++ tailWord_3389754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389754).length < 2 ^ (prefixWord ++ tailWord_3389754).sum := by decide
  have hdescent : baseEnd_3389754 < baseStart_3389754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389811 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 6, 2, 2]
def baseStart_3389811 : Nat := 118140960795 + 3389811 * 2 ^ 59
def prefixEnd_3389811 : Nat := 4983230072969 + 3 ^ 40 * 3389811 * 2
def baseEnd_3389811 : Nat := 1740602370898142082573049

theorem tailTrace_3389811 : CollatzResearch.WordTrace tailWord_3389811 prefixEnd_3389811 1740602370898142082573049 := by
  unfold tailWord_3389811
  simp only [CollatzResearch.WordTrace]
  refine ⟨123636564322301155472649287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82424376214867436981766191 123636564322301155472649287)
  ·
    refine ⟨185454846483451733208973931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123636564322301155472649287 185454846483451733208973931)
    ·
      refine ⟨278182269725177599813460897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185454846483451733208973931 278182269725177599813460897)
      ·
        refine ⟨208636702293883199860095673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278182269725177599813460897 208636702293883199860095673)
        ·
          refine ⟨156477526720412399895071755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208636702293883199860095673 156477526720412399895071755)
          ·
            refine ⟨234716290080618599842607633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156477526720412399895071755 234716290080618599842607633)
            ·
              refine ⟨176037217560463949881955725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234716290080618599842607633 176037217560463949881955725)
              ·
                refine ⟨66013956585173981205733397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176037217560463949881955725 66013956585173981205733397)
                ·
                  refine ⟨3094404214930030369018753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66013956585173981205733397 3094404214930030369018753)
                  ·
                    refine ⟨2320803161197522776764065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094404214930030369018753 2320803161197522776764065)
                    ·
                      refine ⟨1740602370898142082573049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320803161197522776764065 1740602370898142082573049)
                      ·
                        rfl

theorem cell23_3389811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 2, 2].length) (baseStart_3389811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389811 prefixEnd_3389811 := by exact prefixLift 3389811
  have htrace : WordTrace (prefixWord ++ tailWord_3389811) baseStart_3389811 baseEnd_3389811 := by
    simpa [prefixWord, tailWord_3389811, baseEnd_3389811] using wordTrace_append hprefix tailTrace_3389811
  have hstable : (prefixWord ++ tailWord_3389811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389811).length < 2 ^ (prefixWord ++ tailWord_3389811).sum := by decide
  have hdescent : baseEnd_3389811 < baseStart_3389811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389817 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 11]
def baseStart_3389817 : Nat := 118140960795 + 3389817 * 2 ^ 59
def prefixEnd_3389817 : Nat := 4983230072969 + 3 ^ 40 * 3389817 * 2
def baseEnd_3389817 : Nat := 193400605753563228788669

theorem tailTrace_3389817 : CollatzResearch.WordTrace tailWord_3389817 prefixEnd_3389817 193400605753563228788669 := by
  unfold tailWord_3389817
  simp only [CollatzResearch.WordTrace]
  refine ⟨123636783160279418497367705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82424522106852945664911803 123636783160279418497367705)
  ·
    refine ⟨92727587370209563873025779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123636783160279418497367705 92727587370209563873025779)
    ·
      refine ⟨139091381055314345809538669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92727587370209563873025779 139091381055314345809538669)
      ·
        refine ⟨52159267895742879678577001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139091381055314345809538669 52159267895742879678577001)
        ·
          refine ⟨39119450921807159758932751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52159267895742879678577001 39119450921807159758932751)
          ·
            refine ⟨58679176382710739638399127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39119450921807159758932751 58679176382710739638399127)
            ·
              refine ⟨88018764574066109457598691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58679176382710739638399127 88018764574066109457598691)
              ·
                refine ⟨132028146861099164186398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88018764574066109457598691 132028146861099164186398037)
                ·
                  refine ⟨193400605753563228788669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 132028146861099164186398037 193400605753563228788669)
                  ·
                    rfl

theorem cell23_3389817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 11].length) (baseStart_3389817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389817 prefixEnd_3389817 := by exact prefixLift 3389817
  have htrace : WordTrace (prefixWord ++ tailWord_3389817) baseStart_3389817 baseEnd_3389817 := by
    simpa [prefixWord, tailWord_3389817, baseEnd_3389817] using wordTrace_append hprefix tailTrace_3389817
  have hstable : (prefixWord ++ tailWord_3389817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389817).length < 2 ^ (prefixWord ++ tailWord_3389817).sum := by decide
  have hdescent : baseEnd_3389817 < baseStart_3389817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389828 : List Nat := [2, 3, 2, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_3389828 : Nat := 118140960795 + 3389828 * 2 ^ 59
def prefixEnd_3389828 : Nat := 4983230072969 + 3 ^ 40 * 3389828 * 2
def baseEnd_3389828 : Nat := 1740611100069268516060471

theorem tailTrace_3389828 : CollatzResearch.WordTrace tailWord_3389828 prefixEnd_3389828 1740611100069268516060471 := by
  unfold tailWord_3389828
  simp only [CollatzResearch.WordTrace]
  refine ⟨61818592181619783688009069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82424789575493044917345425 61818592181619783688009069)
  ·
    refine ⟨23181972068107418883003401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61818592181619783688009069 23181972068107418883003401)
    ·
      refine ⟨17386479051080564162252551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23181972068107418883003401 17386479051080564162252551)
      ·
        refine ⟨26079718576620846243378827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17386479051080564162252551 26079718576620846243378827)
        ·
          refine ⟨39119577864931269365068241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26079718576620846243378827 39119577864931269365068241)
          ·
            refine ⟨29339683398698452023801181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39119577864931269365068241 29339683398698452023801181)
            ·
              refine ⟨11002381274511919508925443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29339683398698452023801181 11002381274511919508925443)
              ·
                refine ⟨16503571911767879263388165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11002381274511919508925443 16503571911767879263388165)
                ·
                  refine ⟨3094419733456477361885281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16503571911767879263388165 3094419733456477361885281)
                  ·
                    refine ⟨2320814800092358021413961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094419733456477361885281 2320814800092358021413961)
                    ·
                      refine ⟨1740611100069268516060471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320814800092358021413961 1740611100069268516060471)
                      ·
                        rfl

theorem cell23_3389828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_3389828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389828 prefixEnd_3389828 := by exact prefixLift 3389828
  have htrace : WordTrace (prefixWord ++ tailWord_3389828) baseStart_3389828 baseEnd_3389828 := by
    simpa [prefixWord, tailWord_3389828, baseEnd_3389828] using wordTrace_append hprefix tailTrace_3389828
  have hstable : (prefixWord ++ tailWord_3389828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389828).length < 2 ^ (prefixWord ++ tailWord_3389828).sum := by decide
  have hdescent : baseEnd_3389828 < baseStart_3389828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389874 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3389874 : Nat := 118140960795 + 3389874 * 2 ^ 59
def prefixEnd_3389874 : Nat := 4983230072969 + 3 ^ 40 * 3389874 * 2
def baseEnd_3389874 : Nat := 1740634720179375336085259

theorem tailTrace_3389874 : CollatzResearch.WordTrace tailWord_3389874 prefixEnd_3389874 1740634720179375336085259 := by
  unfold tailWord_3389874
  simp only [CollatzResearch.WordTrace]
  refine ⟨30909715530268229308048169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82425908080715278154795117 30909715530268229308048169)
  ·
    refine ⟨23182286647701171981036127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30909715530268229308048169 23182286647701171981036127)
    ·
      refine ⟨34773429971551757971554191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23182286647701171981036127 34773429971551757971554191)
      ·
        refine ⟨52160144957327636957331287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34773429971551757971554191 52160144957327636957331287)
        ·
          refine ⟨78240217435991455435996931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52160144957327636957331287 78240217435991455435996931)
          ·
            refine ⟨117360326153987183153995397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78240217435991455435996931 117360326153987183153995397)
            ·
              refine ⟨22005061153872596841374137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117360326153987183153995397 22005061153872596841374137)
              ·
                refine ⟨16503795865404447631030603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22005061153872596841374137 16503795865404447631030603)
                ·
                  refine ⟨24755693798106671446545905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16503795865404447631030603 24755693798106671446545905)
                  ·
                    refine ⟨18566770348580003584909429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24755693798106671446545905 18566770348580003584909429)
                    ·
                      refine ⟨1740634720179375336085259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18566770348580003584909429 1740634720179375336085259)
                      ·
                        rfl

theorem cell23_3389874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3389874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389874 prefixEnd_3389874 := by exact prefixLift 3389874
  have htrace : WordTrace (prefixWord ++ tailWord_3389874) baseStart_3389874 baseEnd_3389874 := by
    simpa [prefixWord, tailWord_3389874, baseEnd_3389874] using wordTrace_append hprefix tailTrace_3389874
  have hstable : (prefixWord ++ tailWord_3389874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389874).length < 2 ^ (prefixWord ++ tailWord_3389874).sum := by decide
  have hdescent : baseEnd_3389874 < baseStart_3389874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389881 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 2, 5]
def baseStart_3389881 : Nat := 118140960795 + 3389881 * 2 ^ 59
def prefixEnd_3389881 : Nat := 4983230072969 + 3 ^ 40 * 3389881 * 2
def baseEnd_3389881 : Nat := 580212771514652269565909

theorem tailTrace_3389881 : CollatzResearch.WordTrace tailWord_3389881 prefixEnd_3389881 580212771514652269565909 := by
  unfold tailWord_3389881
  simp only [CollatzResearch.WordTrace]
  refine ⟨123639117432047557427697497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82426078288031704951798331 123639117432047557427697497)
  ·
    refine ⟨92729338074035668070773123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123639117432047557427697497 92729338074035668070773123)
    ·
      refine ⟨139094007111053502106159685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92729338074035668070773123 139094007111053502106159685)
      ·
        refine ⟨26080126333322531644904941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139094007111053502106159685 26080126333322531644904941)
        ·
          refine ⟨9780047374995949366839353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26080126333322531644904941 9780047374995949366839353)
          ·
            refine ⟨7335035531246962025129515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9780047374995949366839353 7335035531246962025129515)
            ·
              refine ⟨11002553296870443037694273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335035531246962025129515 11002553296870443037694273)
              ·
                refine ⟨8251914972652832278270705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11002553296870443037694273 8251914972652832278270705)
                ·
                  refine ⟨6188936229489624208703029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8251914972652832278270705 6188936229489624208703029)
                  ·
                    refine ⟨580212771514652269565909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6188936229489624208703029 580212771514652269565909)
                    ·
                      rfl

theorem cell23_3389881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 2, 5].length) (baseStart_3389881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389881 prefixEnd_3389881 := by exact prefixLift 3389881
  have htrace : WordTrace (prefixWord ++ tailWord_3389881) baseStart_3389881 baseEnd_3389881 := by
    simpa [prefixWord, tailWord_3389881, baseEnd_3389881] using wordTrace_append hprefix tailTrace_3389881
  have hstable : (prefixWord ++ tailWord_3389881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389881).length < 2 ^ (prefixWord ++ tailWord_3389881).sum := by decide
  have hdescent : baseEnd_3389881 < baseStart_3389881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389944 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_3389944 : Nat := 118140960795 + 3389944 * 2 ^ 59
def prefixEnd_3389944 : Nat := 4983230072969 + 3 ^ 40 * 3389944 * 2
def baseEnd_3389944 : Nat := 1740670663825190062209937

theorem tailTrace_3389944 : CollatzResearch.WordTrace tailWord_3389944 prefixEnd_3389944 1740670663825190062209937 := by
  unfold tailWord_3389944
  simp only [CollatzResearch.WordTrace]
  refine ⟨61820707615409659593620443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82427610153879546124827257 61820707615409659593620443)
  ·
    refine ⟨92731061423114489390430665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61820707615409659593620443 92731061423114489390430665)
    ·
      refine ⟨69548296067335867042822999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92731061423114489390430665 69548296067335867042822999)
      ·
        refine ⟨104322444101003800564234499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69548296067335867042822999 104322444101003800564234499)
        ·
          refine ⟨156483666151505700846351749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104322444101003800564234499 156483666151505700846351749)
          ·
            refine ⟨29340687403407318908690953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156483666151505700846351749 29340687403407318908690953)
            ·
              refine ⟨22005515552555489181518215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29340687403407318908690953 22005515552555489181518215)
              ·
                refine ⟨33008273328833233772277323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22005515552555489181518215 33008273328833233772277323)
                ·
                  refine ⟨49512409993249850658415985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33008273328833233772277323 49512409993249850658415985)
                  ·
                    refine ⟨37134307494937387993811989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49512409993249850658415985 37134307494937387993811989)
                    ·
                      refine ⟨1740670663825190062209937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37134307494937387993811989 1740670663825190062209937)
                      ·
                        rfl

theorem cell23_3389944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_3389944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389944 prefixEnd_3389944 := by exact prefixLift 3389944
  have htrace : WordTrace (prefixWord ++ tailWord_3389944) baseStart_3389944 baseEnd_3389944 := by
    simpa [prefixWord, tailWord_3389944, baseEnd_3389944] using wordTrace_append hprefix tailTrace_3389944
  have hstable : (prefixWord ++ tailWord_3389944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389944).length < 2 ^ (prefixWord ++ tailWord_3389944).sum := by decide
  have hdescent : baseEnd_3389944 < baseStart_3389944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389945 : List Nat := [1, 2, 1, 3, 1, 2, 6, 2, 1, 4]
def baseStart_3389945 : Nat := 118140960795 + 3389945 * 2 ^ 59
def prefixEnd_3389945 : Nat := 4983230072969 + 3 ^ 40 * 3389945 * 2
def baseEnd_3389945 : Nat := 580223725768614852765811

theorem tailTrace_3389945 : CollatzResearch.WordTrace tailWord_3389945 prefixEnd_3389945 580223725768614852765811 := by
  unfold tailWord_3389945
  simp only [CollatzResearch.WordTrace]
  refine ⟨123641451703815696358027289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82427634469210464238684859 123641451703815696358027289)
  ·
    refine ⟨92731088777861772268520467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123641451703815696358027289 92731088777861772268520467)
    ·
      refine ⟨139096633166792658402780701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92731088777861772268520467 139096633166792658402780701)
      ·
        refine ⟨52161237437547246901042763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139096633166792658402780701 52161237437547246901042763)
        ·
          refine ⟨78241856156320870351564145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52161237437547246901042763 78241856156320870351564145)
          ·
            refine ⟨58681392117240652763673109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78241856156320870351564145 58681392117240652763673109)
            ·
              refine ⟨2750690255495655598297177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58681392117240652763673109 2750690255495655598297177)
              ·
                refine ⟨2063017691621741698722883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2750690255495655598297177 2063017691621741698722883)
                ·
                  refine ⟨3094526537432612548084325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063017691621741698722883 3094526537432612548084325)
                  ·
                    refine ⟨580223725768614852765811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094526537432612548084325 580223725768614852765811)
                    ·
                      rfl

theorem cell23_3389945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 4].length) (baseStart_3389945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389945 prefixEnd_3389945 := by exact prefixLift 3389945
  have htrace : WordTrace (prefixWord ++ tailWord_3389945) baseStart_3389945 baseEnd_3389945 := by
    simpa [prefixWord, tailWord_3389945, baseEnd_3389945] using wordTrace_append hprefix tailTrace_3389945
  have hstable : (prefixWord ++ tailWord_3389945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389945).length < 2 ^ (prefixWord ++ tailWord_3389945).sum := by decide
  have hdescent : baseEnd_3389945 < baseStart_3389945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389971 : List Nat := [1, 1, 1, 2, 1, 5, 2, 4, 1, 5]
def baseStart_3389971 : Nat := 118140960795 + 3389971 * 2 ^ 59
def prefixEnd_3389971 : Nat := 4983230072969 + 3 ^ 40 * 3389971 * 2
def baseEnd_3389971 : Nat := 580228175934287152190771

theorem tailTrace_3389971 : CollatzResearch.WordTrace tailWord_3389971 prefixEnd_3389971 580228175934287152190771 := by
  unfold tailWord_3389971
  simp only [CollatzResearch.WordTrace]
  refine ⟨123642400001721502798473767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82428266667814335198982511 123642400001721502798473767)
  ·
    refine ⟨185463600002582254197710651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123642400001721502798473767 185463600002582254197710651)
    ·
      refine ⟨278195400003873381296565977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185463600002582254197710651 278195400003873381296565977)
      ·
        refine ⟨208646550002905035972424483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278195400003873381296565977 208646550002905035972424483)
        ·
          refine ⟨312969825004357553958636725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208646550002905035972424483 312969825004357553958636725)
          ·
            refine ⟨29340921094158520683622193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 312969825004357553958636725 29340921094158520683622193)
            ·
              refine ⟨22005690820618890512716645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29340921094158520683622193 22005690820618890512716645)
              ·
                refine ⟨4126067028866041971134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22005690820618890512716645 4126067028866041971134371)
                ·
                  refine ⟨6189100543299062956701557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126067028866041971134371 6189100543299062956701557)
                  ·
                    refine ⟨580228175934287152190771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6189100543299062956701557 580228175934287152190771)
                    ·
                      rfl

theorem cell23_3389971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 1, 5].length) (baseStart_3389971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389971 prefixEnd_3389971 := by exact prefixLift 3389971
  have htrace : WordTrace (prefixWord ++ tailWord_3389971) baseStart_3389971 baseEnd_3389971 := by
    simpa [prefixWord, tailWord_3389971, baseEnd_3389971] using wordTrace_append hprefix tailTrace_3389971
  have hstable : (prefixWord ++ tailWord_3389971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389971).length < 2 ^ (prefixWord ++ tailWord_3389971).sum := by decide
  have hdescent : baseEnd_3389971 < baseStart_3389971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3389972 : List Nat := [2, 4, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_3389972 : Nat := 118140960795 + 3389972 * 2 ^ 59
def prefixEnd_3389972 : Nat := 4983230072969 + 3 ^ 40 * 3389972 * 2
def baseEnd_3389972 : Nat := 1740685041283515952659809

theorem tailTrace_3389972 : CollatzResearch.WordTrace tailWord_3389972 prefixEnd_3389972 1740685041283515952659809 := by
  unfold tailWord_3389972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61821218237358939984630085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82428290983145253312840113 61821218237358939984630085)
  ·
    refine ⟨11591478419504801247118141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61821218237358939984630085 11591478419504801247118141)
    ·
      refine ⟨4346804407314300467669303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11591478419504801247118141 4346804407314300467669303)
      ·
        refine ⟨6520206610971450701503955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4346804407314300467669303 6520206610971450701503955)
        ·
          refine ⟨9780309916457176052255933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520206610971450701503955 9780309916457176052255933)
          ·
            refine ⟨3667616218671441019595975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9780309916457176052255933 3667616218671441019595975)
            ·
              refine ⟨5501424328007161529393963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667616218671441019595975 5501424328007161529393963)
              ·
                refine ⟨8252136492010742294090945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5501424328007161529393963 8252136492010742294090945)
                ·
                  refine ⟨6189102369008056720568209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8252136492010742294090945 6189102369008056720568209)
                  ·
                    refine ⟨4641826776756042540426157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6189102369008056720568209 4641826776756042540426157)
                    ·
                      refine ⟨1740685041283515952659809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4641826776756042540426157 1740685041283515952659809)
                      ·
                        rfl

theorem cell23_3389972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_3389972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3389972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3389972 prefixEnd_3389972 := by exact prefixLift 3389972
  have htrace : WordTrace (prefixWord ++ tailWord_3389972) baseStart_3389972 baseEnd_3389972 := by
    simpa [prefixWord, tailWord_3389972, baseEnd_3389972] using wordTrace_append hprefix tailTrace_3389972
  have hstable : (prefixWord ++ tailWord_3389972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3389972).length < 2 ^ (prefixWord ++ tailWord_3389972).sum := by decide
  have hdescent : baseEnd_3389972 < baseStart_3389972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3389972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390021 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_3390021 : Nat := 118140960795 + 3390021 * 2 ^ 59
def prefixEnd_3390021 : Nat := 4983230072969 + 3 ^ 40 * 3390021 * 2
def baseEnd_3390021 : Nat := 1740710201835586260947083

theorem tailTrace_3390021 : CollatzResearch.WordTrace tailWord_3390021 prefixEnd_3390021 1740710201835586260947083 := by
  unfold tailWord_3390021
  simp only [CollatzResearch.WordTrace]
  refine ⟨123644223651540361337793917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82429482434360240891862611 123644223651540361337793917)
  ·
    refine ⟨46366583869327635501672719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123644223651540361337793917 46366583869327635501672719)
    ·
      refine ⟨69549875803991453252509079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46366583869327635501672719 69549875803991453252509079)
      ·
        refine ⟨104324813705987179878763619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69549875803991453252509079 104324813705987179878763619)
        ·
          refine ⟨156487220558980769818145429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104324813705987179878763619 156487220558980769818145429)
          ·
            refine ⟨7335338463702223585225567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156487220558980769818145429 7335338463702223585225567)
            ·
              refine ⟨11003007695553335377838351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335338463702223585225567 11003007695553335377838351)
              ·
                refine ⟨16504511543330003066757527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003007695553335377838351 16504511543330003066757527)
                ·
                  refine ⟨24756767314995004600136291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16504511543330003066757527 24756767314995004600136291)
                  ·
                    refine ⟨37135150972492506900204437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24756767314995004600136291 37135150972492506900204437)
                    ·
                      refine ⟨1740710201835586260947083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37135150972492506900204437 1740710201835586260947083)
                      ·
                        rfl

theorem cell23_3390021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_3390021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390021 prefixEnd_3390021 := by exact prefixLift 3390021
  have htrace : WordTrace (prefixWord ++ tailWord_3390021) baseStart_3390021 baseEnd_3390021 := by
    simpa [prefixWord, tailWord_3390021, baseEnd_3390021] using wordTrace_append hprefix tailTrace_3390021
  have hstable : (prefixWord ++ tailWord_3390021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390021).length < 2 ^ (prefixWord ++ tailWord_3390021).sum := by decide
  have hdescent : baseEnd_3390021 < baseStart_3390021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390022 : List Nat := [6, 1, 1, 1, 2, 2, 2, 2, 1, 5]
def baseStart_3390022 : Nat := 118140960795 + 3390022 * 2 ^ 59
def prefixEnd_3390022 : Nat := 4983230072969 + 3 ^ 40 * 3390022 * 2
def baseEnd_3390022 : Nat := 580236905105413585678193

theorem tailTrace_3390022 : CollatzResearch.WordTrace tailWord_3390022 prefixEnd_3390022 580236905105413585678193 := by
  unfold tailWord_3390022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863883128891773078393135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82429506749691159005720213 3863883128891773078393135)
  ·
    refine ⟨5795824693337659617589703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863883128891773078393135 5795824693337659617589703)
    ·
      refine ⟨8693737040006489426384555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5795824693337659617589703 8693737040006489426384555)
      ·
        refine ⟨13040605560009734139576833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8693737040006489426384555 13040605560009734139576833)
        ·
          refine ⟨9780454170007300604682625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13040605560009734139576833 9780454170007300604682625)
          ·
            refine ⟨7335340627505475453511969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9780454170007300604682625 7335340627505475453511969)
            ·
              refine ⟨5501505470629106590133977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7335340627505475453511969 5501505470629106590133977)
              ·
                refine ⟨4126129102971829942600483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5501505470629106590133977 4126129102971829942600483)
                ·
                  refine ⟨6189193654457744913900725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126129102971829942600483 6189193654457744913900725)
                  ·
                    refine ⟨580236905105413585678193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6189193654457744913900725 580236905105413585678193)
                    ·
                      rfl

theorem cell23_3390022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_3390022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390022 prefixEnd_3390022 := by exact prefixLift 3390022
  have htrace : WordTrace (prefixWord ++ tailWord_3390022) baseStart_3390022 baseEnd_3390022 := by
    simpa [prefixWord, tailWord_3390022, baseEnd_3390022] using wordTrace_append hprefix tailTrace_3390022
  have hstable : (prefixWord ++ tailWord_3390022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390022).length < 2 ^ (prefixWord ++ tailWord_3390022).sum := by decide
  have hdescent : baseEnd_3390022 < baseStart_3390022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390031 : List Nat := [1, 1, 2, 1, 1, 2, 8, 7]
def baseStart_3390031 : Nat := 118140960795 + 3390031 * 2 ^ 59
def prefixEnd_3390031 : Nat := 4983230072969 + 3 ^ 40 * 3390031 * 2
def baseEnd_3390031 : Nat := 64470938394153008215631

theorem tailTrace_3390031 : CollatzResearch.WordTrace tailWord_3390031 prefixEnd_3390031 64470938394153008215631 := by
  unfold tailWord_3390031
  simp only [CollatzResearch.WordTrace]
  refine ⟨123644588381504133045657947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82429725587669422030438631 123644588381504133045657947)
  ·
    refine ⟨185466882572256199568486921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123644588381504133045657947 185466882572256199568486921)
    ·
      refine ⟨139100161929192149676365191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185466882572256199568486921 139100161929192149676365191)
      ·
        refine ⟨208650242893788224514547787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139100161929192149676365191 208650242893788224514547787)
        ·
          refine ⟨312975364340682336771821681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208650242893788224514547787 312975364340682336771821681)
          ·
            refine ⟨234731523255511752578866261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312975364340682336771821681 234731523255511752578866261)
            ·
              refine ⟨2750760038150528350533589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 234731523255511752578866261 2750760038150528350533589)
              ·
                refine ⟨64470938394153008215631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2750760038150528350533589 64470938394153008215631)
                ·
                  rfl

theorem cell23_3390031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 7].length) (baseStart_3390031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390031 prefixEnd_3390031 := by exact prefixLift 3390031
  have htrace : WordTrace (prefixWord ++ tailWord_3390031) baseStart_3390031 baseEnd_3390031 := by
    simpa [prefixWord, tailWord_3390031, baseEnd_3390031] using wordTrace_append hprefix tailTrace_3390031
  have hstable : (prefixWord ++ tailWord_3390031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390031).length < 2 ^ (prefixWord ++ tailWord_3390031).sum := by decide
  have hdescent : baseEnd_3390031 < baseStart_3390031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390046 : List Nat := [4, 4, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3390046 : Nat := 118140960795 + 3390046 * 2 ^ 59
def prefixEnd_3390046 : Nat := 4983230072969 + 3 ^ 40 * 3390046 * 2
def baseEnd_3390046 : Nat := 1740723038851948663134469

theorem tailTrace_3390046 : CollatzResearch.WordTrace tailWord_3390046 prefixEnd_3390046 1740723038851948663134469 := by
  unfold tailWord_3390046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15455641934556223825931749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82430090317633193738302661 15455641934556223825931749)
  ·
    refine ⟨2897932862729291967362203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15455641934556223825931749 2897932862729291967362203)
    ·
      refine ⟨4346899294093937951043305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2897932862729291967362203 4346899294093937951043305)
      ·
        refine ⟨3260174470570453463282479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4346899294093937951043305 3260174470570453463282479)
        ·
          refine ⟨4890261705855680194923719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260174470570453463282479 4890261705855680194923719)
          ·
            refine ⟨7335392558783520292385579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890261705855680194923719 7335392558783520292385579)
            ·
              refine ⟨11003088838175280438578369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335392558783520292385579 11003088838175280438578369)
              ·
                refine ⟨8252316628631460328933777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11003088838175280438578369 8252316628631460328933777)
                ·
                  refine ⟨6189237471473595246700333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8252316628631460328933777 6189237471473595246700333)
                  ·
                    refine ⟨2320964051802598217512625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6189237471473595246700333 2320964051802598217512625)
                    ·
                      refine ⟨1740723038851948663134469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320964051802598217512625 1740723038851948663134469)
                      ·
                        rfl

theorem cell23_3390046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3390046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390046 prefixEnd_3390046 := by exact prefixLift 3390046
  have htrace : WordTrace (prefixWord ++ tailWord_3390046) baseStart_3390046 baseEnd_3390046 := by
    simpa [prefixWord, tailWord_3390046, baseEnd_3390046] using wordTrace_append hprefix tailTrace_3390046
  have hstable : (prefixWord ++ tailWord_3390046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390046).length < 2 ^ (prefixWord ++ tailWord_3390046).sum := by decide
  have hdescent : baseEnd_3390046 < baseStart_3390046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390069 : List Nat := [1, 3, 4, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3390069 : Nat := 118140960795 + 3390069 * 2 ^ 59
def prefixEnd_3390069 : Nat := 4983230072969 + 3 ^ 40 * 3390069 * 2
def baseEnd_3390069 : Nat := 580244949635667357715621

theorem tailTrace_3390069 : CollatzResearch.WordTrace tailWord_3390069 prefixEnd_3390069 580244949635667357715621 := by
  unfold tailWord_3390069
  simp only [CollatzResearch.WordTrace]
  refine ⟨123645974355366465535541261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82430649570244310357027507 123645974355366465535541261)
  ·
    refine ⟨46367240383262424575827973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123645974355366465535541261 46367240383262424575827973)
    ·
      refine ⟨8693857571861704607967745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46367240383262424575827973 8693857571861704607967745)
      ·
        refine ⟨6520393178896278455975809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8693857571861704607967745 6520393178896278455975809)
        ·
          refine ⟨4890294884172208841981857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6520393178896278455975809 4890294884172208841981857)
          ·
            refine ⟨3667721163129156631486393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4890294884172208841981857 3667721163129156631486393)
            ·
              refine ⟨2750790872346867473614795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667721163129156631486393 2750790872346867473614795)
              ·
                refine ⟨4126186308520301210422193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750790872346867473614795 4126186308520301210422193)
                ·
                  refine ⟨3094639731390225907816645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4126186308520301210422193 3094639731390225907816645)
                  ·
                    refine ⟨580244949635667357715621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3094639731390225907816645 580244949635667357715621)
                    ·
                      rfl

theorem cell23_3390069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3390069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390069 prefixEnd_3390069 := by exact prefixLift 3390069
  have htrace : WordTrace (prefixWord ++ tailWord_3390069) baseStart_3390069 baseEnd_3390069 := by
    simpa [prefixWord, tailWord_3390069, baseEnd_3390069] using wordTrace_append hprefix tailTrace_3390069
  have hstable : (prefixWord ++ tailWord_3390069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390069).length < 2 ^ (prefixWord ++ tailWord_3390069).sum := by decide
  have hdescent : baseEnd_3390069 < baseStart_3390069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390085 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_3390085 : Nat := 118140960795 + 3390085 * 2 ^ 59
def prefixEnd_3390085 : Nat := 4983230072969 + 3 ^ 40 * 3390085 * 2
def baseEnd_3390085 : Nat := 1740743064597474010546789

theorem tailTrace_3390085 : CollatzResearch.WordTrace tailWord_3390085 prefixEnd_3390085 1740743064597474010546789 := by
  unfold tailWord_3390085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123646557923308500268123709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82431038615539000178749139 123646557923308500268123709)
  ·
    refine ⟨46367459221240687600546391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123646557923308500268123709 46367459221240687600546391)
    ·
      refine ⟨69551188831861031400819587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46367459221240687600546391 69551188831861031400819587)
      ·
        refine ⟨104326783247791547101229381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69551188831861031400819587 104326783247791547101229381)
        ·
          refine ⟨19561271858960915081480509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104326783247791547101229381 19561271858960915081480509)
          ·
            refine ⟨7335476947110343155555191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19561271858960915081480509 7335476947110343155555191)
            ·
              refine ⟨11003215420665514733332787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7335476947110343155555191 11003215420665514733332787)
              ·
                refine ⟨16504823130998272099999181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003215420665514733332787 16504823130998272099999181)
                ·
                  refine ⟨6189308674124352037499693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16504823130998272099999181 6189308674124352037499693)
                  ·
                    refine ⟨2320990752796632014062385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6189308674124352037499693 2320990752796632014062385)
                    ·
                      refine ⟨1740743064597474010546789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2320990752796632014062385 1740743064597474010546789)
                      ·
                        rfl

theorem cell23_3390085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_3390085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390085 prefixEnd_3390085 := by exact prefixLift 3390085
  have htrace : WordTrace (prefixWord ++ tailWord_3390085) baseStart_3390085 baseEnd_3390085 := by
    simpa [prefixWord, tailWord_3390085, baseEnd_3390085] using wordTrace_append hprefix tailTrace_3390085
  have hstable : (prefixWord ++ tailWord_3390085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390085).length < 2 ^ (prefixWord ++ tailWord_3390085).sum := by decide
  have hdescent : baseEnd_3390085 < baseStart_3390085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390171 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4]
def baseStart_3390171 : Nat := 118140960795 + 3390171 * 2 ^ 59
def prefixEnd_3390171 : Nat := 4983230072969 + 3 ^ 40 * 3390171 * 2
def baseEnd_3390171 : Nat := 1740787223933760674071393

theorem tailTrace_3390171 : CollatzResearch.WordTrace tailWord_3390171 prefixEnd_3390171 1740787223933760674071393 := by
  unfold tailWord_3390171
  simp only [CollatzResearch.WordTrace]
  refine ⟨123649694600996936955754367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82433129733997957970502911 123649694600996936955754367)
  ·
    refine ⟨185474541901495405433631551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123649694600996936955754367 185474541901495405433631551)
    ·
      refine ⟨278211812852243108150447327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185474541901495405433631551 278211812852243108150447327)
      ·
        refine ⟨417317719278364662225670991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278211812852243108150447327 417317719278364662225670991)
        ·
          refine ⟨625976578917546993338506487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417317719278364662225670991 625976578917546993338506487)
          ·
            refine ⟨938964868376320490007759731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625976578917546993338506487 938964868376320490007759731)
            ·
              refine ⟨1408447302564480735011639597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938964868376320490007759731 1408447302564480735011639597)
              ·
                refine ⟨528167738461680275629364849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1408447302564480735011639597 528167738461680275629364849)
                ·
                  refine ⟨396125803846260206722023637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528167738461680275629364849 396125803846260206722023637)
                  ·
                    refine ⟨9284198527646723595047429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 396125803846260206722023637 9284198527646723595047429)
                    ·
                      refine ⟨1740787223933760674071393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9284198527646723595047429 1740787223933760674071393)
                      ·
                        rfl

theorem cell23_3390171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7, 4].length) (baseStart_3390171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390171 prefixEnd_3390171 := by exact prefixLift 3390171
  have htrace : WordTrace (prefixWord ++ tailWord_3390171) baseStart_3390171 baseEnd_3390171 := by
    simpa [prefixWord, tailWord_3390171, baseEnd_3390171] using wordTrace_append hprefix tailTrace_3390171
  have hstable : (prefixWord ++ tailWord_3390171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390171).length < 2 ^ (prefixWord ++ tailWord_3390171).sum := by decide
  have hdescent : baseEnd_3390171 < baseStart_3390171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390172 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 5]
def baseStart_3390172 : Nat := 118140960795 + 3390172 * 2 ^ 59
def prefixEnd_3390172 : Nat := 4983230072969 + 3 ^ 40 * 3390172 * 2
def baseEnd_3390172 : Nat := 193420859712712796684321

theorem tailTrace_3390172 : CollatzResearch.WordTrace tailWord_3390172 prefixEnd_3390172 193420859712712796684321 := by
  unfold tailWord_3390172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61824865536996657063270385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82433154049328876084360513 61824865536996657063270385)
  ·
    refine ⟨46368649152747492797452789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61824865536996657063270385 46368649152747492797452789)
    ·
      refine ⟨4347060858070077449761199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46368649152747492797452789 4347060858070077449761199)
      ·
        refine ⟨6520591287105116174641799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4347060858070077449761199 6520591287105116174641799)
        ·
          refine ⟨9780886930657674261962699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520591287105116174641799 9780886930657674261962699)
          ·
            refine ⟨14671330395986511392944049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9780886930657674261962699 14671330395986511392944049)
            ·
              refine ⟨11003497796989883544708037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14671330395986511392944049 11003497796989883544708037)
              ·
                refine ⟨2063155836935603164632757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11003497796989883544708037 2063155836935603164632757)
                ·
                  refine ⟨193420859712712796684321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2063155836935603164632757 193420859712712796684321)
                  ·
                    rfl

theorem cell23_3390172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 5].length) (baseStart_3390172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390172 prefixEnd_3390172 := by exact prefixLift 3390172
  have htrace : WordTrace (prefixWord ++ tailWord_3390172) baseStart_3390172 baseEnd_3390172 := by
    simpa [prefixWord, tailWord_3390172, baseEnd_3390172] using wordTrace_append hprefix tailTrace_3390172
  have hstable : (prefixWord ++ tailWord_3390172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390172).length < 2 ^ (prefixWord ++ tailWord_3390172).sum := by decide
  have hdescent : baseEnd_3390172 < baseStart_3390172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390198 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_3390198 : Nat := 118140960795 + 3390198 * 2 ^ 59
def prefixEnd_3390198 : Nat := 4983230072969 + 3 ^ 40 * 3390198 * 2
def baseEnd_3390198 : Nat := 580267029303810689477923

theorem tailTrace_3390198 : CollatzResearch.WordTrace tailWord_3390198 prefixEnd_3390198 580267029303810689477923 := by
  unfold tailWord_3390198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728167460743695035436703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82433786247932747044658165 7728167460743695035436703)
  ·
    refine ⟨11592251191115542553155055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728167460743695035436703 11592251191115542553155055)
    ·
      refine ⟨17388376786673313829732583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592251191115542553155055 17388376786673313829732583)
      ·
        refine ⟨26082565180009970744598875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17388376786673313829732583 26082565180009970744598875)
        ·
          refine ⟨39123847770014956116898313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26082565180009970744598875 39123847770014956116898313)
          ·
            refine ⟨29342885827511217087673735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39123847770014956116898313 29342885827511217087673735)
            ·
              refine ⟨44014328741266825631510603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29342885827511217087673735 44014328741266825631510603)
              ·
                refine ⟨66021493111900238447265905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44014328741266825631510603 66021493111900238447265905)
                ·
                  refine ⟨49516119833925178835449429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66021493111900238447265905 49516119833925178835449429)
                  ·
                    refine ⟨580267029303810689477923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49516119833925178835449429 580267029303810689477923)
                    ·
                      rfl

theorem cell23_3390198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_3390198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390198 prefixEnd_3390198 := by exact prefixLift 3390198
  have htrace : WordTrace (prefixWord ++ tailWord_3390198) baseStart_3390198 baseEnd_3390198 := by
    simpa [prefixWord, tailWord_3390198, baseEnd_3390198] using wordTrace_append hprefix tailTrace_3390198
  have hstable : (prefixWord ++ tailWord_3390198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390198).length < 2 ^ (prefixWord ++ tailWord_3390198).sum := by decide
  have hdescent : baseEnd_3390198 < baseStart_3390198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390295 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3390295 : Nat := 118140960795 + 3390295 * 2 ^ 59
def prefixEnd_3390295 : Nat := 4983230072969 + 3 ^ 40 * 3390295 * 2
def baseEnd_3390295 : Nat := 1740850895534918188920823

theorem tailTrace_3390295 : CollatzResearch.WordTrace tailWord_3390295 prefixEnd_3390295 1740850895534918188920823 := by
  unfold tailWord_3390295
  simp only [CollatzResearch.WordTrace]
  refine ⟨123654217252547706133268339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82436144835031804088845559 123654217252547706133268339)
  ·
    refine ⟨185481325878821559199902509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123654217252547706133268339 185481325878821559199902509)
    ·
      refine ⟨69555497204558084699963441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185481325878821559199902509 69555497204558084699963441)
      ·
        refine ⟨52166622903418563524972581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69555497204558084699963441 52166622903418563524972581)
        ·
          refine ⟨9781241794390980660932359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52166622903418563524972581 9781241794390980660932359)
          ·
            refine ⟨14671862691586470991398539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781241794390980660932359 14671862691586470991398539)
            ·
              refine ⟨22007794037379706487097809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14671862691586470991398539 22007794037379706487097809)
              ·
                refine ⟨16505845528034779865323357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22007794037379706487097809 16505845528034779865323357)
                ·
                  refine ⟨6189692073013042449496259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16505845528034779865323357 6189692073013042449496259)
                  ·
                    refine ⟨9284538109519563674244389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6189692073013042449496259 9284538109519563674244389)
                    ·
                      refine ⟨1740850895534918188920823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9284538109519563674244389 1740850895534918188920823)
                      ·
                        rfl

theorem cell23_3390295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3390295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390295 prefixEnd_3390295 := by exact prefixLift 3390295
  have htrace : WordTrace (prefixWord ++ tailWord_3390295) baseStart_3390295 baseEnd_3390295 := by
    simpa [prefixWord, tailWord_3390295, baseEnd_3390295] using wordTrace_append hprefix tailTrace_3390295
  have hstable : (prefixWord ++ tailWord_3390295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390295).length < 2 ^ (prefixWord ++ tailWord_3390295).sum := by decide
  have hdescent : baseEnd_3390295 < baseStart_3390295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390315 : List Nat := [1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3]
def baseStart_3390315 : Nat := 118140960795 + 3390315 * 2 ^ 59
def prefixEnd_3390315 : Nat := 4983230072969 + 3 ^ 40 * 3390315 * 2
def baseEnd_3390315 : Nat := 1740861165148008110670731

theorem tailTrace_3390315 : CollatzResearch.WordTrace tailWord_3390315 prefixEnd_3390315 1740861165148008110670731 := by
  unfold tailWord_3390315
  simp only [CollatzResearch.WordTrace]
  refine ⟨123654946712475249548996399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82436631141650166365997599 123654946712475249548996399)
  ·
    refine ⟨185482420068712874323494599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123654946712475249548996399 185482420068712874323494599)
    ·
      refine ⟨278223630103069311485241899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185482420068712874323494599 278223630103069311485241899)
      ·
        refine ⟨417335445154603967227862849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278223630103069311485241899 417335445154603967227862849)
        ·
          refine ⟨313001583865952975420897137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417335445154603967227862849 313001583865952975420897137)
          ·
            refine ⟨234751187899464731565672853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313001583865952975420897137 234751187899464731565672853)
            ·
              refine ⟨11003961932787409292140915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234751187899464731565672853 11003961932787409292140915)
              ·
                refine ⟨16505942899181113938211373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11003961932787409292140915 16505942899181113938211373)
                ·
                  refine ⟨6189728587192917726829265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16505942899181113938211373 6189728587192917726829265)
                  ·
                    refine ⟨4642296440394688295121949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6189728587192917726829265 4642296440394688295121949)
                    ·
                      refine ⟨1740861165148008110670731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4642296440394688295121949 1740861165148008110670731)
                      ·
                        rfl

theorem cell23_3390315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 1, 3, 2, 3].length) (baseStart_3390315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390315 prefixEnd_3390315 := by exact prefixLift 3390315
  have htrace : WordTrace (prefixWord ++ tailWord_3390315) baseStart_3390315 baseEnd_3390315 := by
    simpa [prefixWord, tailWord_3390315, baseEnd_3390315] using wordTrace_append hprefix tailTrace_3390315
  have hstable : (prefixWord ++ tailWord_3390315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390315).length < 2 ^ (prefixWord ++ tailWord_3390315).sum := by decide
  have hdescent : baseEnd_3390315 < baseStart_3390315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390326 : List Nat := [5, 1, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_3390326 : Nat := 118140960795 + 3390326 * 2 ^ 59
def prefixEnd_3390326 : Nat := 4983230072969 + 3 ^ 40 * 3390326 * 2
def baseEnd_3390326 : Nat := 580288937811735855877727

theorem tailTrace_3390326 : CollatzResearch.WordTrace tailWord_3390326 prefixEnd_3390326 580288937811735855877727 := by
  unfold tailWord_3390326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728459244714712401727927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82436898610290265618431221 7728459244714712401727927)
  ·
    refine ⟨11592688867072068602591891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7728459244714712401727927 11592688867072068602591891)
    ·
      refine ⟨17389033300608102903887837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11592688867072068602591891 17389033300608102903887837)
      ·
        refine ⟨6520887487728038588957939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17389033300608102903887837 6520887487728038588957939)
        ·
          refine ⟨9781331231592057883436909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520887487728038588957939 9781331231592057883436909)
          ·
            refine ⟨3667999211847021706288841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9781331231592057883436909 3667999211847021706288841)
            ·
              refine ⟨2750999408885266279716631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3667999211847021706288841 2750999408885266279716631)
              ·
                refine ⟨4126499113327899419574947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2750999408885266279716631 4126499113327899419574947)
                ·
                  refine ⟨6189748669991849129362421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126499113327899419574947 6189748669991849129362421)
                  ·
                    refine ⟨580288937811735855877727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6189748669991849129362421 580288937811735855877727)
                    ·
                      rfl

theorem cell23_3390326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_3390326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390326 prefixEnd_3390326 := by exact prefixLift 3390326
  have htrace : WordTrace (prefixWord ++ tailWord_3390326) baseStart_3390326 baseEnd_3390326 := by
    simpa [prefixWord, tailWord_3390326, baseEnd_3390326] using wordTrace_append hprefix tailTrace_3390326
  have hstable : (prefixWord ++ tailWord_3390326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390326).length < 2 ^ (prefixWord ++ tailWord_3390326).sum := by decide
  have hdescent : baseEnd_3390326 < baseStart_3390326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390329 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 1, 1, 4]
def baseStart_3390329 : Nat := 118140960795 + 3390329 * 2 ^ 59
def prefixEnd_3390329 : Nat := 4983230072969 + 3 ^ 40 * 3390329 * 2
def baseEnd_3390329 : Nat := 1740868353877171055895667

theorem tailTrace_3390329 : CollatzResearch.WordTrace tailWord_3390329 prefixEnd_3390329 1740868353877171055895667 := by
  unfold tailWord_3390329
  simp only [CollatzResearch.WordTrace]
  refine ⟨123655457334424529940006041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82436971556283019960004027 123655457334424529940006041)
  ·
    refine ⟨92741593000818397455004531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123655457334424529940006041 92741593000818397455004531)
    ·
      refine ⟨139112389501227596182506797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92741593000818397455004531 139112389501227596182506797)
      ·
        refine ⟨52167146062960348568440049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139112389501227596182506797 52167146062960348568440049)
        ·
          refine ⟨39125359547220261426330037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52167146062960348568440049 39125359547220261426330037)
          ·
            refine ⟨3668002457551899508718441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39125359547220261426330037 3668002457551899508718441)
            ·
              refine ⟨2751001843163924631538831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668002457551899508718441 2751001843163924631538831)
              ·
                refine ⟨4126502764745886947308247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751001843163924631538831 4126502764745886947308247)
                ·
                  refine ⟨6189754147118830420962371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126502764745886947308247 6189754147118830420962371)
                  ·
                    refine ⟨9284631220678245631443557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6189754147118830420962371 9284631220678245631443557)
                    ·
                      refine ⟨1740868353877171055895667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9284631220678245631443557 1740868353877171055895667)
                      ·
                        rfl

theorem cell23_3390329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_3390329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390329 prefixEnd_3390329 := by exact prefixLift 3390329
  have htrace : WordTrace (prefixWord ++ tailWord_3390329) baseStart_3390329 baseEnd_3390329 := by
    simpa [prefixWord, tailWord_3390329, baseEnd_3390329] using wordTrace_append hprefix tailTrace_3390329
  have hstable : (prefixWord ++ tailWord_3390329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390329).length < 2 ^ (prefixWord ++ tailWord_3390329).sum := by decide
  have hdescent : baseEnd_3390329 < baseStart_3390329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390346 : List Nat := [3, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3390346 : Nat := 118140960795 + 3390346 * 2 ^ 59
def prefixEnd_3390346 : Nat := 4983230072969 + 3 ^ 40 * 3390346 * 2
def baseEnd_3390346 : Nat := 1740877083048297489383089

theorem tailTrace_3390346 : CollatzResearch.WordTrace tailWord_3390346 prefixEnd_3390346 1740877083048297489383089 := by
  unfold tailWord_3390346
  simp only [CollatzResearch.WordTrace]
  refine ⟨30914019343840735460843723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82437384916908627895583261 30914019343840735460843723)
  ·
    refine ⟨46371029015761103191265585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30914019343840735460843723 46371029015761103191265585)
    ·
      refine ⟨34778271761820827393449189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46371029015761103191265585 34778271761820827393449189)
      ·
        refine ⟨6520925955341405136271723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34778271761820827393449189 6520925955341405136271723)
        ·
          refine ⟨9781388933012107704407585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6520925955341405136271723 9781388933012107704407585)
          ·
            refine ⟨7336041699759080778305689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9781388933012107704407585 7336041699759080778305689)
            ·
              refine ⟨5502031274819310583729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7336041699759080778305689 5502031274819310583729267)
              ·
                refine ⟨8253046912228965875593901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502031274819310583729267 8253046912228965875593901)
                ·
                  refine ⟨3094892592085862203347713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8253046912228965875593901 3094892592085862203347713)
                  ·
                    refine ⟨2321169444064396652510785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3094892592085862203347713 2321169444064396652510785)
                    ·
                      refine ⟨1740877083048297489383089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321169444064396652510785 1740877083048297489383089)
                      ·
                        rfl

theorem cell23_3390346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3390346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390346 prefixEnd_3390346 := by exact prefixLift 3390346
  have htrace : WordTrace (prefixWord ++ tailWord_3390346) baseStart_3390346 baseEnd_3390346 := by
    simpa [prefixWord, tailWord_3390346, baseEnd_3390346] using wordTrace_append hprefix tailTrace_3390346
  have hstable : (prefixWord ++ tailWord_3390346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390346).length < 2 ^ (prefixWord ++ tailWord_3390346).sum := by decide
  have hdescent : baseEnd_3390346 < baseStart_3390346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390348 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 1, 9]
def baseStart_3390348 : Nat := 118140960795 + 3390348 * 2 ^ 59
def prefixEnd_3390348 : Nat := 4983230072969 + 3 ^ 40 * 3390348 * 2
def baseEnd_3390348 : Nat := 580292703336535493852693

theorem tailTrace_3390348 : CollatzResearch.WordTrace tailWord_3390348 prefixEnd_3390348 580292703336535493852693 := by
  unfold tailWord_3390348
  simp only [CollatzResearch.WordTrace]
  refine ⟨61828075160677848092473849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82437433547570464123298465 61828075160677848092473849)
  ·
    refine ⟨46371056370508386069355387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61828075160677848092473849 46371056370508386069355387)
    ·
      refine ⟨69556584555762579104033081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46371056370508386069355387 69556584555762579104033081)
      ·
        refine ⟨52167438416821934328024811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69556584555762579104033081 52167438416821934328024811)
        ·
          refine ⟨78251157625232901492037217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52167438416821934328024811 78251157625232901492037217)
          ·
            refine ⟨58688368218924676119027913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78251157625232901492037217 58688368218924676119027913)
            ·
              refine ⟨44016276164193507089270935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58688368218924676119027913 44016276164193507089270935)
              ·
                refine ⟨66024414246290260633906403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44016276164193507089270935 66024414246290260633906403)
                ·
                  refine ⟨99036621369435390950859605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66024414246290260633906403 99036621369435390950859605)
                  ·
                    refine ⟨580292703336535493852693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 99036621369435390950859605 580292703336535493852693)
                    ·
                      rfl

theorem cell23_3390348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_3390348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390348 prefixEnd_3390348 := by exact prefixLift 3390348
  have htrace : WordTrace (prefixWord ++ tailWord_3390348) baseStart_3390348 baseEnd_3390348 := by
    simpa [prefixWord, tailWord_3390348, baseEnd_3390348] using wordTrace_append hprefix tailTrace_3390348
  have hstable : (prefixWord ++ tailWord_3390348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390348).length < 2 ^ (prefixWord ++ tailWord_3390348).sum := by decide
  have hdescent : baseEnd_3390348 < baseStart_3390348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390355 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 2, 7, 2]
def baseStart_3390355 : Nat := 118140960795 + 3390355 * 2 ^ 59
def prefixEnd_3390355 : Nat := 4983230072969 + 3 ^ 40 * 3390355 * 2
def baseEnd_3390355 : Nat := 1740881704374187954170547

theorem tailTrace_3390355 : CollatzResearch.WordTrace tailWord_3390355 prefixEnd_3390355 1740881704374187954170547 := by
  unfold tailWord_3390355
  simp only [CollatzResearch.WordTrace]
  refine ⟨123656405632330336380452519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82437603754886890920301679 123656405632330336380452519)
  ·
    refine ⟨185484608448495504570678779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123656405632330336380452519 185484608448495504570678779)
    ·
      refine ⟨278226912672743256856018169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185484608448495504570678779 278226912672743256856018169)
      ·
        refine ⟨208670184504557442642013627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278226912672743256856018169 208670184504557442642013627)
        ·
          refine ⟨313005276756836163963020441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208670184504557442642013627 313005276756836163963020441)
          ·
            refine ⟨234753957567627122972265331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313005276756836163963020441 234753957567627122972265331)
            ·
              refine ⟨352130936351440684458397997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234753957567627122972265331 352130936351440684458397997)
              ·
                refine ⟨132049101131790256671899249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 352130936351440684458397997 132049101131790256671899249)
                ·
                  refine ⟨99036825848842692503924437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 132049101131790256671899249 99036825848842692503924437)
                  ·
                    refine ⟨2321175605832250605560729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 99036825848842692503924437 2321175605832250605560729)
                    ·
                      refine ⟨1740881704374187954170547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321175605832250605560729 1740881704374187954170547)
                      ·
                        rfl

theorem cell23_3390355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 7, 2].length) (baseStart_3390355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390355 prefixEnd_3390355 := by exact prefixLift 3390355
  have htrace : WordTrace (prefixWord ++ tailWord_3390355) baseStart_3390355 baseEnd_3390355 := by
    simpa [prefixWord, tailWord_3390355, baseEnd_3390355] using wordTrace_append hprefix tailTrace_3390355
  have hstable : (prefixWord ++ tailWord_3390355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390355).length < 2 ^ (prefixWord ++ tailWord_3390355).sum := by decide
  have hdescent : baseEnd_3390355 < baseStart_3390355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390389 : List Nat := [1, 3, 3, 2, 1, 1, 1, 5, 1, 3, 2]
def baseStart_3390389 : Nat := 118140960795 + 3390389 * 2 ^ 59
def prefixEnd_3390389 : Nat := 4983230072969 + 3 ^ 40 * 3390389 * 2
def baseEnd_3390389 : Nat := 1740899162716440821145391

theorem tailTrace_3390389 : CollatzResearch.WordTrace tailWord_3390389 prefixEnd_3390389 1740899162716440821145391 := by
  unfold tailWord_3390389
  simp only [CollatzResearch.WordTrace]
  refine ⟨123657645714207160187190221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82438430476138106791460147 123657645714207160187190221)
  ·
    refine ⟨46371617142827685070196333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123657645714207160187190221 46371617142827685070196333)
    ·
      refine ⟨17389356428560381901323625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46371617142827685070196333 17389356428560381901323625)
      ·
        refine ⟨13042017321420286425992719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17389356428560381901323625 13042017321420286425992719)
        ·
          refine ⟨19563025982130429638989079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13042017321420286425992719 19563025982130429638989079)
          ·
            refine ⟨29344538973195644458483619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19563025982130429638989079 29344538973195644458483619)
            ·
              refine ⟨44016808459793466687725429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29344538973195644458483619 44016808459793466687725429)
              ·
                refine ⟨4126575793105637501974259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44016808459793466687725429 4126575793105637501974259)
                ·
                  refine ⟨6189863689658456252961389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126575793105637501974259 6189863689658456252961389)
                  ·
                    refine ⟨2321198883621921094860521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6189863689658456252961389 2321198883621921094860521)
                    ·
                      refine ⟨1740899162716440821145391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321198883621921094860521 1740899162716440821145391)
                      ·
                        rfl

theorem cell23_3390389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_3390389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390389 prefixEnd_3390389 := by exact prefixLift 3390389
  have htrace : WordTrace (prefixWord ++ tailWord_3390389) baseStart_3390389 baseEnd_3390389 := by
    simpa [prefixWord, tailWord_3390389, baseEnd_3390389] using wordTrace_append hprefix tailTrace_3390389
  have hstable : (prefixWord ++ tailWord_3390389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390389).length < 2 ^ (prefixWord ++ tailWord_3390389).sum := by decide
  have hdescent : baseEnd_3390389 < baseStart_3390389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390466 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3390466 : Nat := 118140960795 + 3390466 * 2 ^ 59
def prefixEnd_3390466 : Nat := 4983230072969 + 3 ^ 40 * 3390466 * 2
def baseEnd_3390466 : Nat := 1740938700726837019882537

theorem tailTrace_3390466 : CollatzResearch.WordTrace tailWord_3390466 prefixEnd_3390466 1740938700726837019882537 := by
  unfold tailWord_3390466
  simp only [CollatzResearch.WordTrace]
  refine ⟨30915113533732050584435813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82440302756618801558495501 30915113533732050584435813)
  ·
    refine ⟨5796583787574759484581715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30915113533732050584435813 5796583787574759484581715)
    ·
      refine ⟨8694875681362139226872573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796583787574759484581715 8694875681362139226872573)
      ·
        refine ⟨3260578380510802210077215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8694875681362139226872573 3260578380510802210077215)
        ·
          refine ⟨4890867570766203315115823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3260578380510802210077215 4890867570766203315115823)
          ·
            refine ⟨7336301356149304972673735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4890867570766203315115823 7336301356149304972673735)
            ·
              refine ⟨11004452034223957459010603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7336301356149304972673735 11004452034223957459010603)
              ·
                refine ⟨16506678051335936188515905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11004452034223957459010603 16506678051335936188515905)
                ·
                  refine ⟨12380008538501952141386929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16506678051335936188515905 12380008538501952141386929)
                  ·
                    refine ⟨9285006403876464106040197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12380008538501952141386929 9285006403876464106040197)
                    ·
                      refine ⟨1740938700726837019882537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9285006403876464106040197 1740938700726837019882537)
                      ·
                        rfl

theorem cell23_3390466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3390466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390466 prefixEnd_3390466 := by exact prefixLift 3390466
  have htrace : WordTrace (prefixWord ++ tailWord_3390466) baseStart_3390466 baseEnd_3390466 := by
    simpa [prefixWord, tailWord_3390466, baseEnd_3390466] using wordTrace_append hprefix tailTrace_3390466
  have hstable : (prefixWord ++ tailWord_3390466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390466).length < 2 ^ (prefixWord ++ tailWord_3390466).sum := by decide
  have hdescent : baseEnd_3390466 < baseStart_3390466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390512 : List Nat := [2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3]
def baseStart_3390512 : Nat := 118140960795 + 3390512 * 2 ^ 59
def prefixEnd_3390512 : Nat := 4983230072969 + 3 ^ 40 * 3390512 * 2
def baseEnd_3390512 : Nat := 1740962320836943839907325

theorem tailTrace_3390512 : CollatzResearch.WordTrace tailWord_3390512 prefixEnd_3390512 1740962320836943839907325 := by
  unfold tailWord_3390512
  simp only [CollatzResearch.WordTrace]
  refine ⟨61831065946380776096958895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82441421261841034795945193 61831065946380776096958895)
  ·
    refine ⟨92746598919571164145438343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61831065946380776096958895 92746598919571164145438343)
    ·
      refine ⟨139119898379356746218157515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92746598919571164145438343 139119898379356746218157515)
      ·
        refine ⟨208679847569035119327236273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139119898379356746218157515 208679847569035119327236273)
        ·
          refine ⟨156509885676776339495427205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208679847569035119327236273 156509885676776339495427205)
          ·
            refine ⟨29345603564395563655392601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156509885676776339495427205 29345603564395563655392601)
            ·
              refine ⟨22009202673296672741544451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29345603564395563655392601 22009202673296672741544451)
              ·
                refine ⟨33013804009945009112316677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22009202673296672741544451 33013804009945009112316677)
                ·
                  refine ⟨6190088251864689208559377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33013804009945009112316677 6190088251864689208559377)
                  ·
                    refine ⟨4642566188898516906419533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6190088251864689208559377 4642566188898516906419533)
                    ·
                      refine ⟨1740962320836943839907325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4642566188898516906419533 1740962320836943839907325)
                      ·
                        rfl

theorem cell23_3390512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 3].length) (baseStart_3390512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390512 prefixEnd_3390512 := by exact prefixLift 3390512
  have htrace : WordTrace (prefixWord ++ tailWord_3390512) baseStart_3390512 baseEnd_3390512 := by
    simpa [prefixWord, tailWord_3390512, baseEnd_3390512] using wordTrace_append hprefix tailTrace_3390512
  have hstable : (prefixWord ++ tailWord_3390512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390512).length < 2 ^ (prefixWord ++ tailWord_3390512).sum := by decide
  have hdescent : baseEnd_3390512 < baseStart_3390512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390526 : List Nat := [4, 2, 1, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3390526 : Nat := 118140960795 + 3390526 * 2 ^ 59
def prefixEnd_3390526 : Nat := 4983230072969 + 3 ^ 40 * 3390526 * 2
def baseEnd_3390526 : Nat := 1740969509566106785132261

theorem tailTrace_3390526 : CollatzResearch.WordTrace tailWord_3390526 prefixEnd_3390526 1740969509566106785132261 := by
  unfold tailWord_3390526
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457830314338854073115929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82441761676473888389951621 15457830314338854073115929)
  ·
    refine ⟨11593372735754140554836947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15457830314338854073115929 11593372735754140554836947)
    ·
      refine ⟨17390059103631210832255421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11593372735754140554836947 17390059103631210832255421)
      ·
        refine ⟨6521272163861704062095783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17390059103631210832255421 6521272163861704062095783)
        ·
          refine ⟨9781908245792556093143675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6521272163861704062095783 9781908245792556093143675)
          ·
            refine ⟨14672862368688834139715513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9781908245792556093143675 14672862368688834139715513)
            ·
              refine ⟨11004646776516625604786635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14672862368688834139715513 11004646776516625604786635)
              ·
                refine ⟨16506970164774938407179953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11004646776516625604786635 16506970164774938407179953)
                ·
                  refine ⟨12380227623581203805384965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16506970164774938407179953 12380227623581203805384965)
                  ·
                    refine ⟨2321292679421475713509681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12380227623581203805384965 2321292679421475713509681)
                    ·
                      refine ⟨1740969509566106785132261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321292679421475713509681 1740969509566106785132261)
                      ·
                        rfl

theorem cell23_3390526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3390526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390526 prefixEnd_3390526 := by exact prefixLift 3390526
  have htrace : WordTrace (prefixWord ++ tailWord_3390526) baseStart_3390526 baseEnd_3390526 := by
    simpa [prefixWord, tailWord_3390526, baseEnd_3390526] using wordTrace_append hprefix tailTrace_3390526
  have hstable : (prefixWord ++ tailWord_3390526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390526).length < 2 ^ (prefixWord ++ tailWord_3390526).sum := by decide
  have hdescent : baseEnd_3390526 < baseStart_3390526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390542 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3390542 : Nat := 118140960795 + 3390542 * 2 ^ 59
def prefixEnd_3390542 : Nat := 4983230072969 + 3 ^ 40 * 3390542 * 2
def baseEnd_3390542 : Nat := 1740977725256578722532187

theorem tailTrace_3390542 : CollatzResearch.WordTrace tailWord_3390542 prefixEnd_3390542 1740977725256578722532187 := by
  unfold tailWord_3390542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15457903260331608414688735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82442150721768578211673253 15457903260331608414688735)
  ·
    refine ⟨23186854890497412622033103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15457903260331608414688735 23186854890497412622033103)
    ·
      refine ⟨34780282335746118933049655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23186854890497412622033103 34780282335746118933049655)
      ·
        refine ⟨52170423503619178399574483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34780282335746118933049655 52170423503619178399574483)
        ·
          refine ⟨78255635255428767599361725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52170423503619178399574483 78255635255428767599361725)
          ·
            refine ⟨29345863220785787849760647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78255635255428767599361725 29345863220785787849760647)
            ·
              refine ⟨44018794831178681774640971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29345863220785787849760647 44018794831178681774640971)
              ·
                refine ⟨66028192246768022661961457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44018794831178681774640971 66028192246768022661961457)
                ·
                  refine ⟨49521144185076016996471093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66028192246768022661961457 49521144185076016996471093)
                  ·
                    refine ⟨4642607267350876593419165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49521144185076016996471093 4642607267350876593419165)
                    ·
                      refine ⟨1740977725256578722532187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4642607267350876593419165 1740977725256578722532187)
                      ·
                        rfl

theorem cell23_3390542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3390542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390542 prefixEnd_3390542 := by exact prefixLift 3390542
  have htrace : WordTrace (prefixWord ++ tailWord_3390542) baseStart_3390542 baseEnd_3390542 := by
    simpa [prefixWord, tailWord_3390542, baseEnd_3390542] using wordTrace_append hprefix tailTrace_3390542
  have hstable : (prefixWord ++ tailWord_3390542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390542).length < 2 ^ (prefixWord ++ tailWord_3390542).sum := by decide
  have hdescent : baseEnd_3390542 < baseStart_3390542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390569 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 4, 3, 2]
def baseStart_3390569 : Nat := 118140960795 + 3390569 * 2 ^ 59
def prefixEnd_3390569 : Nat := 4983230072969 + 3 ^ 40 * 3390569 * 2
def baseEnd_3390569 : Nat := 1740991589234250116894563

theorem tailTrace_3390569 : CollatzResearch.WordTrace tailWord_3390569 prefixEnd_3390569 1740991589234250116894563 := by
  unfold tailWord_3390569
  simp only [CollatzResearch.WordTrace]
  refine ⟨123664210853555050928742761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82442807235703367285828507 123664210853555050928742761)
  ·
    refine ⟨92748158140166288196557071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123664210853555050928742761 92748158140166288196557071)
    ·
      refine ⟨139122237210249432294835607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92748158140166288196557071 139122237210249432294835607)
      ·
        refine ⟨208683355815374148442253411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139122237210249432294835607 208683355815374148442253411)
        ·
          refine ⟨313025033723061222663380117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208683355815374148442253411 313025033723061222663380117)
          ·
            refine ⟨14673048455768494812345943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 313025033723061222663380117 14673048455768494812345943)
            ·
              refine ⟨22009572683652742218518915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14673048455768494812345943 22009572683652742218518915)
              ·
                refine ⟨33014359025479113327778373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22009572683652742218518915 33014359025479113327778373)
                ·
                  refine ⟨6190192317277333748958445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33014359025479113327778373 6190192317277333748958445)
                  ·
                    refine ⟨2321322118979000155859417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6190192317277333748958445 2321322118979000155859417)
                    ·
                      refine ⟨1740991589234250116894563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321322118979000155859417 1740991589234250116894563)
                      ·
                        rfl

theorem cell23_3390569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 4, 3, 2].length) (baseStart_3390569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390569 prefixEnd_3390569 := by exact prefixLift 3390569
  have htrace : WordTrace (prefixWord ++ tailWord_3390569) baseStart_3390569 baseEnd_3390569 := by
    simpa [prefixWord, tailWord_3390569, baseEnd_3390569] using wordTrace_append hprefix tailTrace_3390569
  have hstable : (prefixWord ++ tailWord_3390569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390569).length < 2 ^ (prefixWord ++ tailWord_3390569).sum := by decide
  have hdescent : baseEnd_3390569 < baseStart_3390569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390596 : List Nat := [2, 3, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_3390596 : Nat := 118140960795 + 3390596 * 2 ^ 59
def prefixEnd_3390596 : Nat := 4983230072969 + 3 ^ 40 * 3390596 * 2
def baseEnd_3390596 : Nat := 580335151070640503752313

theorem tailTrace_3390596 : CollatzResearch.WordTrace tailWord_3390596 prefixEnd_3390596 580335151070640503752313 := by
  unfold tailWord_3390596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61832597812228617269987821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82443463749638156359983761 61832597812228617269987821)
  ·
    refine ⟨23187224179585731476245433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61832597812228617269987821 23187224179585731476245433)
    ·
      refine ⟨17390418134689298607184075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23187224179585731476245433 17390418134689298607184075)
      ·
        refine ⟨26085627202033947910776113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17390418134689298607184075 26085627202033947910776113)
        ·
          refine ⟨19564220401525460933082085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26085627202033947910776113 19564220401525460933082085)
          ·
            refine ⟨3668291325286023924952891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19564220401525460933082085 3668291325286023924952891)
            ·
              refine ⟨5502436987929035887429337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668291325286023924952891 5502436987929035887429337)
              ·
                refine ⟨4126827740946776915572003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5502436987929035887429337 4126827740946776915572003)
                ·
                  refine ⟨6190241611420165373358005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126827740946776915572003 6190241611420165373358005)
                  ·
                    refine ⟨580335151070640503752313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6190241611420165373358005 580335151070640503752313)
                    ·
                      rfl

theorem cell23_3390596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_3390596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390596 prefixEnd_3390596 := by exact prefixLift 3390596
  have htrace : WordTrace (prefixWord ++ tailWord_3390596) baseStart_3390596 baseEnd_3390596 := by
    simpa [prefixWord, tailWord_3390596, baseEnd_3390596] using wordTrace_append hprefix tailTrace_3390596
  have hstable : (prefixWord ++ tailWord_3390596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390596).length < 2 ^ (prefixWord ++ tailWord_3390596).sum := by decide
  have hdescent : baseEnd_3390596 < baseStart_3390596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390649 : List Nat := [1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 3]
def baseStart_3390649 : Nat := 118140960795 + 3390649 * 2 ^ 59
def prefixEnd_3390649 : Nat := 4983230072969 + 3 ^ 40 * 3390649 * 2
def baseEnd_3390649 : Nat := 1741032667686609803894195

theorem tailTrace_3390649 : CollatzResearch.WordTrace tailWord_3390649 prefixEnd_3390649 1741032667686609803894195 := by
  unfold tailWord_3390649
  simp only [CollatzResearch.WordTrace]
  refine ⟨123667128693265224591655001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82444752462176816394436667 123667128693265224591655001)
  ·
    refine ⟨92750346519948918443741251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123667128693265224591655001 92750346519948918443741251)
    ·
      refine ⟨139125519779923377665611877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92750346519948918443741251 139125519779923377665611877)
      ·
        refine ⟨26086034958735633312302227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139125519779923377665611877 26086034958735633312302227)
        ·
          refine ⟨39129052438103449968453341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26086034958735633312302227 39129052438103449968453341)
          ·
            refine ⟨14673394664288793738170003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39129052438103449968453341 14673394664288793738170003)
            ·
              refine ⟨22010091996433190607255005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14673394664288793738170003 22010091996433190607255005)
              ·
                refine ⟨8253784498662446477720627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22010091996433190607255005 8253784498662446477720627)
                ·
                  refine ⟨12380676747993669716580941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8253784498662446477720627 12380676747993669716580941)
                  ·
                    refine ⟨4642753780497626143717853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12380676747993669716580941 4642753780497626143717853)
                    ·
                      refine ⟨1741032667686609803894195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4642753780497626143717853 1741032667686609803894195)
                      ·
                        rfl

theorem cell23_3390649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_3390649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390649 prefixEnd_3390649 := by exact prefixLift 3390649
  have htrace : WordTrace (prefixWord ++ tailWord_3390649) baseStart_3390649 baseEnd_3390649 := by
    simpa [prefixWord, tailWord_3390649, baseEnd_3390649] using wordTrace_append hprefix tailTrace_3390649
  have hstable : (prefixWord ++ tailWord_3390649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390649).length < 2 ^ (prefixWord ++ tailWord_3390649).sum := by decide
  have hdescent : baseEnd_3390649 < baseStart_3390649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390670 : List Nat := [4, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_3390670 : Nat := 118140960795 + 3390670 * 2 ^ 59
def prefixEnd_3390670 : Nat := 4983230072969 + 3 ^ 40 * 3390670 * 2
def baseEnd_3390670 : Nat := 1741043450780354221731599

theorem tailTrace_3390670 : CollatzResearch.WordTrace tailWord_3390670 prefixEnd_3390670 1741043450780354221731599 := by
  unfold tailWord_3390670
  simp only [CollatzResearch.WordTrace]
  refine ⟨15458486828273643147271183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82445263084126096785446309 15458486828273643147271183)
  ·
    refine ⟨23187730242410464720906775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15458486828273643147271183 23187730242410464720906775)
    ·
      refine ⟨34781595363615697081360163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23187730242410464720906775 34781595363615697081360163)
      ·
        refine ⟨52172393045423545622040245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34781595363615697081360163 52172393045423545622040245)
        ·
          refine ⟨4891161848008457402066273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52172393045423545622040245 4891161848008457402066273)
          ·
            refine ⟨3668371386006343051549705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4891161848008457402066273 3668371386006343051549705)
            ·
              refine ⟨2751278539504757288662279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668371386006343051549705 2751278539504757288662279)
              ·
                refine ⟨4126917809257135932993419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751278539504757288662279 4126917809257135932993419)
                ·
                  refine ⟨6190376713885703899490129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4126917809257135932993419 6190376713885703899490129)
                  ·
                    refine ⟨4642782535414277924617597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6190376713885703899490129 4642782535414277924617597)
                    ·
                      refine ⟨1741043450780354221731599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4642782535414277924617597 1741043450780354221731599)
                      ·
                        rfl

theorem cell23_3390670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_3390670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390670 prefixEnd_3390670 := by exact prefixLift 3390670
  have htrace : WordTrace (prefixWord ++ tailWord_3390670) baseStart_3390670 baseEnd_3390670 := by
    simpa [prefixWord, tailWord_3390670, baseEnd_3390670] using wordTrace_append hprefix tailTrace_3390670
  have hstable : (prefixWord ++ tailWord_3390670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390670).length < 2 ^ (prefixWord ++ tailWord_3390670).sum := by decide
  have hdescent : baseEnd_3390670 < baseStart_3390670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390746 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 7]
def baseStart_3390746 : Nat := 118140960795 + 3390746 * 2 ^ 59
def prefixEnd_3390746 : Nat := 4983230072969 + 3 ^ 40 * 3390746 * 2
def baseEnd_3390746 : Nat := 193453608367788436042361

theorem tailTrace_3390746 : CollatzResearch.WordTrace tailWord_3390746 prefixEnd_3390746 193453608367788436042361 := by
  unfold tailWord_3390746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30917666643478452539484023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82447111049275873438624061 30917666643478452539484023)
  ·
    refine ⟨46376499965217678809226035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30917666643478452539484023 46376499965217678809226035)
    ·
      refine ⟨69564749947826518213839053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46376499965217678809226035 69564749947826518213839053)
      ·
        refine ⟨26086781230434944330189645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69564749947826518213839053 26086781230434944330189645)
        ·
          refine ⟨9782542961413104123821117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26086781230434944330189645 9782542961413104123821117)
          ·
            refine ⟨3668453610529914046432919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9782542961413104123821117 3668453610529914046432919)
            ·
              refine ⟨5502680415794871069649379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668453610529914046432919 5502680415794871069649379)
              ·
                refine ⟨8254020623692306604474069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5502680415794871069649379 8254020623692306604474069)
                ·
                  refine ⟨193453608367788436042361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8254020623692306604474069 193453608367788436042361)
                  ·
                    rfl

theorem cell23_3390746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_3390746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390746 prefixEnd_3390746 := by exact prefixLift 3390746
  have htrace : WordTrace (prefixWord ++ tailWord_3390746) baseStart_3390746 baseEnd_3390746 := by
    simpa [prefixWord, tailWord_3390746, baseEnd_3390746] using wordTrace_append hprefix tailTrace_3390746
  have hstable : (prefixWord ++ tailWord_3390746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390746).length < 2 ^ (prefixWord ++ tailWord_3390746).sum := by decide
  have hdescent : baseEnd_3390746 < baseStart_3390746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390757 : List Nat := [1, 3, 1, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_3390757 : Nat := 118140960795 + 3390757 * 2 ^ 59
def prefixEnd_3390757 : Nat := 4983230072969 + 3 ^ 40 * 3390757 * 2
def baseEnd_3390757 : Nat := 1741088123597295381343699

theorem tailTrace_3390757 : CollatzResearch.WordTrace tailWord_3390757 prefixEnd_3390757 1741088123597295381343699 := by
  unfold tailWord_3390757
  simp only [CollatzResearch.WordTrace]
  refine ⟨123671067776873959036586525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82447378517915972691057683 123671067776873959036586525)
  ·
    refine ⟨46376650416327734638719947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123671067776873959036586525 46376650416327734638719947)
    ·
      refine ⟨69564975624491601958079921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46376650416327734638719947 69564975624491601958079921)
      ·
        refine ⟨52173731718368701468559941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69564975624491601958079921 52173731718368701468559941)
        ·
          refine ⟨9782574697194131525354989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52173731718368701468559941 9782574697194131525354989)
          ·
            refine ⟨3668465511447799322008121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9782574697194131525354989 3668465511447799322008121)
            ·
              refine ⟨2751349133585849491506091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3668465511447799322008121 2751349133585849491506091)
              ·
                refine ⟨4127023700378774237259137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2751349133585849491506091 4127023700378774237259137)
                ·
                  refine ⟨3095267775284080677944353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127023700378774237259137 3095267775284080677944353)
                  ·
                    refine ⟨2321450831463060508458265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3095267775284080677944353 2321450831463060508458265)
                    ·
                      refine ⟨1741088123597295381343699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321450831463060508458265 1741088123597295381343699)
                      ·
                        rfl

theorem cell23_3390757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_3390757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390757 prefixEnd_3390757 := by exact prefixLift 3390757
  have htrace : WordTrace (prefixWord ++ tailWord_3390757) baseStart_3390757 baseEnd_3390757 := by
    simpa [prefixWord, tailWord_3390757, baseEnd_3390757] using wordTrace_append hprefix tailTrace_3390757
  have hstable : (prefixWord ++ tailWord_3390757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390757).length < 2 ^ (prefixWord ++ tailWord_3390757).sum := by decide
  have hdescent : baseEnd_3390757 < baseStart_3390757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390796 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3390796 : Nat := 118140960795 + 3390796 * 2 ^ 59
def prefixEnd_3390796 : Nat := 4983230072969 + 3 ^ 40 * 3390796 * 2
def baseEnd_3390796 : Nat := 1741108149342820728756019

theorem tailTrace_3390796 : CollatzResearch.WordTrace tailWord_3390796 prefixEnd_3390796 1741108149342820728756019 := by
  unfold tailWord_3390796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61836245111866334348628121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82448326815821779131504161 61836245111866334348628121)
  ·
    refine ⟨46377183833899750761471091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61836245111866334348628121 46377183833899750761471091)
    ·
      refine ⟨69565775750849626142206637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46377183833899750761471091 69565775750849626142206637)
      ·
        refine ⟨26087165906568609803327489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69565775750849626142206637 26087165906568609803327489)
        ·
          refine ⟨19565374429926457352495617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26087165906568609803327489 19565374429926457352495617)
          ·
            refine ⟨14674030822444843014371713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19565374429926457352495617 14674030822444843014371713)
            ·
              refine ⟨11005523116833632260778785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14674030822444843014371713 11005523116833632260778785)
              ·
                refine ⟨8254142337625224195584089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11005523116833632260778785 8254142337625224195584089)
                ·
                  refine ⟨6190606753218918146688067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8254142337625224195584089 6190606753218918146688067)
                  ·
                    refine ⟨9285910129828377220032101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6190606753218918146688067 9285910129828377220032101)
                    ·
                      refine ⟨1741108149342820728756019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9285910129828377220032101 1741108149342820728756019)
                      ·
                        rfl

theorem cell23_3390796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3390796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390796 prefixEnd_3390796 := by exact prefixLift 3390796
  have htrace : WordTrace (prefixWord ++ tailWord_3390796) baseStart_3390796 baseEnd_3390796 := by
    simpa [prefixWord, tailWord_3390796, baseEnd_3390796] using wordTrace_append hprefix tailTrace_3390796
  have hstable : (prefixWord ++ tailWord_3390796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390796).length < 2 ^ (prefixWord ++ tailWord_3390796).sum := by decide
  have hdescent : baseEnd_3390796 < baseStart_3390796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390823 : List Nat := [1, 1, 5, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3390823 : Nat := 118140960795 + 3390823 * 2 ^ 59
def prefixEnd_3390823 : Nat := 4983230072969 + 3 ^ 40 * 3390823 * 2
def baseEnd_3390823 : Nat := 580374004440164041039465

theorem tailTrace_3390823 : CollatzResearch.WordTrace tailWord_3390823 prefixEnd_3390823 580374004440164041039465 := by
  unfold tailWord_3390823
  simp only [CollatzResearch.WordTrace]
  refine ⟨123673474994634852308489123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82448983329756568205659415 123673474994634852308489123)
  ·
    refine ⟨185510212491952278462733685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123673474994634852308489123 185510212491952278462733685)
    ·
      refine ⟨17391582421120526105881283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185510212491952278462733685 17391582421120526105881283)
      ·
        refine ⟨26087373631680789158821925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17391582421120526105881283 26087373631680789158821925)
        ·
          refine ⟨4891382555940147967279111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26087373631680789158821925 4891382555940147967279111)
          ·
            refine ⟨7337073833910221950918667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891382555940147967279111 7337073833910221950918667)
            ·
              refine ⟨11005610750865332926378001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337073833910221950918667 11005610750865332926378001)
              ·
                refine ⟨8254208063148999694783501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11005610750865332926378001 8254208063148999694783501)
                ·
                  refine ⟨3095328023680874885543813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8254208063148999694783501 3095328023680874885543813)
                  ·
                    refine ⟨580374004440164041039465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3095328023680874885543813 580374004440164041039465)
                    ·
                      rfl

theorem cell23_3390823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3390823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390823 prefixEnd_3390823 := by exact prefixLift 3390823
  have htrace : WordTrace (prefixWord ++ tailWord_3390823) baseStart_3390823 baseEnd_3390823 := by
    simpa [prefixWord, tailWord_3390823, baseEnd_3390823] using wordTrace_append hprefix tailTrace_3390823
  have hstable : (prefixWord ++ tailWord_3390823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390823).length < 2 ^ (prefixWord ++ tailWord_3390823).sum := by decide
  have hdescent : baseEnd_3390823 < baseStart_3390823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390906 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_3390906 : Nat := 118140960795 + 3390906 * 2 ^ 59
def prefixEnd_3390906 : Nat := 4983230072969 + 3 ^ 40 * 3390906 * 2
def baseEnd_3390906 : Nat := 1741164632214815298380513

theorem tailTrace_3390906 : CollatzResearch.WordTrace tailWord_3390906 prefixEnd_3390906 1741164632214815298380513 := by
  unfold tailWord_3390906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919125563333539370940143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82451001502222771655840381 30919125563333539370940143)
  ·
    refine ⟨46378688345000309056410215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30919125563333539370940143 46378688345000309056410215)
    ·
      refine ⟨69568032517500463584615323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46378688345000309056410215 69568032517500463584615323)
      ·
        refine ⟨104352048776250695376922985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69568032517500463584615323 104352048776250695376922985)
        ·
          refine ⟨78264036582188021532692239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104352048776250695376922985 78264036582188021532692239)
          ·
            refine ⟨117396054873282032299038359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78264036582188021532692239 117396054873282032299038359)
            ·
              refine ⟨176094082309923048448557539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117396054873282032299038359 176094082309923048448557539)
              ·
                refine ⟨264141123464884572672836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176094082309923048448557539 264141123464884572672836309)
                ·
                  refine ⟨6190807581208232172019601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 264141123464884572672836309 6190807581208232172019601)
                  ·
                    refine ⟨4643105685906174129014701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6190807581208232172019601 4643105685906174129014701)
                    ·
                      refine ⟨1741164632214815298380513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643105685906174129014701 1741164632214815298380513)
                      ·
                        rfl

theorem cell23_3390906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_3390906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390906 prefixEnd_3390906 := by exact prefixLift 3390906
  have htrace : WordTrace (prefixWord ++ tailWord_3390906) baseStart_3390906 baseEnd_3390906 := by
    simpa [prefixWord, tailWord_3390906, baseEnd_3390906] using wordTrace_append hprefix tailTrace_3390906
  have hstable : (prefixWord ++ tailWord_3390906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390906).length < 2 ^ (prefixWord ++ tailWord_3390906).sum := by decide
  have hdescent : baseEnd_3390906 < baseStart_3390906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390957 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3390957 : Nat := 118140960795 + 3390957 * 2 ^ 59
def prefixEnd_3390957 : Nat := 4983230072969 + 3 ^ 40 * 3390957 * 2
def baseEnd_3390957 : Nat := 1741190819728194598842779

theorem tailTrace_3390957 : CollatzResearch.WordTrace tailWord_3390957 prefixEnd_3390957 1741190819728194598842779 := by
  unfold tailWord_3390957
  simp only [CollatzResearch.WordTrace]
  refine ⟨123678362376149393193867125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82452241584099595462578083 123678362376149393193867125)
  ·
    refine ⟨11594846472764005611925043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123678362376149393193867125 11594846472764005611925043)
    ·
      refine ⟨17392269709146008417887565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11594846472764005611925043 17392269709146008417887565)
      ·
        refine ⟨6522101140929753156707837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17392269709146008417887565 6522101140929753156707837)
        ·
          refine ⟨2445787927848657433765439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6522101140929753156707837 2445787927848657433765439)
          ·
            refine ⟨3668681891772986150648159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445787927848657433765439 3668681891772986150648159)
            ·
              refine ⟨5503022837659479225972239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3668681891772986150648159 5503022837659479225972239)
              ·
                refine ⟨8254534256489218838958359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503022837659479225972239 8254534256489218838958359)
                ·
                  refine ⟨12381801384733828258437539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254534256489218838958359 12381801384733828258437539)
                  ·
                    refine ⟨18572702077100742387656309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12381801384733828258437539 18572702077100742387656309)
                    ·
                      refine ⟨1741190819728194598842779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18572702077100742387656309 1741190819728194598842779)
                      ·
                        rfl

theorem cell23_3390957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3390957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390957 prefixEnd_3390957 := by exact prefixLift 3390957
  have htrace : WordTrace (prefixWord ++ tailWord_3390957) baseStart_3390957 baseEnd_3390957 := by
    simpa [prefixWord, tailWord_3390957, baseEnd_3390957] using wordTrace_append hprefix tailTrace_3390957
  have hstable : (prefixWord ++ tailWord_3390957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390957).length < 2 ^ (prefixWord ++ tailWord_3390957).sum := by decide
  have hdescent : baseEnd_3390957 < baseStart_3390957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390970 : List Nat := [3, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_3390970 : Nat := 118140960795 + 3390970 * 2 ^ 59
def prefixEnd_3390970 : Nat := 4983230072969 + 3 ^ 40 * 3390970 * 2
def baseEnd_3390970 : Nat := 1741197494976703047980219

theorem tailTrace_3390970 : CollatzResearch.WordTrace tailWord_3390970 prefixEnd_3390970 1741197494976703047980219 := by
  unfold tailWord_3390970
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919709131275574103522591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82452557683401530942726909 30919709131275574103522591)
  ·
    refine ⟨46379563696913361155283887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30919709131275574103522591 46379563696913361155283887)
    ·
      refine ⟨69569345545370041732925831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46379563696913361155283887 69569345545370041732925831)
      ·
        refine ⟨104354018318055062599388747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69569345545370041732925831 104354018318055062599388747)
        ·
          refine ⟨156531027477082593899083121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104354018318055062599388747 156531027477082593899083121)
          ·
            refine ⟨117398270607811945424312341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156531027477082593899083121 117398270607811945424312341)
            ·
              refine ⟨5503043934741184941764641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117398270607811945424312341 5503043934741184941764641)
              ·
                refine ⟨4127282951055888706323481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503043934741184941764641 4127282951055888706323481)
                ·
                  refine ⟨3095462213291916529742611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127282951055888706323481 3095462213291916529742611)
                  ·
                    refine ⟨4643193319937874794613917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3095462213291916529742611 4643193319937874794613917)
                    ·
                      refine ⟨1741197494976703047980219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643193319937874794613917 1741197494976703047980219)
                      ·
                        rfl

theorem cell23_3390970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_3390970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390970 prefixEnd_3390970 := by exact prefixLift 3390970
  have htrace : WordTrace (prefixWord ++ tailWord_3390970) baseStart_3390970 baseEnd_3390970 := by
    simpa [prefixWord, tailWord_3390970, baseEnd_3390970] using wordTrace_append hprefix tailTrace_3390970
  have hstable : (prefixWord ++ tailWord_3390970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390970).length < 2 ^ (prefixWord ++ tailWord_3390970).sum := by decide
  have hdescent : baseEnd_3390970 < baseStart_3390970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3390986 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_3390986 : Nat := 118140960795 + 3390986 * 2 ^ 59
def prefixEnd_3390986 : Nat := 4983230072969 + 3 ^ 40 * 3390986 * 2
def baseEnd_3390986 : Nat := 580401903555724995126715

theorem tailTrace_3390986 : CollatzResearch.WordTrace tailWord_3390986 prefixEnd_3390986 580401903555724995126715 := by
  unfold tailWord_3390986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30919855023261082786668203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82452946728696220764448541 30919855023261082786668203)
  ·
    refine ⟨46379782534891624180002305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30919855023261082786668203 46379782534891624180002305)
    ·
      refine ⟨34784836901168718135001729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46379782534891624180002305 34784836901168718135001729)
      ·
        refine ⟨26088627675876538601251297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34784836901168718135001729 26088627675876538601251297)
        ·
          refine ⟨19566470756907403950938473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26088627675876538601251297 19566470756907403950938473)
          ·
            refine ⟨14674853067680552963203855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19566470756907403950938473 14674853067680552963203855)
            ·
              refine ⟨22012279601520829444805783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14674853067680552963203855 22012279601520829444805783)
              ·
                refine ⟨33018419402281244167208675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22012279601520829444805783 33018419402281244167208675)
                ·
                  refine ⟨49527629103421866250813013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33018419402281244167208675 49527629103421866250813013)
                  ·
                    refine ⟨580401903555724995126715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49527629103421866250813013 580401903555724995126715)
                    ·
                      rfl

theorem cell23_3390986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_3390986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3390986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3390986 prefixEnd_3390986 := by exact prefixLift 3390986
  have htrace : WordTrace (prefixWord ++ tailWord_3390986) baseStart_3390986 baseEnd_3390986 := by
    simpa [prefixWord, tailWord_3390986, baseEnd_3390986] using wordTrace_append hprefix tailTrace_3390986
  have hstable : (prefixWord ++ tailWord_3390986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3390986).length < 2 ^ (prefixWord ++ tailWord_3390986).sum := by decide
  have hdescent : baseEnd_3390986 < baseStart_3390986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3390986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391010 : List Nat := [3, 3, 1, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_3391010 : Nat := 118140960795 + 3391010 * 2 ^ 59
def prefixEnd_3391010 : Nat := 4983230072969 + 3 ^ 40 * 3391010 * 2
def baseEnd_3391010 : Nat := 1741218034202882891480035

theorem tailTrace_3391010 : CollatzResearch.WordTrace tailWord_3391010 prefixEnd_3391010 1741218034202882891480035 := by
  unfold tailWord_3391010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30920073861239345811386621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82453530296638255497030989 30920073861239345811386621)
  ·
    refine ⟨11595027697964754679269983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30920073861239345811386621 11595027697964754679269983)
    ·
      refine ⟨17392541546947132018904975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11595027697964754679269983 17392541546947132018904975)
      ·
        refine ⟨26088812320420698028357463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17392541546947132018904975 26088812320420698028357463)
        ·
          refine ⟨39133218480631047042536195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26088812320420698028357463 39133218480631047042536195)
          ·
            refine ⟨58699827720946570563804293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39133218480631047042536195 58699827720946570563804293)
            ·
              refine ⟨11006217697677481980713305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58699827720946570563804293 11006217697677481980713305)
              ·
                refine ⟨8254663273258111485534979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006217697677481980713305 8254663273258111485534979)
                ·
                  refine ⟨12381994909887167228302469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8254663273258111485534979 12381994909887167228302469)
                  ·
                    refine ⟨2321624045603843855306713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12381994909887167228302469 2321624045603843855306713)
                    ·
                      refine ⟨1741218034202882891480035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321624045603843855306713 1741218034202882891480035)
                      ·
                        rfl

theorem cell23_3391010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_3391010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391010 prefixEnd_3391010 := by exact prefixLift 3391010
  have htrace : WordTrace (prefixWord ++ tailWord_3391010) baseStart_3391010 baseEnd_3391010 := by
    simpa [prefixWord, tailWord_3391010, baseEnd_3391010] using wordTrace_append hprefix tailTrace_3391010
  have hstable : (prefixWord ++ tailWord_3391010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391010).length < 2 ^ (prefixWord ++ tailWord_3391010).sum := by decide
  have hdescent : baseEnd_3391010 < baseStart_3391010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391027 : List Nat := [1, 1, 1, 2, 4, 3, 3, 2, 2, 2, 2]
def baseStart_3391027 : Nat := 118140960795 + 3391027 * 2 ^ 59
def prefixEnd_3391027 : Nat := 4983230072969 + 3 ^ 40 * 3391027 * 2
def baseEnd_3391027 : Nat := 1741226763374009324967457

theorem tailTrace_3391027 : CollatzResearch.WordTrace tailWord_3391027 prefixEnd_3391027 1741226763374009324967457 := by
  unfold tailWord_3391027
  simp only [CollatzResearch.WordTrace]
  refine ⟨123680915485895795148915335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82453943657263863432610223 123680915485895795148915335)
  ·
    refine ⟨185521373228843692723373003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123680915485895795148915335 185521373228843692723373003)
    ·
      refine ⟨278282059843265539085059505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185521373228843692723373003 278282059843265539085059505)
      ·
        refine ⟨208711544882449154313794629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278282059843265539085059505 208711544882449154313794629)
        ·
          refine ⟨39133414665459216433836493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208711544882449154313794629 39133414665459216433836493)
          ·
            refine ⟨14675030499547206162688685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39133414665459216433836493 14675030499547206162688685)
            ·
              refine ⟨5503136437330202311008257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14675030499547206162688685 5503136437330202311008257)
              ·
                refine ⟨4127352327997651733256193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503136437330202311008257 4127352327997651733256193)
                ·
                  refine ⟨3095514245998238799942145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4127352327997651733256193 3095514245998238799942145)
                  ·
                    refine ⟨2321635684498679099956609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3095514245998238799942145 2321635684498679099956609)
                    ·
                      refine ⟨1741226763374009324967457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321635684498679099956609 1741226763374009324967457)
                      ·
                        rfl

theorem cell23_3391027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 2, 2, 2, 2].length) (baseStart_3391027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391027 prefixEnd_3391027 := by exact prefixLift 3391027
  have htrace : WordTrace (prefixWord ++ tailWord_3391027) baseStart_3391027 baseEnd_3391027 := by
    simpa [prefixWord, tailWord_3391027, baseEnd_3391027] using wordTrace_append hprefix tailTrace_3391027
  have hstable : (prefixWord ++ tailWord_3391027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391027).length < 2 ^ (prefixWord ++ tailWord_3391027).sum := by decide
  have hdescent : baseEnd_3391027 < baseStart_3391027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391033 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 7]
def baseStart_3391033 : Nat := 118140960795 + 3391033 * 2 ^ 59
def prefixEnd_3391033 : Nat := 4983230072969 + 3 ^ 40 * 3391033 * 2
def baseEnd_3391033 : Nat := 193469982695326255721381

theorem tailTrace_3391033 : CollatzResearch.WordTrace tailWord_3391033 prefixEnd_3391033 193469982695326255721381 := by
  unfold tailWord_3391033
  simp only [CollatzResearch.WordTrace]
  refine ⟨123681134323874058173633753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82454089549249372115755835 123681134323874058173633753)
  ·
    refine ⟨92760850742905543630225315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123681134323874058173633753 92760850742905543630225315)
    ·
      refine ⟨139141276114358315445337973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92760850742905543630225315 139141276114358315445337973)
      ·
        refine ⟨13044494635721092073000435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 139141276114358315445337973 13044494635721092073000435)
        ·
          refine ⟨19566741953581638109500653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13044494635721092073000435 19566741953581638109500653)
          ·
            refine ⟨7337528232593114291062745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19566741953581638109500653 7337528232593114291062745)
            ·
              refine ⟨5503146174444835718297059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337528232593114291062745 5503146174444835718297059)
              ·
                refine ⟨8254719261667253577445589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503146174444835718297059 8254719261667253577445589)
                ·
                  refine ⟨193469982695326255721381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8254719261667253577445589 193469982695326255721381)
                  ·
                    rfl

theorem cell23_3391033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_3391033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391033 prefixEnd_3391033 := by exact prefixLift 3391033
  have htrace : WordTrace (prefixWord ++ tailWord_3391033) baseStart_3391033 baseEnd_3391033 := by
    simpa [prefixWord, tailWord_3391033, baseEnd_3391033] using wordTrace_append hprefix tailTrace_3391033
  have hstable : (prefixWord ++ tailWord_3391033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391033).length < 2 ^ (prefixWord ++ tailWord_3391033).sum := by decide
  have hdescent : baseEnd_3391033 < baseStart_3391033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391080 : List Nat := [2, 1, 4, 3, 1, 2, 1, 2, 2, 5]
def baseStart_3391080 : Nat := 118140960795 + 3391080 * 2 ^ 59
def prefixEnd_3391080 : Nat := 4983230072969 + 3 ^ 40 * 3391080 * 2
def baseEnd_3391080 : Nat := 580417992616232539201571

theorem tailTrace_3391080 : CollatzResearch.WordTrace tailWord_3391080 prefixEnd_3391080 580417992616232539201571 := by
  unfold tailWord_3391080
  simp only [CollatzResearch.WordTrace]
  refine ⟨61841424277351892600297347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82455232369802523467063129 61841424277351892600297347)
  ·
    refine ⟨92762136416027838900446021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61841424277351892600297347 92762136416027838900446021)
    ·
      refine ⟨17392900578005219793833629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92762136416027838900446021 17392900578005219793833629)
      ·
        refine ⟨6522337716751957422687611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17392900578005219793833629 6522337716751957422687611)
        ·
          refine ⟨9783506575127936134031417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6522337716751957422687611 9783506575127936134031417)
          ·
            refine ⟨7337629931345952100523563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9783506575127936134031417 7337629931345952100523563)
            ·
              refine ⟨11006444897018928150785345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337629931345952100523563 11006444897018928150785345)
              ·
                refine ⟨8254833672764196113089009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006444897018928150785345 8254833672764196113089009)
                ·
                  refine ⟨6191125254573147084816757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8254833672764196113089009 6191125254573147084816757)
                  ·
                    refine ⟨580417992616232539201571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6191125254573147084816757 580417992616232539201571)
                    ·
                      rfl

theorem cell23_3391080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_3391080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391080 prefixEnd_3391080 := by exact prefixLift 3391080
  have htrace : WordTrace (prefixWord ++ tailWord_3391080) baseStart_3391080 baseEnd_3391080 := by
    simpa [prefixWord, tailWord_3391080, baseEnd_3391080] using wordTrace_append hprefix tailTrace_3391080
  have hstable : (prefixWord ++ tailWord_3391080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391080).length < 2 ^ (prefixWord ++ tailWord_3391080).sum := by decide
  have hdescent : baseEnd_3391080 < baseStart_3391080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391140 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 6]
def baseStart_3391140 : Nat := 118140960795 + 3391140 * 2 ^ 59
def prefixEnd_3391140 : Nat := 4983230072969 + 3 ^ 40 * 3391140 * 2
def baseEnd_3391140 : Nat := 193476087409774153650493

theorem tailTrace_3391140 : CollatzResearch.WordTrace tailWord_3391140 prefixEnd_3391140 193476087409774153650493 := by
  unfold tailWord_3391140
  simp only [CollatzResearch.WordTrace]
  refine ⟨61842518467243207723889437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82456691289657610298519249 61842518467243207723889437)
  ·
    refine ⟨23190944425216202896458539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61842518467243207723889437 23190944425216202896458539)
    ·
      refine ⟨34786416637824304344687809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23190944425216202896458539 34786416637824304344687809)
      ·
        refine ⟨26089812478368228258515857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34786416637824304344687809 26089812478368228258515857)
        ·
          refine ⟨19567359358776171193886893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26089812478368228258515857 19567359358776171193886893)
          ·
            refine ⟨7337759759541064197707585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19567359358776171193886893 7337759759541064197707585)
            ·
              refine ⟨5503319819655798148280689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7337759759541064197707585 5503319819655798148280689)
              ·
                refine ⟨4127489864741848611210517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503319819655798148280689 4127489864741848611210517)
                ·
                  refine ⟨193476087409774153650493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4127489864741848611210517 193476087409774153650493)
                  ·
                    rfl

theorem cell23_3391140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_3391140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391140 prefixEnd_3391140 := by exact prefixLift 3391140
  have htrace : WordTrace (prefixWord ++ tailWord_3391140) baseStart_3391140 baseEnd_3391140 := by
    simpa [prefixWord, tailWord_3391140, baseEnd_3391140] using wordTrace_append hprefix tailTrace_3391140
  have hstable : (prefixWord ++ tailWord_3391140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391140).length < 2 ^ (prefixWord ++ tailWord_3391140).sum := by decide
  have hdescent : baseEnd_3391140 < baseStart_3391140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391160 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2]
def baseStart_3391160 : Nat := 118140960795 + 3391160 * 2 ^ 59
def prefixEnd_3391160 : Nat := 4983230072969 + 3 ^ 40 * 3391160 * 2
def baseEnd_3391160 : Nat := 1741295056301057304604345

theorem tailTrace_3391160 : CollatzResearch.WordTrace tailWord_3391160 prefixEnd_3391160 1741295056301057304604345 := by
  unfold tailWord_3391160
  simp only [CollatzResearch.WordTrace]
  refine ⟨61842883197206979431753467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82457177596275972575671289 61842883197206979431753467)
  ·
    refine ⟨92764324795810469147630201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61842883197206979431753467 92764324795810469147630201)
    ·
      refine ⟨69573243596857851860722651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92764324795810469147630201 69573243596857851860722651)
      ·
        refine ⟨104359865395286777791083977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69573243596857851860722651 104359865395286777791083977)
        ·
          refine ⟨78269899046465083343312983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104359865395286777791083977 78269899046465083343312983)
          ·
            refine ⟨117404848569697625014969475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78269899046465083343312983 117404848569697625014969475)
            ·
              refine ⟨176107272854546437522454213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117404848569697625014969475 176107272854546437522454213)
              ·
                refine ⟨33020113660227457035460165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 176107272854546437522454213 33020113660227457035460165)
                ·
                  refine ⟨6191271311292648194148781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33020113660227457035460165 6191271311292648194148781)
                  ·
                    refine ⟨2321726741734743072805793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6191271311292648194148781 2321726741734743072805793)
                    ·
                      refine ⟨1741295056301057304604345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321726741734743072805793 1741295056301057304604345)
                      ·
                        rfl

theorem cell23_3391160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_3391160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391160 prefixEnd_3391160 := by exact prefixLift 3391160
  have htrace : WordTrace (prefixWord ++ tailWord_3391160) baseStart_3391160 baseEnd_3391160 := by
    simpa [prefixWord, tailWord_3391160, baseEnd_3391160] using wordTrace_append hprefix tailTrace_3391160
  have hstable : (prefixWord ++ tailWord_3391160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391160).length < 2 ^ (prefixWord ++ tailWord_3391160).sum := by decide
  have hdescent : baseEnd_3391160 < baseStart_3391160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391210 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3391210 : Nat := 118140960795 + 3391210 * 2 ^ 59
def prefixEnd_3391210 : Nat := 4983230072969 + 3 ^ 40 * 3391210 * 2
def baseEnd_3391210 : Nat := 1741320730333782108979115

theorem tailTrace_3391210 : CollatzResearch.WordTrace tailWord_3391210 prefixEnd_3391210 1741320730333782108979115 := by
  unfold tailWord_3391210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30921897511058204350706771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82458393362821878268551389 30921897511058204350706771)
  ·
    refine ⟨46382846266587306526060157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30921897511058204350706771 46382846266587306526060157)
    ·
      refine ⟨17393567349970239947272559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46382846266587306526060157 17393567349970239947272559)
      ·
        refine ⟨26090351024955359920908839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17393567349970239947272559 26090351024955359920908839)
        ·
          refine ⟨39135526537433039881363259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26090351024955359920908839 39135526537433039881363259)
          ·
            refine ⟨58703289806149559822044889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39135526537433039881363259 58703289806149559822044889)
            ·
              refine ⟨44027467354612169866533667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58703289806149559822044889 44027467354612169866533667)
              ·
                refine ⟨66041201031918254799800501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44027467354612169866533667 66041201031918254799800501)
                ·
                  refine ⟨6191362596742336387481297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66041201031918254799800501 6191362596742336387481297)
                  ·
                    refine ⟨4643521947556752290610973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191362596742336387481297 4643521947556752290610973)
                    ·
                      refine ⟨1741320730333782108979115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643521947556752290610973 1741320730333782108979115)
                      ·
                        rfl

theorem cell23_3391210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3391210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391210 prefixEnd_3391210 := by exact prefixLift 3391210
  have htrace : WordTrace (prefixWord ++ tailWord_3391210) baseStart_3391210 baseEnd_3391210 := by
    simpa [prefixWord, tailWord_3391210, baseEnd_3391210] using wordTrace_append hprefix tailTrace_3391210
  have hstable : (prefixWord ++ tailWord_3391210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391210).length < 2 ^ (prefixWord ++ tailWord_3391210).sum := by decide
  have hdescent : baseEnd_3391210 < baseStart_3391210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391240 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_3391240 : Nat := 118140960795 + 3391240 * 2 ^ 59
def prefixEnd_3391240 : Nat := 4983230072969 + 3 ^ 40 * 3391240 * 2
def baseEnd_3391240 : Nat := 1741336134753416991603977

theorem tailTrace_3391240 : CollatzResearch.WordTrace tailWord_3391240 prefixEnd_3391240 1741336134753416991603977 := by
  unfold tailWord_3391240
  simp only [CollatzResearch.WordTrace]
  refine ⟨61844342117062066263209587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82459122822749421684279449 61844342117062066263209587)
  ·
    refine ⟨92766513175593099394814381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61844342117062066263209587 92766513175593099394814381)
    ·
      refine ⟨34787442440847412273055393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92766513175593099394814381 34787442440847412273055393)
      ·
        refine ⟨26090581830635559204791545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34787442440847412273055393 26090581830635559204791545)
        ·
          refine ⟨19567936372976669403593659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26090581830635559204791545 19567936372976669403593659)
          ·
            refine ⟨29351904559465004105390489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19567936372976669403593659 29351904559465004105390489)
            ·
              refine ⟨22013928419598753079042867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29351904559465004105390489 22013928419598753079042867)
              ·
                refine ⟨33020892629398129618564301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22013928419598753079042867 33020892629398129618564301)
                ·
                  refine ⟨12382834736024298606961613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33020892629398129618564301 12382834736024298606961613)
                  ·
                    refine ⟨4643563026009111977610605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12382834736024298606961613 4643563026009111977610605)
                    ·
                      refine ⟨1741336134753416991603977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643563026009111977610605 1741336134753416991603977)
                      ·
                        rfl

theorem cell23_3391240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_3391240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391240 prefixEnd_3391240 := by exact prefixLift 3391240
  have htrace : WordTrace (prefixWord ++ tailWord_3391240) baseStart_3391240 baseEnd_3391240 := by
    simpa [prefixWord, tailWord_3391240, baseEnd_3391240] using wordTrace_append hprefix tailTrace_3391240
  have hstable : (prefixWord ++ tailWord_3391240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391240).length < 2 ^ (prefixWord ++ tailWord_3391240).sum := by decide
  have hdescent : baseEnd_3391240 < baseStart_3391240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391245 : List Nat := [1, 7, 2, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3391245 : Nat := 118140960795 + 3391245 * 2 ^ 59
def prefixEnd_3391245 : Nat := 4983230072969 + 3 ^ 40 * 3391245 * 2
def baseEnd_3391245 : Nat := 1741338702156689472041455

theorem tailTrace_3391245 : CollatzResearch.WordTrace tailWord_3391245 prefixEnd_3391245 1741338702156689472041455 := by
  unfold tailWord_3391245
  simp only [CollatzResearch.WordTrace]
  refine ⟨123688866599106018380351189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82459244399404012253567459 123688866599106018380351189)
  ·
    refine ⟨2898957810916547305789481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 123688866599106018380351189 2898957810916547305789481)
    ·
      refine ⟨2174218358187410479342111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2898957810916547305789481 2174218358187410479342111)
      ·
        refine ⟨3261327537281115719013167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174218358187410479342111 3261327537281115719013167)
        ·
          refine ⟨4891991305921673578519751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261327537281115719013167 4891991305921673578519751)
          ·
            refine ⟨7337986958882510367779627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4891991305921673578519751 7337986958882510367779627)
            ·
              refine ⟨11006980438323765551669441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7337986958882510367779627 11006980438323765551669441)
              ·
                refine ⟨8255235328742824163752081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11006980438323765551669441 8255235328742824163752081)
                ·
                  refine ⟨6191426496557118122814061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8255235328742824163752081 6191426496557118122814061)
                  ·
                    refine ⟨2321784936208919296055273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6191426496557118122814061 2321784936208919296055273)
                    ·
                      refine ⟨1741338702156689472041455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321784936208919296055273 1741338702156689472041455)
                      ·
                        rfl

theorem cell23_3391245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3391245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391245 prefixEnd_3391245 := by exact prefixLift 3391245
  have htrace : WordTrace (prefixWord ++ tailWord_3391245) baseStart_3391245 baseEnd_3391245 := by
    simpa [prefixWord, tailWord_3391245, baseEnd_3391245] using wordTrace_append hprefix tailTrace_3391245
  have hstable : (prefixWord ++ tailWord_3391245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391245).length < 2 ^ (prefixWord ++ tailWord_3391245).sum := by decide
  have hdescent : baseEnd_3391245 < baseStart_3391245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391252 : List Nat := [2, 4, 4, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_3391252 : Nat := 118140960795 + 3391252 * 2 ^ 59
def prefixEnd_3391252 : Nat := 4983230072969 + 3 ^ 40 * 3391252 * 2
def baseEnd_3391252 : Nat := 1741342296521270944653923

theorem tailTrace_3391252 : CollatzResearch.WordTrace tailWord_3391252 prefixEnd_3391252 1741342296521270944653923 := by
  unfold tailWord_3391252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61844560955040329287928005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82459414606720439050570673 61844560955040329287928005)
  ·
    refine ⟨11595855179070061741486501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61844560955040329287928005 11595855179070061741486501)
    ·
      refine ⟨2174222846075636576528719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11595855179070061741486501 2174222846075636576528719)
      ·
        refine ⟨3261334269113454864793079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2174222846075636576528719 3261334269113454864793079)
        ·
          refine ⟨4892001403670182297189619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261334269113454864793079 4892001403670182297189619)
          ·
            refine ⟨7338002105505273445784429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892001403670182297189619 7338002105505273445784429)
            ·
              refine ⟨2751750789564477542169161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7338002105505273445784429 2751750789564477542169161)
              ·
                refine ⟨2063813092173358156626871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751750789564477542169161 2063813092173358156626871)
                ·
                  refine ⟨3095719638260037234940307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063813092173358156626871 3095719638260037234940307)
                  ·
                    refine ⟨4643579457390055852410461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3095719638260037234940307 4643579457390055852410461)
                    ·
                      refine ⟨1741342296521270944653923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643579457390055852410461 1741342296521270944653923)
                      ·
                        rfl

theorem cell23_3391252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_3391252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391252 prefixEnd_3391252 := by exact prefixLift 3391252
  have htrace : WordTrace (prefixWord ++ tailWord_3391252) baseStart_3391252 baseEnd_3391252 := by
    simpa [prefixWord, tailWord_3391252, baseEnd_3391252] using wordTrace_append hprefix tailTrace_3391252
  have hstable : (prefixWord ++ tailWord_3391252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391252).length < 2 ^ (prefixWord ++ tailWord_3391252).sum := by decide
  have hdescent : baseEnd_3391252 < baseStart_3391252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391258 : List Nat := [3, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_3391258 : Nat := 118140960795 + 3391258 * 2 ^ 59
def prefixEnd_3391258 : Nat := 4983230072969 + 3 ^ 40 * 3391258 * 2
def baseEnd_3391258 : Nat := 1741345377405197921178895

theorem tailTrace_3391258 : CollatzResearch.WordTrace tailWord_3391258 prefixEnd_3391258 1741345377405197921178895 := by
  unfold tailWord_3391258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30922335187014730400143607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82459560498705947733716285 30922335187014730400143607)
  ·
    refine ⟨46383502780522095600215411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30922335187014730400143607 46383502780522095600215411)
    ·
      refine ⟨69575254170783143400323117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46383502780522095600215411 69575254170783143400323117)
      ·
        refine ⟨26090720314043678775121169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69575254170783143400323117 26090720314043678775121169)
        ·
          refine ⟨19568040235532759081340877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26090720314043678775121169 19568040235532759081340877)
          ·
            refine ⟨7338015088324784655502829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19568040235532759081340877 7338015088324784655502829)
            ·
              refine ⟨2751755658121794245813561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7338015088324784655502829 2751755658121794245813561)
              ·
                refine ⟨2063816743591345684360171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2751755658121794245813561 2063816743591345684360171)
                ·
                  refine ⟨3095725115387018526540257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063816743591345684360171 3095725115387018526540257)
                  ·
                    refine ⟨2321793836540263894905193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3095725115387018526540257 2321793836540263894905193)
                    ·
                      refine ⟨1741345377405197921178895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321793836540263894905193 1741345377405197921178895)
                      ·
                        rfl

theorem cell23_3391258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_3391258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391258 prefixEnd_3391258 := by exact prefixLift 3391258
  have htrace : WordTrace (prefixWord ++ tailWord_3391258) baseStart_3391258 baseEnd_3391258 := by
    simpa [prefixWord, tailWord_3391258, baseEnd_3391258] using wordTrace_append hprefix tailTrace_3391258
  have hstable : (prefixWord ++ tailWord_3391258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391258).length < 2 ^ (prefixWord ++ tailWord_3391258).sum := by decide
  have hdescent : baseEnd_3391258 < baseStart_3391258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391278 : List Nat := [4, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3391278 : Nat := 118140960795 + 3391278 * 2 ^ 59
def prefixEnd_3391278 : Nat := 4983230072969 + 3 ^ 40 * 3391278 * 2
def baseEnd_3391278 : Nat := 1741355647018287842928803

theorem tailTrace_3391278 : CollatzResearch.WordTrace tailWord_3391278 prefixEnd_3391278 1741355647018287842928803 := by
  unfold tailWord_3391278
  simp only [CollatzResearch.WordTrace]
  refine ⟨15461258775998308127037811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82460046805324310010868325 15461258775998308127037811)
  ·
    refine ⟨23191888163997462190556717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15461258775998308127037811 23191888163997462190556717)
    ·
      refine ⟨8696958061499048321458769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23191888163997462190556717 8696958061499048321458769)
      ·
        refine ⟨6522718546124286241094077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8696958061499048321458769 6522718546124286241094077)
        ·
          refine ⟨2446019454796607340410279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6522718546124286241094077 2446019454796607340410279)
          ·
            refine ⟨3669029182194911010615419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446019454796607340410279 3669029182194911010615419)
            ·
              refine ⟨5503543773292366515923129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669029182194911010615419 5503543773292366515923129)
              ·
                refine ⟨4127657829969274886942347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5503543773292366515923129 4127657829969274886942347)
                ·
                  refine ⟨6191486744953912330413521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127657829969274886942347 6191486744953912330413521)
                  ·
                    refine ⟨4643615058715434247810141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191486744953912330413521 4643615058715434247810141)
                    ·
                      refine ⟨1741355647018287842928803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643615058715434247810141 1741355647018287842928803)
                      ·
                        rfl

theorem cell23_3391278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3391278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391278 prefixEnd_3391278 := by exact prefixLift 3391278
  have htrace : WordTrace (prefixWord ++ tailWord_3391278) baseStart_3391278 baseEnd_3391278 := by
    simpa [prefixWord, tailWord_3391278, baseEnd_3391278] using wordTrace_append hprefix tailTrace_3391278
  have hstable : (prefixWord ++ tailWord_3391278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391278).length < 2 ^ (prefixWord ++ tailWord_3391278).sum := by decide
  have hdescent : baseEnd_3391278 < baseStart_3391278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391323 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_3391323 : Nat := 118140960795 + 3391323 * 2 ^ 59
def prefixEnd_3391323 : Nat := 4983230072969 + 3 ^ 40 * 3391323 * 2
def baseEnd_3391323 : Nat := 1741378753647740166866095

theorem tailTrace_3391323 : CollatzResearch.WordTrace tailWord_3391323 prefixEnd_3391323 1741378753647740166866095 := by
  unfold tailWord_3391323
  simp only [CollatzResearch.WordTrace]
  refine ⟨123691711492823437701690623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82461140995215625134460415 123691711492823437701690623)
  ·
    refine ⟨185537567239235156552535935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123691711492823437701690623 185537567239235156552535935)
    ·
      refine ⟨278306350858852734828803903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185537567239235156552535935 278306350858852734828803903)
      ·
        refine ⟨417459526288279102243205855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278306350858852734828803903 417459526288279102243205855)
        ·
          refine ⟨626189289432418653364808783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417459526288279102243205855 626189289432418653364808783)
          ·
            refine ⟨939283934148627980047213175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626189289432418653364808783 939283934148627980047213175)
            ·
              refine ⟨1408925901222941970070819763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939283934148627980047213175 1408925901222941970070819763)
              ·
                refine ⟨2113388851834412955106229645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408925901222941970070819763 2113388851834412955106229645)
                ·
                  refine ⟨792520819437904858164836117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2113388851834412955106229645 792520819437904858164836117)
                  ·
                    refine ⟨37149413411151790226476693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 792520819437904858164836117 37149413411151790226476693)
                    ·
                      refine ⟨1741378753647740166866095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37149413411151790226476693 1741378753647740166866095)
                      ·
                        rfl

theorem cell23_3391323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_3391323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391323 prefixEnd_3391323 := by exact prefixLift 3391323
  have htrace : WordTrace (prefixWord ++ tailWord_3391323) baseStart_3391323 baseEnd_3391323 := by
    simpa [prefixWord, tailWord_3391323, baseEnd_3391323] using wordTrace_append hprefix tailTrace_3391323
  have hstable : (prefixWord ++ tailWord_3391323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391323).length < 2 ^ (prefixWord ++ tailWord_3391323).sum := by decide
  have hdescent : baseEnd_3391323 < baseStart_3391323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391382 : List Nat := [5, 3, 1, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_3391382 : Nat := 118140960795 + 3391382 * 2 ^ 59
def prefixEnd_3391382 : Nat := 4983230072969 + 3 ^ 40 * 3391382 * 2
def baseEnd_3391382 : Nat := 1741409049006355436028325

theorem tailTrace_3391382 : CollatzResearch.WordTrace tailWord_3391382 prefixEnd_3391382 1741409049006355436028325 := by
  unfold tailWord_3391382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7730866462475605673630525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82462575599739793852058933 7730866462475605673630525)
  ·
    refine ⟨2899074923428352127611447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7730866462475605673630525 2899074923428352127611447)
    ·
      refine ⟨4348612385142528191417171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2899074923428352127611447 4348612385142528191417171)
      ·
        refine ⟨6522918577713792287125757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348612385142528191417171 6522918577713792287125757)
        ·
          refine ⟨2446094466642672107672159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6522918577713792287125757 2446094466642672107672159)
          ·
            refine ⟨3669141699964008161508239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2446094466642672107672159 3669141699964008161508239)
            ·
              refine ⟨5503712549946012242262359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669141699964008161508239 5503712549946012242262359)
              ·
                refine ⟨8255568824919018363393539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503712549946012242262359 8255568824919018363393539)
                ·
                  refine ⟨12383353237378527545090309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255568824919018363393539 12383353237378527545090309)
                  ·
                    refine ⟨2321878732008473914704433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12383353237378527545090309 2321878732008473914704433)
                    ·
                      refine ⟨1741409049006355436028325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2321878732008473914704433 1741409049006355436028325)
                      ·
                        rfl

theorem cell23_3391382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_3391382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391382 prefixEnd_3391382 := by exact prefixLift 3391382
  have htrace : WordTrace (prefixWord ++ tailWord_3391382) baseStart_3391382 baseEnd_3391382 := by
    simpa [prefixWord, tailWord_3391382, baseEnd_3391382] using wordTrace_append hprefix tailTrace_3391382
  have hstable : (prefixWord ++ tailWord_3391382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391382).length < 2 ^ (prefixWord ++ tailWord_3391382).sum := by decide
  have hdescent : baseEnd_3391382 < baseStart_3391382 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391407 : List Nat := [1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_3391407 : Nat := 118140960795 + 3391407 * 2 ^ 59
def prefixEnd_3391407 : Nat := 4983230072969 + 3 ^ 40 * 3391407 * 2
def baseEnd_3391407 : Nat := 1741421886022717838215709

theorem tailTrace_3391407 : CollatzResearch.WordTrace tailWord_3391407 prefixEnd_3391407 1741421886022717838215709 := by
  unfold tailWord_3391407
  simp only [CollatzResearch.WordTrace]
  refine ⟨123694775224519120047748475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82463183483012746698498983 123694775224519120047748475)
  ·
    refine ⟨185542162836778680071622713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123694775224519120047748475 185542162836778680071622713)
    ·
      refine ⟨139156622127584010053717035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185542162836778680071622713 139156622127584010053717035)
      ·
        refine ⟨208734933191376015080575553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139156622127584010053717035 208734933191376015080575553)
        ·
          refine ⟨156551199893532011310431665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208734933191376015080575553 156551199893532011310431665)
          ·
            refine ⟨117413399920149008482823749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156551199893532011310431665 117413399920149008482823749)
            ·
              refine ⟨22015012485027939090529453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117413399920149008482823749 22015012485027939090529453)
              ·
                refine ⟨8255629681885477158948545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22015012485027939090529453 8255629681885477158948545)
                ·
                  refine ⟨6191722261414107869211409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8255629681885477158948545 6191722261414107869211409)
                  ·
                    refine ⟨4643791696060580901908557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191722261414107869211409 4643791696060580901908557)
                    ·
                      refine ⟨1741421886022717838215709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643791696060580901908557 1741421886022717838215709)
                      ·
                        rfl

theorem cell23_3391407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_3391407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391407 prefixEnd_3391407 := by exact prefixLift 3391407
  have htrace : WordTrace (prefixWord ++ tailWord_3391407) baseStart_3391407 baseEnd_3391407 := by
    simpa [prefixWord, tailWord_3391407, baseEnd_3391407] using wordTrace_append hprefix tailTrace_3391407
  have hstable : (prefixWord ++ tailWord_3391407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391407).length < 2 ^ (prefixWord ++ tailWord_3391407).sum := by decide
  have hdescent : baseEnd_3391407 < baseStart_3391407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391458 : List Nat := [3, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3391458 : Nat := 118140960795 + 3391458 * 2 ^ 59
def prefixEnd_3391458 : Nat := 4983230072969 + 3 ^ 40 * 3391458 * 2
def baseEnd_3391458 : Nat := 1741448073536097138677975

theorem tailTrace_3391458 : CollatzResearch.WordTrace tailWord_3391458 prefixEnd_3391458 1741448073536097138677975 := by
  unfold tailWord_3391458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30924158836833588939463757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82464423564889570505236685 30924158836833588939463757)
  ·
    refine ⟨11596559563812595852298909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30924158836833588939463757 11596559563812595852298909)
    ·
      refine ⟨4348709836429723444612091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11596559563812595852298909 4348709836429723444612091)
      ·
        refine ⟨6523064754644585166918137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4348709836429723444612091 6523064754644585166918137)
        ·
          refine ⟨4892298565983438875188603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6523064754644585166918137 4892298565983438875188603)
          ·
            refine ⟨7338447848975158312782905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892298565983438875188603 7338447848975158312782905)
            ·
              refine ⟨5503835886731368734587179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7338447848975158312782905 5503835886731368734587179)
              ·
                refine ⟨8255753830097053101880769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5503835886731368734587179 8255753830097053101880769)
                ·
                  refine ⟨6191815372572789826410577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8255753830097053101880769 6191815372572789826410577)
                  ·
                    refine ⟨4643861529429592369807933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191815372572789826410577 4643861529429592369807933)
                    ·
                      refine ⟨1741448073536097138677975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643861529429592369807933 1741448073536097138677975)
                      ·
                        rfl

theorem cell23_3391458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3391458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391458 prefixEnd_3391458 := by exact prefixLift 3391458
  have htrace : WordTrace (prefixWord ++ tailWord_3391458) baseStart_3391458 baseEnd_3391458 := by
    simpa [prefixWord, tailWord_3391458, baseEnd_3391458] using wordTrace_append hprefix tailTrace_3391458
  have hstable : (prefixWord ++ tailWord_3391458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391458).length < 2 ^ (prefixWord ++ tailWord_3391458).sum := by decide
  have hdescent : baseEnd_3391458 < baseStart_3391458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391471 : List Nat := [1, 1, 2, 1, 4, 2, 2, 5, 1, 1, 3]
def baseStart_3391471 : Nat := 118140960795 + 3391471 * 2 ^ 59
def prefixEnd_3391471 : Nat := 4983230072969 + 3 ^ 40 * 3391471 * 2
def baseEnd_3391471 : Nat := 1741454748784605587815415

theorem tailTrace_3391471 : CollatzResearch.WordTrace tailWord_3391471 prefixEnd_3391471 1741454748784605587815415 := by
  unfold tailWord_3391471
  simp only [CollatzResearch.WordTrace]
  refine ⟨123697109496287258978078267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82464739664191505985385511 123697109496287258978078267)
  ·
    refine ⟨185545664244430888467117401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123697109496287258978078267 185545664244430888467117401)
    ·
      refine ⟨139159248183323166350338051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185545664244430888467117401 139159248183323166350338051)
      ·
        refine ⟨208738872274984749525507077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139159248183323166350338051 208738872274984749525507077)
        ·
          refine ⟨39138538551559640536032577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208738872274984749525507077 39138538551559640536032577)
          ·
            refine ⟨29353903913669730402024433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39138538551559640536032577 29353903913669730402024433)
            ·
              refine ⟨22015427935252297801518325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29353903913669730402024433 22015427935252297801518325)
              ·
                refine ⟨2063946368929902918892343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22015427935252297801518325 2063946368929902918892343)
                ·
                  refine ⟨3095919553394854378338515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2063946368929902918892343 3095919553394854378338515)
                  ·
                    refine ⟨4643879330092281567507773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3095919553394854378338515 4643879330092281567507773)
                    ·
                      refine ⟨1741454748784605587815415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643879330092281567507773 1741454748784605587815415)
                      ·
                        rfl

theorem cell23_3391471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 5, 1, 1, 3].length) (baseStart_3391471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391471 prefixEnd_3391471 := by exact prefixLift 3391471
  have htrace : WordTrace (prefixWord ++ tailWord_3391471) baseStart_3391471 baseEnd_3391471 := by
    simpa [prefixWord, tailWord_3391471, baseEnd_3391471] using wordTrace_append hprefix tailTrace_3391471
  have hstable : (prefixWord ++ tailWord_3391471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391471).length < 2 ^ (prefixWord ++ tailWord_3391471).sum := by decide
  have hdescent : baseEnd_3391471 < baseStart_3391471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391487 : List Nat := [1, 1, 2, 2, 1, 2, 1, 5, 4, 4]
def baseStart_3391487 : Nat := 118140960795 + 3391487 * 2 ^ 59
def prefixEnd_3391487 : Nat := 4983230072969 + 3 ^ 40 * 3391487 * 2
def baseEnd_3391487 : Nat := 580487654825025841738447

theorem tailTrace_3391487 : CollatzResearch.WordTrace tailWord_3391487 prefixEnd_3391487 580487654825025841738447 := by
  unfold tailWord_3391487
  simp only [CollatzResearch.WordTrace]
  refine ⟨123697693064229293710660715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82465128709486195807107143 123697693064229293710660715)
  ·
    refine ⟨185546539596343940565991073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123697693064229293710660715 185546539596343940565991073)
    ·
      refine ⟨139159904697257955424493305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185546539596343940565991073 139159904697257955424493305)
      ·
        refine ⟨104369928522943466568369979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139159904697257955424493305 104369928522943466568369979)
        ·
          refine ⟨156554892784415199852554969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104369928522943466568369979 156554892784415199852554969)
          ·
            refine ⟨117416169588311399889416227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156554892784415199852554969 117416169588311399889416227)
            ·
              refine ⟨176124254382467099834124341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117416169588311399889416227 176124254382467099834124341)
              ·
                refine ⟨16511648848356290609449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176124254382467099834124341 16511648848356290609449157)
                ·
                  refine ⟨3095934159066804489271717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16511648848356290609449157 3095934159066804489271717)
                  ·
                    refine ⟨580487654825025841738447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3095934159066804489271717 580487654825025841738447)
                    ·
                      rfl

theorem cell23_3391487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_3391487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391487 prefixEnd_3391487 := by exact prefixLift 3391487
  have htrace : WordTrace (prefixWord ++ tailWord_3391487) baseStart_3391487 baseEnd_3391487 := by
    simpa [prefixWord, tailWord_3391487, baseEnd_3391487] using wordTrace_append hprefix tailTrace_3391487
  have hstable : (prefixWord ++ tailWord_3391487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391487).length < 2 ^ (prefixWord ++ tailWord_3391487).sum := by decide
  have hdescent : baseEnd_3391487 < baseStart_3391487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391507 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_3391507 : Nat := 118140960795 + 3391507 * 2 ^ 59
def prefixEnd_3391507 : Nat := 4983230072969 + 3 ^ 40 * 3391507 * 2
def baseEnd_3391507 : Nat := 1741473234088167446965249

theorem tailTrace_3391507 : CollatzResearch.WordTrace tailWord_3391507 prefixEnd_3391507 1741473234088167446965249 := by
  unfold tailWord_3391507
  simp only [CollatzResearch.WordTrace]
  refine ⟨123698422524156837126388775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82465615016104558084259183 123698422524156837126388775)
  ·
    refine ⟨185547633786235255689583163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123698422524156837126388775 185547633786235255689583163)
    ·
      refine ⟨278321450679352883534374745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185547633786235255689583163 278321450679352883534374745)
      ·
        refine ⟨208741088009514662650781059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278321450679352883534374745 208741088009514662650781059)
        ·
          refine ⟨313111632014271993976171589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208741088009514662650781059 313111632014271993976171589)
          ·
            refine ⟨58708431002675998870532173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 313111632014271993976171589 58708431002675998870532173)
            ·
              refine ⟨22015661626003499576449565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58708431002675998870532173 22015661626003499576449565)
              ·
                refine ⟨8255873109751312341168587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22015661626003499576449565 8255873109751312341168587)
                ·
                  refine ⟨12383809664626968511752881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8255873109751312341168587 12383809664626968511752881)
                  ·
                    refine ⟨9287857248470226383814661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12383809664626968511752881 9287857248470226383814661)
                    ·
                      refine ⟨1741473234088167446965249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9287857248470226383814661 1741473234088167446965249)
                      ·
                        rfl

theorem cell23_3391507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_3391507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391507 prefixEnd_3391507 := by exact prefixLift 3391507
  have htrace : WordTrace (prefixWord ++ tailWord_3391507) baseStart_3391507 baseEnd_3391507 := by
    simpa [prefixWord, tailWord_3391507, baseEnd_3391507] using wordTrace_append hprefix tailTrace_3391507
  have hstable : (prefixWord ++ tailWord_3391507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391507).length < 2 ^ (prefixWord ++ tailWord_3391507).sum := by decide
  have hdescent : baseEnd_3391507 < baseStart_3391507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391514 : List Nat := [3, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_3391514 : Nat := 118140960795 + 3391514 * 2 ^ 59
def prefixEnd_3391514 : Nat := 4983230072969 + 3 ^ 40 * 3391514 * 2
def baseEnd_3391514 : Nat := 1741476828452748919577717

theorem tailTrace_3391514 : CollatzResearch.WordTrace tailWord_3391514 prefixEnd_3391514 1741476828452748919577717 := by
  unfold tailWord_3391514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30924669458782869330473399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82465785223420984881262397 30924669458782869330473399)
  ·
    refine ⟨46387004188174303995710099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30924669458782869330473399 46387004188174303995710099)
    ·
      refine ⟨69580506282261455993565149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46387004188174303995710099 69580506282261455993565149)
      ·
        refine ⟨26092689855848045997586931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69580506282261455993565149 26092689855848045997586931)
        ·
          refine ⟨39139034783772068996380397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26092689855848045997586931 39139034783772068996380397)
          ·
            refine ⟨14677138043914525873642649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39139034783772068996380397 14677138043914525873642649)
            ·
              refine ⟨11007853532935894405231987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14677138043914525873642649 11007853532935894405231987)
              ·
                refine ⟨16511780299403841607847981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11007853532935894405231987 16511780299403841607847981)
                ·
                  refine ⟨6191917612276440602942993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16511780299403841607847981 6191917612276440602942993)
                  ·
                    refine ⟨4643938209207330452207245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6191917612276440602942993 4643938209207330452207245)
                    ·
                      refine ⟨1741476828452748919577717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4643938209207330452207245 1741476828452748919577717)
                      ·
                        rfl

theorem cell23_3391514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_3391514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391514 prefixEnd_3391514 := by exact prefixLift 3391514
  have htrace : WordTrace (prefixWord ++ tailWord_3391514) baseStart_3391514 baseEnd_3391514 := by
    simpa [prefixWord, tailWord_3391514, baseEnd_3391514] using wordTrace_append hprefix tailTrace_3391514
  have hstable : (prefixWord ++ tailWord_3391514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391514).length < 2 ^ (prefixWord ++ tailWord_3391514).sum := by decide
  have hdescent : baseEnd_3391514 < baseStart_3391514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391528 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_3391528 : Nat := 118140960795 + 3391528 * 2 ^ 59
def prefixEnd_3391528 : Nat := 4983230072969 + 3 ^ 40 * 3391528 * 2
def baseEnd_3391528 : Nat := 1741484017181911864802653

theorem tailTrace_3391528 : CollatzResearch.WordTrace tailWord_3391528 prefixEnd_3391528 1741484017181911864802653 := by
  unfold tailWord_3391528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61849594228540378856451619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82466125638053838475268825 61849594228540378856451619)
  ·
    refine ⟨92774391342810568284677429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61849594228540378856451619 92774391342810568284677429)
    ·
      refine ⟨8697599188388490776688509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92774391342810568284677429 8697599188388490776688509)
      ·
        refine ⟨3261599695645684041258191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8697599188388490776688509 3261599695645684041258191)
        ·
          refine ⟨4892399543468526061887287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261599695645684041258191 4892399543468526061887287)
          ·
            refine ⟨7338599315202789092830931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892399543468526061887287 7338599315202789092830931)
            ·
              refine ⟨11007898972804183639246397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7338599315202789092830931 11007898972804183639246397)
              ·
                refine ⟨4127962114801568864717399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11007898972804183639246397 4127962114801568864717399)
                ·
                  refine ⟨6191943172202353297076099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4127962114801568864717399 6191943172202353297076099)
                  ·
                    refine ⟨9287914758303529945614149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6191943172202353297076099 9287914758303529945614149)
                    ·
                      refine ⟨1741484017181911864802653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9287914758303529945614149 1741484017181911864802653)
                      ·
                        rfl

theorem cell23_3391528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_3391528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391528 prefixEnd_3391528 := by exact prefixLift 3391528
  have htrace : WordTrace (prefixWord ++ tailWord_3391528) baseStart_3391528 baseEnd_3391528 := by
    simpa [prefixWord, tailWord_3391528, baseEnd_3391528] using wordTrace_append hprefix tailTrace_3391528
  have hstable : (prefixWord ++ tailWord_3391528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391528).length < 2 ^ (prefixWord ++ tailWord_3391528).sum := by decide
  have hdescent : baseEnd_3391528 < baseStart_3391528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391587 : List Nat := [1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_3391587 : Nat := 118140960795 + 3391587 * 2 ^ 59
def prefixEnd_3391587 : Nat := 4983230072969 + 3 ^ 40 * 3391587 * 2
def baseEnd_3391587 : Nat := 1741514312540527133964881

theorem tailTrace_3391587 : CollatzResearch.WordTrace tailWord_3391587 prefixEnd_3391587 1741514312540527133964881 := by
  unfold tailWord_3391587
  simp only [CollatzResearch.WordTrace]
  refine ⟨123701340363867010789301015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82467560242578007192867343 123701340363867010789301015)
  ·
    refine ⟨185552010545800516183951523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123701340363867010789301015 185552010545800516183951523)
    ·
      refine ⟨278328015818700774275927285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185552010545800516183951523 278328015818700774275927285)
      ·
        refine ⟨26093251483003197588368183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 278328015818700774275927285 26093251483003197588368183)
        ·
          refine ⟨39139877224504796382552275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26093251483003197588368183 39139877224504796382552275)
          ·
            refine ⟨58709815836757194573828413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39139877224504796382552275 58709815836757194573828413)
            ·
              refine ⟨22016180938783947965185655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58709815836757194573828413 22016180938783947965185655)
              ·
                refine ⟨33024271408175921947778483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22016180938783947965185655 33024271408175921947778483)
                ·
                  refine ⟨49536407112263882921667725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33024271408175921947778483 49536407112263882921667725)
                  ·
                    refine ⟨18576152667098956095625397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49536407112263882921667725 18576152667098956095625397)
                    ·
                      refine ⟨1741514312540527133964881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18576152667098956095625397 1741514312540527133964881)
                      ·
                        rfl

theorem cell23_3391587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_3391587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391587 prefixEnd_3391587 := by exact prefixLift 3391587
  have htrace : WordTrace (prefixWord ++ tailWord_3391587) baseStart_3391587 baseEnd_3391587 := by
    simpa [prefixWord, tailWord_3391587, baseEnd_3391587] using wordTrace_append hprefix tailTrace_3391587
  have hstable : (prefixWord ++ tailWord_3391587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391587).length < 2 ^ (prefixWord ++ tailWord_3391587).sum := by decide
  have hdescent : baseEnd_3391587 < baseStart_3391587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391601 : List Nat := [1, 2, 2, 2, 1, 1, 3, 3, 4, 2, 2]
def baseStart_3391601 : Nat := 118140960795 + 3391601 * 2 ^ 59
def prefixEnd_3391601 : Nat := 4983230072969 + 3 ^ 40 * 3391601 * 2
def baseEnd_3391601 : Nat := 1741521501269690079189817

theorem tailTrace_3391601 : CollatzResearch.WordTrace tailWord_3391601 prefixEnd_3391601 1741521501269690079189817 := by
  unfold tailWord_3391601
  simp only [CollatzResearch.WordTrace]
  refine ⟨123701850985816291180310657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82467900657210860786873771 123701850985816291180310657)
  ·
    refine ⟨92776388239362218385232993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123701850985816291180310657 92776388239362218385232993)
    ·
      refine ⟨69582291179521663788924745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92776388239362218385232993 69582291179521663788924745)
      ·
        refine ⟨52186718384641247841693559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69582291179521663788924745 52186718384641247841693559)
        ·
          refine ⟨78280077576961871762540339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52186718384641247841693559 78280077576961871762540339)
          ·
            refine ⟨117420116365442807643810509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78280077576961871762540339 117420116365442807643810509)
            ·
              refine ⟨44032543637041052866428941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117420116365442807643810509 44032543637041052866428941)
              ·
                refine ⟨16512203863890394824910853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44032543637041052866428941 16512203863890394824910853)
                ·
                  refine ⟨3096038224479449029670785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16512203863890394824910853 3096038224479449029670785)
                  ·
                    refine ⟨2322028668359586772253089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096038224479449029670785 2322028668359586772253089)
                    ·
                      refine ⟨1741521501269690079189817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322028668359586772253089 1741521501269690079189817)
                      ·
                        rfl

theorem cell23_3391601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_3391601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391601 prefixEnd_3391601 := by exact prefixLift 3391601
  have htrace : WordTrace (prefixWord ++ tailWord_3391601) baseStart_3391601 baseEnd_3391601 := by
    simpa [prefixWord, tailWord_3391601, baseEnd_3391601] using wordTrace_append hprefix tailTrace_3391601
  have hstable : (prefixWord ++ tailWord_3391601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391601).length < 2 ^ (prefixWord ++ tailWord_3391601).sum := by decide
  have hdescent : baseEnd_3391601 < baseStart_3391601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391667 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 2, 8]
def baseStart_3391667 : Nat := 118140960795 + 3391667 * 2 ^ 59
def prefixEnd_3391667 : Nat := 4983230072969 + 3 ^ 40 * 3391667 * 2
def baseEnd_3391667 : Nat := 580518463664295606988171

theorem tailTrace_3391667 : CollatzResearch.WordTrace tailWord_3391667 prefixEnd_3391667 580518463664295606988171 := by
  unfold tailWord_3391667
  simp only [CollatzResearch.WordTrace]
  refine ⟨123704258203577184452213255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82469505469051456301475503 123704258203577184452213255)
  ·
    refine ⟨185556387305365776678319883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123704258203577184452213255 185556387305365776678319883)
    ·
      refine ⟨278334580958048665017479825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185556387305365776678319883 278334580958048665017479825)
      ·
        refine ⟨208750935718536498763109869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278334580958048665017479825 208750935718536498763109869)
        ·
          refine ⟨78281600894451187036166201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208750935718536498763109869 78281600894451187036166201)
          ·
            refine ⟨58711200670838390277124651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78281600894451187036166201 58711200670838390277124651)
            ·
              refine ⟨88066801006257585415686977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58711200670838390277124651 88066801006257585415686977)
              ·
                refine ⟨66050100754693189061765233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88066801006257585415686977 66050100754693189061765233)
                ·
                  refine ⟨49537575566019891796323925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66050100754693189061765233 49537575566019891796323925)
                  ·
                    refine ⟨580518463664295606988171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49537575566019891796323925 580518463664295606988171)
                    ·
                      rfl

theorem cell23_3391667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_3391667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391667 prefixEnd_3391667 := by exact prefixLift 3391667
  have htrace : WordTrace (prefixWord ++ tailWord_3391667) baseStart_3391667 baseEnd_3391667 := by
    simpa [prefixWord, tailWord_3391667, baseEnd_3391667] using wordTrace_append hprefix tailTrace_3391667
  have hstable : (prefixWord ++ tailWord_3391667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391667).length < 2 ^ (prefixWord ++ tailWord_3391667).sum := by decide
  have hdescent : baseEnd_3391667 < baseStart_3391667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391674 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_3391674 : Nat := 118140960795 + 3391674 * 2 ^ 59
def prefixEnd_3391674 : Nat := 4983230072969 + 3 ^ 40 * 3391674 * 2
def baseEnd_3391674 : Nat := 1741558985357468293576981

theorem tailTrace_3391674 : CollatzResearch.WordTrace tailWord_3391674 prefixEnd_3391674 1741558985357468293576981 := by
  unfold tailWord_3391674
  simp only [CollatzResearch.WordTrace]
  refine ⟨30926128378637956161929519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82469675676367883098478717 30926128378637956161929519)
  ·
    refine ⟨46389192567956934242894279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30926128378637956161929519 46389192567956934242894279)
    ·
      refine ⟨69583788851935401364341419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46389192567956934242894279 69583788851935401364341419)
      ·
        refine ⟨104375683277903102046512129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69583788851935401364341419 104375683277903102046512129)
        ·
          refine ⟨78281762458427326534884097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104375683277903102046512129 78281762458427326534884097)
          ·
            refine ⟨58711321843820494901163073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78281762458427326534884097 58711321843820494901163073)
            ·
              refine ⟨44033491382865371175872305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58711321843820494901163073 44033491382865371175872305)
              ·
                refine ⟨33025118537149028381904229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44033491382865371175872305 33025118537149028381904229)
                ·
                  refine ⟨6192209725715442821607043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33025118537149028381904229 6192209725715442821607043)
                  ·
                    refine ⟨9288314588573164232410565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192209725715442821607043 9288314588573164232410565)
                    ·
                      refine ⟨1741558985357468293576981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9288314588573164232410565 1741558985357468293576981)
                      ·
                        rfl

theorem cell23_3391674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_3391674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391674 prefixEnd_3391674 := by exact prefixLift 3391674
  have htrace : WordTrace (prefixWord ++ tailWord_3391674) baseStart_3391674 baseEnd_3391674 := by
    simpa [prefixWord, tailWord_3391674, baseEnd_3391674] using wordTrace_append hprefix tailTrace_3391674
  have hstable : (prefixWord ++ tailWord_3391674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391674).length < 2 ^ (prefixWord ++ tailWord_3391674).sum := by decide
  have hdescent : baseEnd_3391674 < baseStart_3391674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391704 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6]
def baseStart_3391704 : Nat := 118140960795 + 3391704 * 2 ^ 59
def prefixEnd_3391704 : Nat := 4983230072969 + 3 ^ 40 * 3391704 * 2
def baseEnd_3391704 : Nat := 1741574389777103176201843

theorem tailTrace_3391704 : CollatzResearch.WordTrace tailWord_3391704 prefixEnd_3391704 1741574389777103176201843 := by
  unfold tailWord_3391704
  simp only [CollatzResearch.WordTrace]
  refine ⟨61852803852221569885655083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82470405136295426514206777 61852803852221569885655083)
  ·
    refine ⟨92779205778332354828482625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61852803852221569885655083 92779205778332354828482625)
    ·
      refine ⟨69584404333749266121361969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92779205778332354828482625 69584404333749266121361969)
      ·
        refine ⟨52188303250311949591021477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69584404333749266121361969 52188303250311949591021477)
        ·
          refine ⟨9785306859433490548316527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52188303250311949591021477 9785306859433490548316527)
          ·
            refine ⟨14677960289150235822474791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785306859433490548316527 14677960289150235822474791)
            ·
              refine ⟨22016940433725353733712187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14677960289150235822474791 22016940433725353733712187)
              ·
                refine ⟨33025410650588030600568281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22016940433725353733712187 33025410650588030600568281)
                ·
                  refine ⟨24769057987941022950426211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33025410650588030600568281 24769057987941022950426211)
                  ·
                    refine ⟨37153586981911534425639317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24769057987941022950426211 37153586981911534425639317)
                    ·
                      refine ⟨1741574389777103176201843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37153586981911534425639317 1741574389777103176201843)
                      ·
                        rfl

theorem cell23_3391704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_3391704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391704 prefixEnd_3391704 := by exact prefixLift 3391704
  have htrace : WordTrace (prefixWord ++ tailWord_3391704) baseStart_3391704 baseEnd_3391704 := by
    simpa [prefixWord, tailWord_3391704, baseEnd_3391704] using wordTrace_append hprefix tailTrace_3391704
  have hstable : (prefixWord ++ tailWord_3391704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391704).length < 2 ^ (prefixWord ++ tailWord_3391704).sum := by decide
  have hdescent : baseEnd_3391704 < baseStart_3391704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391731 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 6]
def baseStart_3391731 : Nat := 118140960795 + 3391731 * 2 ^ 59
def prefixEnd_3391731 : Nat := 4983230072969 + 3 ^ 40 * 3391731 * 2
def baseEnd_3391731 : Nat := 193509805972752730062691

theorem tailTrace_3391731 : CollatzResearch.WordTrace tailWord_3391731 prefixEnd_3391731 193509805972752730062691 := by
  unfold tailWord_3391731
  simp only [CollatzResearch.WordTrace]
  refine ⟨123706592475345323382543047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82471061650230215588362031 123706592475345323382543047)
  ·
    refine ⟨185559888713017985073814571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123706592475345323382543047 185559888713017985073814571)
    ·
      refine ⟨278339833069526977610721857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185559888713017985073814571 278339833069526977610721857)
      ·
        refine ⟨208754874802145233208041393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278339833069526977610721857 208754874802145233208041393)
        ·
          refine ⟨156566156101608924906031045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208754874802145233208041393 156566156101608924906031045)
          ·
            refine ⟨29356154269051673419880821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 156566156101608924906031045 29356154269051673419880821)
            ·
              refine ⟨2752139462723594383113827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29356154269051673419880821 2752139462723594383113827)
              ·
                refine ⟨4128209194085391574670741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752139462723594383113827 4128209194085391574670741)
                ·
                  refine ⟨193509805972752730062691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4128209194085391574670741 193509805972752730062691)
                  ·
                    rfl

theorem cell23_3391731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 6].length) (baseStart_3391731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391731 prefixEnd_3391731 := by exact prefixLift 3391731
  have htrace : WordTrace (prefixWord ++ tailWord_3391731) baseStart_3391731 baseEnd_3391731 := by
    simpa [prefixWord, tailWord_3391731, baseEnd_3391731] using wordTrace_append hprefix tailTrace_3391731
  have hstable : (prefixWord ++ tailWord_3391731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391731).length < 2 ^ (prefixWord ++ tailWord_3391731).sum := by decide
  have hdescent : baseEnd_3391731 < baseStart_3391731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391744 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 3, 5]
def baseStart_3391744 : Nat := 118140960795 + 3391744 * 2 ^ 59
def prefixEnd_3391744 : Nat := 4983230072969 + 3 ^ 40 * 3391744 * 2
def baseEnd_3391744 : Nat := 580531643001094339900553

theorem tailTrace_3391744 : CollatzResearch.WordTrace tailWord_3391744 prefixEnd_3391744 580531643001094339900553 := by
  unfold tailWord_3391744
  simp only [CollatzResearch.WordTrace]
  refine ⟨61853533312149113301383143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82471377749532151068510857 61853533312149113301383143)
  ·
    refine ⟨92780299968223669952074715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61853533312149113301383143 92780299968223669952074715)
    ·
      refine ⟨139170449952335504928112073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92780299968223669952074715 139170449952335504928112073)
      ·
        refine ⟨104377837464251628696084055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139170449952335504928112073 104377837464251628696084055)
        ·
          refine ⟨156566756196377443044126083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104377837464251628696084055 156566756196377443044126083)
          ·
            refine ⟨234850134294566164566189125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156566756196377443044126083 234850134294566164566189125)
            ·
              refine ⟨44034400180231155856160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 234850134294566164566189125 44034400180231155856160461)
              ·
                refine ⟨16512900067586683446060173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44034400180231155856160461 16512900067586683446060173)
                ·
                  refine ⟨6192337525345006292272565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16512900067586683446060173 6192337525345006292272565)
                  ·
                    refine ⟨580531643001094339900553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6192337525345006292272565 580531643001094339900553)
                    ·
                      rfl

theorem cell23_3391744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 3, 5].length) (baseStart_3391744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391744 prefixEnd_3391744 := by exact prefixLift 3391744
  have htrace : WordTrace (prefixWord ++ tailWord_3391744) baseStart_3391744 baseEnd_3391744 := by
    simpa [prefixWord, tailWord_3391744, baseEnd_3391744] using wordTrace_append hprefix tailTrace_3391744
  have hstable : (prefixWord ++ tailWord_3391744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391744).length < 2 ^ (prefixWord ++ tailWord_3391744).sum := by decide
  have hdescent : baseEnd_3391744 < baseStart_3391744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391761 : List Nat := [1, 2, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_3391761 : Nat := 118140960795 + 3391761 * 2 ^ 59
def prefixEnd_3391761 : Nat := 4983230072969 + 3 ^ 40 * 3391761 * 2
def baseEnd_3391761 : Nat := 580534552724803151063027

theorem tailTrace_3391761 : CollatzResearch.WordTrace tailWord_3391761 prefixEnd_3391761 580534552724803151063027 := by
  unfold tailWord_3391761
  simp only [CollatzResearch.WordTrace]
  refine ⟨123707686665236638506135137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82471791110157759004090091 123707686665236638506135137)
  ·
    refine ⟨92780764998927478879601353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123707686665236638506135137 92780764998927478879601353)
    ·
      refine ⟨69585573749195609159701015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92780764998927478879601353 69585573749195609159701015)
      ·
        refine ⟨104378360623793413739551523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69585573749195609159701015 104378360623793413739551523)
        ·
          refine ⟨156567540935690120609327285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104378360623793413739551523 156567540935690120609327285)
          ·
            refine ⟨14678206962720948807124433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 156567540935690120609327285 14678206962720948807124433)
            ·
              refine ⟨11008655222040711605343325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14678206962720948807124433 11008655222040711605343325)
              ·
                refine ⟨4128245708265266852003747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11008655222040711605343325 4128245708265266852003747)
                ·
                  refine ⟨6192368562397900278005621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128245708265266852003747 6192368562397900278005621)
                  ·
                    refine ⟨580534552724803151063027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6192368562397900278005621 580534552724803151063027)
                    ·
                      rfl

theorem cell23_3391761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_3391761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391761 prefixEnd_3391761 := by exact prefixLift 3391761
  have htrace : WordTrace (prefixWord ++ tailWord_3391761) baseStart_3391761 baseEnd_3391761 := by
    simpa [prefixWord, tailWord_3391761, baseEnd_3391761] using wordTrace_append hprefix tailTrace_3391761
  have hstable : (prefixWord ++ tailWord_3391761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391761).length < 2 ^ (prefixWord ++ tailWord_3391761).sum := by decide
  have hdescent : baseEnd_3391761 < baseStart_3391761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391768 : List Nat := [2, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_3391768 : Nat := 118140960795 + 3391768 * 2 ^ 59
def prefixEnd_3391768 : Nat := 4983230072969 + 3 ^ 40 * 3391768 * 2
def baseEnd_3391768 : Nat := 1741607252538990925801549

theorem tailTrace_3391768 : CollatzResearch.WordTrace tailWord_3391768 prefixEnd_3391768 1741607252538990925801549 := by
  unfold tailWord_3391768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61853970988105639350819979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82471961317474185801093305 61853970988105639350819979)
  ·
    refine ⟨92780956482158459026229969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61853970988105639350819979 92780956482158459026229969)
    ·
      refine ⟨69585717361618844269672477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92780956482158459026229969 69585717361618844269672477)
      ·
        refine ⟨26094644010607066601127179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69585717361618844269672477 26094644010607066601127179)
        ·
          refine ⟨39141966015910599901690769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26094644010607066601127179 39141966015910599901690769)
          ·
            refine ⟨29356474511932949926268077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39141966015910599901690769 29356474511932949926268077)
            ·
              refine ⟨11008677941974856222350529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29356474511932949926268077 11008677941974856222350529)
              ·
                refine ⟨8256508456481142166762897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11008677941974856222350529 8256508456481142166762897)
                ·
                  refine ⟨6192381342360856625072173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8256508456481142166762897 6192381342360856625072173)
                  ·
                    refine ⟨2322143003385321234402065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6192381342360856625072173 2322143003385321234402065)
                    ·
                      refine ⟨1741607252538990925801549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322143003385321234402065 1741607252538990925801549)
                      ·
                        rfl

theorem cell23_3391768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_3391768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391768 prefixEnd_3391768 := by exact prefixLift 3391768
  have htrace : WordTrace (prefixWord ++ tailWord_3391768) baseStart_3391768 baseEnd_3391768 := by
    simpa [prefixWord, tailWord_3391768, baseEnd_3391768] using wordTrace_append hprefix tailTrace_3391768
  have hstable : (prefixWord ++ tailWord_3391768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391768).length < 2 ^ (prefixWord ++ tailWord_3391768).sum := by decide
  have hdescent : baseEnd_3391768 < baseStart_3391768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391775 : List Nat := [1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3391775 : Nat := 118140960795 + 3391775 * 2 ^ 59
def prefixEnd_3391775 : Nat := 4983230072969 + 3 ^ 40 * 3391775 * 2
def baseEnd_3391775 : Nat := 1741610846903572398414017

theorem tailTrace_3391775 : CollatzResearch.WordTrace tailWord_3391775 prefixEnd_3391775 1741610846903572398414017 := by
  unfold tailWord_3391775
  simp only [CollatzResearch.WordTrace]
  refine ⟨123708197287185918897144779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82472131524790612598096519 123708197287185918897144779)
  ·
    refine ⟨185562295930778878345717169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123708197287185918897144779 185562295930778878345717169)
    ·
      refine ⟨139171721948084158759287877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185562295930778878345717169 139171721948084158759287877)
      ·
        refine ⟨26094697865265779767366477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 139171721948084158759287877 26094697865265779767366477)
        ·
          refine ⟨9785511699474667412762429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26094697865265779767366477 9785511699474667412762429)
          ·
            refine ⟨3669566887303000279785911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9785511699474667412762429 3669566887303000279785911)
            ·
              refine ⟨5504350330954500419678867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3669566887303000279785911 5504350330954500419678867)
              ·
                refine ⟨8256525496431750629518301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5504350330954500419678867 8256525496431750629518301)
                ·
                  refine ⟨3096197061161906486069363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8256525496431750629518301 3096197061161906486069363)
                  ·
                    refine ⟨4644295591742859729104045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3096197061161906486069363 4644295591742859729104045)
                    ·
                      refine ⟨1741610846903572398414017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644295591742859729104045 1741610846903572398414017)
                      ·
                        rfl

theorem cell23_3391775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3391775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391775 prefixEnd_3391775 := by exact prefixLift 3391775
  have htrace : WordTrace (prefixWord ++ tailWord_3391775) baseStart_3391775 baseEnd_3391775 := by
    simpa [prefixWord, tailWord_3391775, baseEnd_3391775] using wordTrace_append hprefix tailTrace_3391775
  have hstable : (prefixWord ++ tailWord_3391775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391775).length < 2 ^ (prefixWord ++ tailWord_3391775).sum := by decide
  have hdescent : baseEnd_3391775 < baseStart_3391775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391804 : List Nat := [2, 2, 2, 2, 1, 2, 1, 11]
def baseStart_3391804 : Nat := 118140960795 + 3391804 * 2 ^ 59
def prefixEnd_3391804 : Nat := 4983230072969 + 3 ^ 40 * 3391804 * 2
def baseEnd_3391804 : Nat := 64504656957131584627829

theorem tailTrace_3391804 : CollatzResearch.WordTrace tailWord_3391804 prefixEnd_3391804 64504656957131584627829 := by
  unfold tailWord_3391804
  simp only [CollatzResearch.WordTrace]
  refine ⟨61854627502040428424975233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82472836669387237899966977 61854627502040428424975233)
  ·
    refine ⟨46390970626530321318731425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61854627502040428424975233 46390970626530321318731425)
    ·
      refine ⟨34793227969897740989048569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46390970626530321318731425 34793227969897740989048569)
      ·
        refine ⟨26094920977423305741786427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34793227969897740989048569 26094920977423305741786427)
        ·
          refine ⟨39142381466134958612679641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26094920977423305741786427 39142381466134958612679641)
          ·
            refine ⟨29356786099601218959509731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39142381466134958612679641 29356786099601218959509731)
            ·
              refine ⟨44035179149401828439264597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29356786099601218959509731 44035179149401828439264597)
              ·
                refine ⟨64504656957131584627829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 44035179149401828439264597 64504656957131584627829)
                ·
                  rfl

theorem cell23_3391804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 11].length) (baseStart_3391804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391804 prefixEnd_3391804 := by exact prefixLift 3391804
  have htrace : WordTrace (prefixWord ++ tailWord_3391804) baseStart_3391804 baseEnd_3391804 := by
    simpa [prefixWord, tailWord_3391804, baseEnd_3391804] using wordTrace_append hprefix tailTrace_3391804
  have hstable : (prefixWord ++ tailWord_3391804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391804).length < 2 ^ (prefixWord ++ tailWord_3391804).sum := by decide
  have hdescent : baseEnd_3391804 < baseStart_3391804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391812 : List Nat := [2, 3, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3391812 : Nat := 118140960795 + 3391812 * 2 ^ 59
def prefixEnd_3391812 : Nat := 4983230072969 + 3 ^ 40 * 3391812 * 2
def baseEnd_3391812 : Nat := 580543281895929584550449

theorem tailTrace_3391812 : CollatzResearch.WordTrace tailWord_3391812 prefixEnd_3391812 580543281895929584550449 := by
  unfold tailWord_3391812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61854773394025937108120845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82473031192034582810827793 61854773394025937108120845)
  ·
    refine ⟨23195540022759726415545317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61854773394025937108120845 23195540022759726415545317)
    ·
      refine ⟨4349163754267448702914747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23195540022759726415545317 4349163754267448702914747)
      ·
        refine ⟨6523745631401173054372121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4349163754267448702914747 6523745631401173054372121)
        ·
          refine ⟨4892809223550879790779091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6523745631401173054372121 4892809223550879790779091)
          ·
            refine ⟨7339213835326319686168637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892809223550879790779091 7339213835326319686168637)
            ·
              refine ⟨2752205188247369882313239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7339213835326319686168637 2752205188247369882313239)
              ·
                refine ⟨4128307782371054823469859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752205188247369882313239 4128307782371054823469859)
                ·
                  refine ⟨6192461673556582235204789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128307782371054823469859 6192461673556582235204789)
                  ·
                    refine ⟨580543281895929584550449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6192461673556582235204789 580543281895929584550449)
                    ·
                      rfl

theorem cell23_3391812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3391812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391812 prefixEnd_3391812 := by exact prefixLift 3391812
  have htrace : WordTrace (prefixWord ++ tailWord_3391812) baseStart_3391812 baseEnd_3391812 := by
    simpa [prefixWord, tailWord_3391812, baseEnd_3391812] using wordTrace_append hprefix tailTrace_3391812
  have hstable : (prefixWord ++ tailWord_3391812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391812).length < 2 ^ (prefixWord ++ tailWord_3391812).sum := by decide
  have hdescent : baseEnd_3391812 < baseStart_3391812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391831 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_3391831 : Nat := 118140960795 + 3391831 * 2 ^ 59
def prefixEnd_3391831 : Nat := 4983230072969 + 3 ^ 40 * 3391831 * 2
def baseEnd_3391831 : Nat := 1741639601820224179313759

theorem tailTrace_3391831 : CollatzResearch.WordTrace tailWord_3391831 prefixEnd_3391831 1741639601820224179313759 := by
  unfold tailWord_3391831
  simp only [CollatzResearch.WordTrace]
  refine ⟨123710239774983040461183347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82473493183322026974122231 123710239774983040461183347)
  ·
    refine ⟨185565359662474560691775021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123710239774983040461183347 185565359662474560691775021)
    ·
      refine ⟨69587009873427960259415633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185565359662474560691775021 69587009873427960259415633)
      ·
        refine ⟨52190257405070970194561725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69587009873427960259415633 52190257405070970194561725)
        ·
          refine ⟨19571346526901613822960647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52190257405070970194561725 19571346526901613822960647)
          ·
            refine ⟨29357019790352420734440971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19571346526901613822960647 29357019790352420734440971)
            ·
              refine ⟨44035529685528631101661457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29357019790352420734440971 44035529685528631101661457)
              ·
                refine ⟨33026647264146473326246093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44035529685528631101661457 33026647264146473326246093)
                ·
                  refine ⟨12384992724054927497342285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33026647264146473326246093 12384992724054927497342285)
                  ·
                    refine ⟨4644372271520597811503357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12384992724054927497342285 4644372271520597811503357)
                    ·
                      refine ⟨1741639601820224179313759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644372271520597811503357 1741639601820224179313759)
                      ·
                        rfl

theorem cell23_3391831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_3391831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391831 prefixEnd_3391831 := by exact prefixLift 3391831
  have htrace : WordTrace (prefixWord ++ tailWord_3391831) baseStart_3391831 baseEnd_3391831 := by
    simpa [prefixWord, tailWord_3391831, baseEnd_3391831] using wordTrace_append hprefix tailTrace_3391831
  have hstable : (prefixWord ++ tailWord_3391831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391831).length < 2 ^ (prefixWord ++ tailWord_3391831).sum := by decide
  have hdescent : baseEnd_3391831 < baseStart_3391831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391848 : List Nat := [2, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3391848 : Nat := 118140960795 + 3391848 * 2 ^ 59
def prefixEnd_3391848 : Nat := 4983230072969 + 3 ^ 40 * 3391848 * 2
def baseEnd_3391848 : Nat := 1741648330991350612801181

theorem tailTrace_3391848 : CollatzResearch.WordTrace tailWord_3391848 prefixEnd_3391848 1741648330991350612801181 := by
  unfold tailWord_3391848
  simp only [CollatzResearch.WordTrace]
  refine ⟨61855429907960726182276099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82473906543947634909701465 61855429907960726182276099)
  ·
    refine ⟨92783144861941089273414149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61855429907960726182276099 92783144861941089273414149)
    ·
      refine ⟨17396839661613954238765153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92783144861941089273414149 17396839661613954238765153)
      ·
        refine ⟨13047629746210465679073865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17396839661613954238765153 13047629746210465679073865)
        ·
          refine ⟨9785722309657849259305399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13047629746210465679073865 9785722309657849259305399)
          ·
            refine ⟨14678583464486773888958099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785722309657849259305399 14678583464486773888958099)
            ·
              refine ⟨22017875196730160833437149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14678583464486773888958099 22017875196730160833437149)
              ·
                refine ⟨8256703198773810312538931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22017875196730160833437149 8256703198773810312538931)
                ·
                  refine ⟨12385054798160715468808397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8256703198773810312538931 12385054798160715468808397)
                  ·
                    refine ⟨4644395549310268300803149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12385054798160715468808397 4644395549310268300803149)
                    ·
                      refine ⟨1741648330991350612801181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644395549310268300803149 1741648330991350612801181)
                      ·
                        rfl

theorem cell23_3391848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3391848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391848 prefixEnd_3391848 := by exact prefixLift 3391848
  have htrace : WordTrace (prefixWord ++ tailWord_3391848) baseStart_3391848 baseEnd_3391848 := by
    simpa [prefixWord, tailWord_3391848, baseEnd_3391848] using wordTrace_append hprefix tailTrace_3391848
  have hstable : (prefixWord ++ tailWord_3391848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391848).length < 2 ^ (prefixWord ++ tailWord_3391848).sum := by decide
  have hdescent : baseEnd_3391848 < baseStart_3391848 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391881 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_3391881 : Nat := 118140960795 + 3391881 * 2 ^ 59
def prefixEnd_3391881 : Nat := 4983230072969 + 3 ^ 40 * 3391881 * 2
def baseEnd_3391881 : Nat := 580555091950982994562843

theorem tailTrace_3391881 : CollatzResearch.WordTrace tailWord_3391881 prefixEnd_3391881 580555091950982994562843 := by
  unfold tailWord_3391881
  simp only [CollatzResearch.WordTrace]
  refine ⟨123712063424801899000503497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82474708949867932667002331 123712063424801899000503497)
  ·
    refine ⟨92784047568601424250377623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123712063424801899000503497 92784047568601424250377623)
    ·
      refine ⟨139176071352902136375566435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92784047568601424250377623 139176071352902136375566435)
      ·
        refine ⟨208764107029353204563349653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139176071352902136375566435 208764107029353204563349653)
        ·
          refine ⟨9785817517000931463907015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 208764107029353204563349653 9785817517000931463907015)
          ·
            refine ⟨14678726275501397195860523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9785817517000931463907015 14678726275501397195860523)
            ·
              refine ⟨22018089413252095793790785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14678726275501397195860523 22018089413252095793790785)
              ·
                refine ⟨16513567059939071845343089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22018089413252095793790785 16513567059939071845343089)
                ·
                  refine ⟨12385175294954303884007317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16513567059939071845343089 12385175294954303884007317)
                  ·
                    refine ⟨580555091950982994562843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12385175294954303884007317 580555091950982994562843)
                    ·
                      rfl

theorem cell23_3391881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_3391881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391881 prefixEnd_3391881 := by exact prefixLift 3391881
  have htrace : WordTrace (prefixWord ++ tailWord_3391881) baseStart_3391881 baseEnd_3391881 := by
    simpa [prefixWord, tailWord_3391881, baseEnd_3391881] using wordTrace_append hprefix tailTrace_3391881
  have hstable : (prefixWord ++ tailWord_3391881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391881).length < 2 ^ (prefixWord ++ tailWord_3391881).sum := by decide
  have hdescent : baseEnd_3391881 < baseStart_3391881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391882 : List Nat := [3, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3391882 : Nat := 118140960795 + 3391882 * 2 ^ 59
def prefixEnd_3391882 : Nat := 4983230072969 + 3 ^ 40 * 3391882 * 2
def baseEnd_3391882 : Nat := 1741665789333603479776025

theorem tailTrace_3391882 : CollatzResearch.WordTrace tailWord_3391882 prefixEnd_3391882 1741665789333603479776025 := by
  unfold tailWord_3391882
  simp only [CollatzResearch.WordTrace]
  refine ⟨30928024974449569042822475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82474733265198850780859933 30928024974449569042822475)
  ·
    refine ⟨46392037461674353564233713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30928024974449569042822475 46392037461674353564233713)
    ·
      refine ⟨34794028096255765173175285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46392037461674353564233713 34794028096255765173175285)
      ·
        refine ⟨3261940134023977984985183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34794028096255765173175285 3261940134023977984985183)
        ·
          refine ⟨4892910201035966977477775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3261940134023977984985183 4892910201035966977477775)
          ·
            refine ⟨7339365301553950466216663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4892910201035966977477775 7339365301553950466216663)
            ·
              refine ⟨11009047952330925699324995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339365301553950466216663 11009047952330925699324995)
              ·
                refine ⟨16513571928496388548987493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009047952330925699324995 16513571928496388548987493)
                ·
                  refine ⟨3096294736593072852935155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16513571928496388548987493 3096294736593072852935155)
                  ·
                    refine ⟨4644442104889609279402733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3096294736593072852935155 4644442104889609279402733)
                    ·
                      refine ⟨1741665789333603479776025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644442104889609279402733 1741665789333603479776025)
                      ·
                        rfl

theorem cell23_3391882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3391882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391882 prefixEnd_3391882 := by exact prefixLift 3391882
  have htrace : WordTrace (prefixWord ++ tailWord_3391882) baseStart_3391882 baseEnd_3391882 := by
    simpa [prefixWord, tailWord_3391882, baseEnd_3391882] using wordTrace_append hprefix tailTrace_3391882
  have hstable : (prefixWord ++ tailWord_3391882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391882).length < 2 ^ (prefixWord ++ tailWord_3391882).sum := by decide
  have hdescent : baseEnd_3391882 < baseStart_3391882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391956 : List Nat := [2, 4, 1, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3391956 : Nat := 118140960795 + 3391956 * 2 ^ 59
def prefixEnd_3391956 : Nat := 4983230072969 + 3 ^ 40 * 3391956 * 2
def baseEnd_3391956 : Nat := 1741703786902036190250685

theorem tailTrace_3391956 : CollatzResearch.WordTrace tailWord_3391956 prefixEnd_3391956 1741703786902036190250685 := by
  unfold tailWord_3391956
  simp only [CollatzResearch.WordTrace]
  refine ⟨61857399449765093404741861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82476532599686791206322481 61857399449765093404741861)
  ·
    refine ⟨11598262396830955013389099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61857399449765093404741861 11598262396830955013389099)
    ·
      refine ⟨17397393595246432520083649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11598262396830955013389099 17397393595246432520083649)
      ·
        refine ⟨13048045196434824390062737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17397393595246432520083649 13048045196434824390062737)
        ·
          refine ⟨9786033897326118292547053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13048045196434824390062737 9786033897326118292547053)
          ·
            refine ⟨3669762711497294359705145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9786033897326118292547053 3669762711497294359705145)
            ·
              refine ⟨2752322033622970769778859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3669762711497294359705145 2752322033622970769778859)
              ·
                refine ⟨4128483050434456154668289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752322033622970769778859 4128483050434456154668289)
                ·
                  refine ⟨3096362287825842116001217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4128483050434456154668289 3096362287825842116001217)
                  ·
                    refine ⟨2322271715869381587000913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096362287825842116001217 2322271715869381587000913)
                    ·
                      refine ⟨1741703786902036190250685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322271715869381587000913 1741703786902036190250685)
                      ·
                        rfl

theorem cell23_3391956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3391956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391956 prefixEnd_3391956 := by exact prefixLift 3391956
  have htrace : WordTrace (prefixWord ++ tailWord_3391956) baseStart_3391956 baseEnd_3391956 := by
    simpa [prefixWord, tailWord_3391956, baseEnd_3391956] using wordTrace_append hprefix tailTrace_3391956
  have hstable : (prefixWord ++ tailWord_3391956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391956).length < 2 ^ (prefixWord ++ tailWord_3391956).sum := by decide
  have hdescent : baseEnd_3391956 < baseStart_3391956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3391991 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_3391991 : Nat := 118140960795 + 3391991 * 2 ^ 59
def prefixEnd_3391991 : Nat := 4983230072969 + 3 ^ 40 * 3391991 * 2
def baseEnd_3391991 : Nat := 1741721758724943553313023

theorem tailTrace_3391991 : CollatzResearch.WordTrace tailWord_3391991 prefixEnd_3391991 1741721758724943553313023 := by
  unfold tailWord_3391991
  simp only [CollatzResearch.WordTrace]
  refine ⟨123716075454403387787007827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82477383636268925191338551 123716075454403387787007827)
  ·
    refine ⟨185574113181605081680511741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123716075454403387787007827 185574113181605081680511741)
    ·
      refine ⟨69590292443101905630191903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185574113181605081680511741 69590292443101905630191903)
      ·
        refine ⟨104385438664652858445287855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69590292443101905630191903 104385438664652858445287855)
        ·
          refine ⟨156578157996979287667931783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104385438664652858445287855 156578157996979287667931783)
          ·
            refine ⟨234867236995468931501897675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156578157996979287667931783 234867236995468931501897675)
            ·
              refine ⟨352300855493203397252846513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234867236995468931501897675 352300855493203397252846513)
              ·
                refine ⟨264225641619902547939634885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 352300855493203397252846513 264225641619902547939634885)
                ·
                  refine ⟨49542307803731727738681541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 264225641619902547939634885 49542307803731727738681541)
                  ·
                    refine ⟨9289182713199698951002789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49542307803731727738681541 9289182713199698951002789)
                    ·
                      refine ⟨1741721758724943553313023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9289182713199698951002789 1741721758724943553313023)
                      ·
                        rfl

theorem cell23_3391991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_3391991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3391991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3391991 prefixEnd_3391991 := by exact prefixLift 3391991
  have htrace : WordTrace (prefixWord ++ tailWord_3391991) baseStart_3391991 baseEnd_3391991 := by
    simpa [prefixWord, tailWord_3391991, baseEnd_3391991] using wordTrace_append hprefix tailTrace_3391991
  have hstable : (prefixWord ++ tailWord_3391991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3391991).length < 2 ^ (prefixWord ++ tailWord_3391991).sum := by decide
  have hdescent : baseEnd_3391991 < baseStart_3391991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3391991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392052 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3392052 : Nat := 118140960795 + 3392052 * 2 ^ 59
def prefixEnd_3392052 : Nat := 4983230072969 + 3 ^ 40 * 3392052 * 2
def baseEnd_3392052 : Nat := 193528120116096423850027

theorem tailTrace_3392052 : CollatzResearch.WordTrace tailWord_3392052 prefixEnd_3392052 193528120116096423850027 := by
  unfold tailWord_3392052
  simp only [CollatzResearch.WordTrace]
  refine ⟨61859150153591197602489205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82478866871454930136652273 61859150153591197602489205)
  ·
    refine ⟨5799295326899174775233363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61859150153591197602489205 5799295326899174775233363)
    ·
      refine ⟨8698942990348762162850045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5799295326899174775233363 8698942990348762162850045)
      ·
        refine ⟨3262103621380785811068767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8698942990348762162850045 3262103621380785811068767)
        ·
          refine ⟨4893155432071178716603151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262103621380785811068767 4893155432071178716603151)
          ·
            refine ⟨7339733148106768074904727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893155432071178716603151 7339733148106768074904727)
            ·
              refine ⟨11009599722160152112357091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339733148106768074904727 11009599722160152112357091)
              ·
                refine ⟨16514399583240228168535637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11009599722160152112357091 16514399583240228168535637)
                ·
                  refine ⟨193528120116096423850027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16514399583240228168535637 193528120116096423850027)
                  ·
                    rfl

theorem cell23_3392052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3392052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392052 prefixEnd_3392052 := by exact prefixLift 3392052
  have htrace : WordTrace (prefixWord ++ tailWord_3392052) baseStart_3392052 baseEnd_3392052 := by
    simpa [prefixWord, tailWord_3392052, baseEnd_3392052] using wordTrace_append hprefix tailTrace_3392052
  have hstable : (prefixWord ++ tailWord_3392052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392052).length < 2 ^ (prefixWord ++ tailWord_3392052).sum := by decide
  have hdescent : baseEnd_3392052 < baseStart_3392052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392055 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_3392055 : Nat := 118140960795 + 3392055 * 2 ^ 59
def prefixEnd_3392055 : Nat := 4983230072969 + 3 ^ 40 * 3392055 * 2
def baseEnd_3392055 : Nat := 1741754621486831302912729

theorem tailTrace_3392055 : CollatzResearch.WordTrace tailWord_3392055 prefixEnd_3392055 1741754621486831302912729 := by
  unfold tailWord_3392055
  simp only [CollatzResearch.WordTrace]
  refine ⟨123718409726171526717337619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82478939817447684478225079 123718409726171526717337619)
  ·
    refine ⟨185577614589257290076006429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123718409726171526717337619 185577614589257290076006429)
    ·
      refine ⟨69591605470971483778502411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185577614589257290076006429 69591605470971483778502411)
      ·
        refine ⟨104387408206457225667753617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69591605470971483778502411 104387408206457225667753617)
        ·
          refine ⟨78290556154842919250815213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104387408206457225667753617 78290556154842919250815213)
          ·
            refine ⟨29358958558066094719055705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78290556154842919250815213 29358958558066094719055705)
            ·
              refine ⟨22019218918549571039291779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29358958558066094719055705 22019218918549571039291779)
              ·
                refine ⟨33028828377824356558937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22019218918549571039291779 33028828377824356558937669)
                ·
                  refine ⟨6192905320842066854800813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33028828377824356558937669 6192905320842066854800813)
                  ·
                    refine ⟨2322339495315775070550305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6192905320842066854800813 2322339495315775070550305)
                    ·
                      refine ⟨1741754621486831302912729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322339495315775070550305 1741754621486831302912729)
                      ·
                        rfl

theorem cell23_3392055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_3392055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392055 prefixEnd_3392055 := by exact prefixLift 3392055
  have htrace : WordTrace (prefixWord ++ tailWord_3392055) baseStart_3392055 baseEnd_3392055 := by
    simpa [prefixWord, tailWord_3392055, baseEnd_3392055] using wordTrace_append hprefix tailTrace_3392055
  have hstable : (prefixWord ++ tailWord_3392055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392055).length < 2 ^ (prefixWord ++ tailWord_3392055).sum := by decide
  have hdescent : baseEnd_3392055 < baseStart_3392055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392085 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_3392085 : Nat := 118140960795 + 3392085 * 2 ^ 59
def prefixEnd_3392085 : Nat := 4983230072969 + 3 ^ 40 * 3392085 * 2
def baseEnd_3392085 : Nat := 1741770025906466185537591

theorem tailTrace_3392085 : CollatzResearch.WordTrace tailWord_3392085 prefixEnd_3392085 1741770025906466185537591 := by
  unfold tailWord_3392085
  simp only [CollatzResearch.WordTrace]
  refine ⟨123719503916062841840929709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82479669277375227893953139 123719503916062841840929709)
  ·
    refine ⟨46394813968523565690348641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123719503916062841840929709 46394813968523565690348641)
    ·
      refine ⟨34796110476392674267761481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46394813968523565690348641 34796110476392674267761481)
      ·
        refine ⟨26097082857294505700821111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34796110476392674267761481 26097082857294505700821111)
        ·
          refine ⟨39145624285941758551231667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26097082857294505700821111 39145624285941758551231667)
          ·
            refine ⟨58718436428912637826847501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39145624285941758551231667 58718436428912637826847501)
            ·
              refine ⟨22019413660842239185067813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58718436428912637826847501 22019413660842239185067813)
              ·
                refine ⟨4128640061407919847200215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22019413660842239185067813 4128640061407919847200215)
                ·
                  refine ⟨6192960092111879770800323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4128640061407919847200215 6192960092111879770800323)
                  ·
                    refine ⟨9289440138167819656200485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6192960092111879770800323 9289440138167819656200485)
                    ·
                      refine ⟨1741770025906466185537591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9289440138167819656200485 1741770025906466185537591)
                      ·
                        rfl

theorem cell23_3392085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_3392085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392085 prefixEnd_3392085 := by exact prefixLift 3392085
  have htrace : WordTrace (prefixWord ++ tailWord_3392085) baseStart_3392085 baseEnd_3392085 := by
    simpa [prefixWord, tailWord_3392085, baseEnd_3392085] using wordTrace_append hprefix tailTrace_3392085
  have hstable : (prefixWord ++ tailWord_3392085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392085).length < 2 ^ (prefixWord ++ tailWord_3392085).sum := by decide
  have hdescent : baseEnd_3392085 < baseStart_3392085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392119 : List Nat := [1, 1, 3, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_3392119 : Nat := 118140960795 + 3392119 * 2 ^ 59
def prefixEnd_3392119 : Nat := 4983230072969 + 3 ^ 40 * 3392119 * 2
def baseEnd_3392119 : Nat := 1741787484248719052512435

theorem tailTrace_3392119 : CollatzResearch.WordTrace tailWord_3392119 prefixEnd_3392119 1741787484248719052512435 := by
  unfold tailWord_3392119
  simp only [CollatzResearch.WordTrace]
  refine ⟨123720743997939665647667411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82480495998626443765111607 123720743997939665647667411)
  ·
    refine ⟨185581115996909498471501117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123720743997939665647667411 185581115996909498471501117)
    ·
      refine ⟨69592918498841061926812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185581115996909498471501117 69592918498841061926812919)
      ·
        refine ⟨104389377748261592890219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69592918498841061926812919 104389377748261592890219379)
        ·
          refine ⟨156584066622392389335329069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104389377748261592890219379 156584066622392389335329069)
          ·
            refine ⟨58719024983397146000748401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156584066622392389335329069 58719024983397146000748401)
            ·
              refine ⟨44039268737547859500561301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58719024983397146000748401 44039268737547859500561301)
              ·
                refine ⟨2064340722072555914088811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44039268737547859500561301 2064340722072555914088811)
                ·
                  refine ⟨3096511083108833871133217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064340722072555914088811 3096511083108833871133217)
                  ·
                    refine ⟨2322383312331625403349913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096511083108833871133217 2322383312331625403349913)
                    ·
                      refine ⟨1741787484248719052512435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322383312331625403349913 1741787484248719052512435)
                      ·
                        rfl

theorem cell23_3392119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_3392119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392119 prefixEnd_3392119 := by exact prefixLift 3392119
  have htrace : WordTrace (prefixWord ++ tailWord_3392119) baseStart_3392119 baseEnd_3392119 := by
    simpa [prefixWord, tailWord_3392119, baseEnd_3392119] using wordTrace_append hprefix tailTrace_3392119
  have hstable : (prefixWord ++ tailWord_3392119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392119).length < 2 ^ (prefixWord ++ tailWord_3392119).sum := by decide
  have hdescent : baseEnd_3392119 < baseStart_3392119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392125 : List Nat := [1, 4, 1, 1, 5, 1, 2, 8]
def baseStart_3392125 : Nat := 118140960795 + 3392125 * 2 ^ 59
def prefixEnd_3392125 : Nat := 4983230072969 + 3 ^ 40 * 3392125 * 2
def baseEnd_3392125 : Nat := 64510761671579482556941

theorem tailTrace_3392125 : CollatzResearch.WordTrace tailWord_3392125 prefixEnd_3392125 64510761671579482556941 := by
  unfold tailWord_3392125
  simp only [CollatzResearch.WordTrace]
  refine ⟨123720962835917928672385829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82480641890611952448257219 123720962835917928672385829)
  ·
    refine ⟨23197680531734611626072343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123720962835917928672385829 23197680531734611626072343)
    ·
      refine ⟨34796520797601917439108515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23197680531734611626072343 34796520797601917439108515)
      ·
        refine ⟨52194781196402876158662773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34796520797601917439108515 52194781196402876158662773)
        ·
          refine ⟨4893260737162769639874635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52194781196402876158662773 4893260737162769639874635)
          ·
            refine ⟨7339891105744154459811953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893260737162769639874635 7339891105744154459811953)
            ·
              refine ⟨5504918329308115844858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7339891105744154459811953 5504918329308115844858965)
              ·
                refine ⟨64510761671579482556941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5504918329308115844858965 64510761671579482556941)
                ·
                  rfl

theorem cell23_3392125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 8].length) (baseStart_3392125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392125 prefixEnd_3392125 := by exact prefixLift 3392125
  have htrace : WordTrace (prefixWord ++ tailWord_3392125) baseStart_3392125 baseEnd_3392125 := by
    simpa [prefixWord, tailWord_3392125, baseEnd_3392125] using wordTrace_append hprefix tailTrace_3392125
  have hstable : (prefixWord ++ tailWord_3392125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392125).length < 2 ^ (prefixWord ++ tailWord_3392125).sum := by decide
  have hdescent : baseEnd_3392125 < baseStart_3392125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392135 : List Nat := [1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3392135 : Nat := 118140960795 + 3392135 * 2 ^ 59
def prefixEnd_3392135 : Nat := 4983230072969 + 3 ^ 40 * 3392135 * 2
def baseEnd_3392135 : Nat := 1741795699939190989912361

theorem tailTrace_3392135 : CollatzResearch.WordTrace tailWord_3392135 prefixEnd_3392135 1741795699939190989912361 := by
  unfold tailWord_3392135
  simp only [CollatzResearch.WordTrace]
  refine ⟨123721327565881700380249859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82480885043921133586833239 123721327565881700380249859)
  ·
    refine ⟨185581991348822550570374789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123721327565881700380249859 185581991348822550570374789)
    ·
      refine ⟨34796623377904228231945273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185581991348822550570374789 34796623377904228231945273)
      ·
        refine ⟨26097467533428171173958955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34796623377904228231945273 26097467533428171173958955)
        ·
          refine ⟨39146201300142256760938433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26097467533428171173958955 39146201300142256760938433)
          ·
            refine ⟨29359650975106692570703825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39146201300142256760938433 29359650975106692570703825)
            ·
              refine ⟨22019738231330019428027869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29359650975106692570703825 22019738231330019428027869)
              ·
                refine ⟨8257401836748757285510451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22019738231330019428027869 8257401836748757285510451)
                ·
                  refine ⟨12386102755123135928265677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257401836748757285510451 12386102755123135928265677)
                  ·
                    refine ⟨4644788533171175973099629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12386102755123135928265677 4644788533171175973099629)
                    ·
                      refine ⟨1741795699939190989912361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644788533171175973099629 1741795699939190989912361)
                      ·
                        rfl

theorem cell23_3392135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3392135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392135 prefixEnd_3392135 := by exact prefixLift 3392135
  have htrace : WordTrace (prefixWord ++ tailWord_3392135) baseStart_3392135 baseEnd_3392135 := by
    simpa [prefixWord, tailWord_3392135, baseEnd_3392135] using wordTrace_append hprefix tailTrace_3392135
  have hstable : (prefixWord ++ tailWord_3392135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392135).length < 2 ^ (prefixWord ++ tailWord_3392135).sum := by decide
  have hdescent : baseEnd_3392135 < baseStart_3392135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392170 : List Nat := [3, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_3392170 : Nat := 118140960795 + 3392170 * 2 ^ 59
def prefixEnd_3392170 : Nat := 4983230072969 + 3 ^ 40 * 3392170 * 2
def baseEnd_3392170 : Nat := 1741813671762098352974701

theorem tailTrace_3392170 : CollatzResearch.WordTrace tailWord_3392170 prefixEnd_3392170 1741813671762098352974701 := by
  unfold tailWord_3392170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30930651030188725339443491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82481736080503267571849309 30930651030188725339443491)
  ·
    refine ⟨46395976545283088009165237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30930651030188725339443491 46395976545283088009165237)
    ·
      refine ⟨4349622801120289500859241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46395976545283088009165237 4349622801120289500859241)
      ·
        refine ⟨3262217100840217125644431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4349622801120289500859241 3262217100840217125644431)
        ·
          refine ⟨4893325651260325688466647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262217100840217125644431 4893325651260325688466647)
          ·
            refine ⟨7339988476890488532699971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893325651260325688466647 7339988476890488532699971)
            ·
              refine ⟨11009982715335732799049957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7339988476890488532699971 11009982715335732799049957)
              ·
                refine ⟨2064371759125449899821867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11009982715335732799049957 2064371759125449899821867)
                ·
                  refine ⟨3096557638688174849732801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064371759125449899821867 3096557638688174849732801)
                  ·
                    refine ⟨2322418229016131137299601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096557638688174849732801 2322418229016131137299601)
                    ·
                      refine ⟨1741813671762098352974701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322418229016131137299601 1741813671762098352974701)
                      ·
                        rfl

theorem cell23_3392170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_3392170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392170 prefixEnd_3392170 := by exact prefixLift 3392170
  have htrace : WordTrace (prefixWord ++ tailWord_3392170) baseStart_3392170 baseEnd_3392170 := by
    simpa [prefixWord, tailWord_3392170, baseEnd_3392170] using wordTrace_append hprefix tailTrace_3392170
  have hstable : (prefixWord ++ tailWord_3392170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392170).length < 2 ^ (prefixWord ++ tailWord_3392170).sum := by decide
  have hdescent : baseEnd_3392170 < baseStart_3392170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392192 : List Nat := [2, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2]
def baseStart_3392192 : Nat := 118140960795 + 3392192 * 2 ^ 59
def prefixEnd_3392192 : Nat := 4983230072969 + 3 ^ 40 * 3392192 * 2
def baseEnd_3392192 : Nat := 1741824968336497266899599

theorem tailTrace_3392192 : CollatzResearch.WordTrace tailWord_3392192 prefixEnd_3392192 1741824968336497266899599 := by
  unfold tailWord_3392192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61861703263337599557537415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82482271017783466076716553 61861703263337599557537415)
  ·
    refine ⟨92792554895006399336306123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61861703263337599557537415 92792554895006399336306123)
    ·
      refine ⟨139188832342509599004459185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92792554895006399336306123 139188832342509599004459185)
      ·
        refine ⟨104391624256882199253344389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139188832342509599004459185 104391624256882199253344389)
        ·
          refine ⟨19573429548165412360002073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104391624256882199253344389 19573429548165412360002073)
          ·
            refine ⟨14680072161124059270001555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19573429548165412360002073 14680072161124059270001555)
            ·
              refine ⟨22020108241686088905002333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14680072161124059270001555 22020108241686088905002333)
              ·
                refine ⟨8257540590632283339375875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22020108241686088905002333 8257540590632283339375875)
                ·
                  refine ⟨12386310885948425009063813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8257540590632283339375875 12386310885948425009063813)
                  ·
                    refine ⟨2322433291115329689199465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12386310885948425009063813 2322433291115329689199465)
                    ·
                      refine ⟨1741824968336497266899599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322433291115329689199465 1741824968336497266899599)
                      ·
                        rfl

theorem cell23_3392192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_3392192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392192 prefixEnd_3392192 := by exact prefixLift 3392192
  have htrace : WordTrace (prefixWord ++ tailWord_3392192) baseStart_3392192 baseEnd_3392192 := by
    simpa [prefixWord, tailWord_3392192, baseEnd_3392192] using wordTrace_append hprefix tailTrace_3392192
  have hstable : (prefixWord ++ tailWord_3392192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392192).length < 2 ^ (prefixWord ++ tailWord_3392192).sum := by decide
  have hdescent : baseEnd_3392192 < baseStart_3392192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392232 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 7]
def baseStart_3392232 : Nat := 118140960795 + 3392232 * 2 ^ 59
def prefixEnd_3392232 : Nat := 4983230072969 + 3 ^ 40 * 3392232 * 2
def baseEnd_3392232 : Nat := 193538389729186345599935

theorem tailTrace_3392232 : CollatzResearch.WordTrace tailWord_3392232 prefixEnd_3392232 193538389729186345599935 := by
  unfold tailWord_3392232
  simp only [CollatzResearch.WordTrace]
  refine ⟨61862432723265142973265475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82483243631020190631020633 61862432723265142973265475)
  ·
    refine ⟨92793649084897714459898213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61862432723265142973265475 92793649084897714459898213)
    ·
      refine ⟨17398809203418321461230915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92793649084897714459898213 17398809203418321461230915)
      ·
        refine ⟨26098213805127482191846373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17398809203418321461230915 26098213805127482191846373)
        ·
          refine ⟨4893415088461402910971195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26098213805127482191846373 4893415088461402910971195)
          ·
            refine ⟨7340122632692104366456793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4893415088461402910971195 7340122632692104366456793)
            ·
              refine ⟨5505091974519078274842595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340122632692104366456793 5505091974519078274842595)
              ·
                refine ⟨8257637961778617412263893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505091974519078274842595 8257637961778617412263893)
                ·
                  refine ⟨193538389729186345599935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8257637961778617412263893 193538389729186345599935)
                  ·
                    rfl

theorem cell23_3392232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 7].length) (baseStart_3392232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392232 prefixEnd_3392232 := by exact prefixLift 3392232
  have htrace : WordTrace (prefixWord ++ tailWord_3392232) baseStart_3392232 baseEnd_3392232 := by
    simpa [prefixWord, tailWord_3392232, baseEnd_3392232] using wordTrace_append hprefix tailTrace_3392232
  have hstable : (prefixWord ++ tailWord_3392232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392232).length < 2 ^ (prefixWord ++ tailWord_3392232).sum := by decide
  have hdescent : baseEnd_3392232 < baseStart_3392232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392242 : List Nat := [3, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3392242 : Nat := 118140960795 + 3392242 * 2 ^ 59
def prefixEnd_3392242 : Nat := 4983230072969 + 3 ^ 40 * 3392242 * 2
def baseEnd_3392242 : Nat := 1741850642369222071274369

theorem tailTrace_3392242 : CollatzResearch.WordTrace tailWord_3392242 prefixEnd_3392242 1741850642369222071274369 := by
  unfold tailWord_3392242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931307544123514413598745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82483486784329371769596653 30931307544123514413598745)
  ·
    refine ⟨23198480658092635810199059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30931307544123514413598745 23198480658092635810199059)
    ·
      refine ⟨34797720987138953715298589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23198480658092635810199059 34797720987138953715298589)
      ·
        refine ⟨13049145370177107643236971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34797720987138953715298589 13049145370177107643236971)
        ·
          refine ⟨19573718055265661464855457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13049145370177107643236971 19573718055265661464855457)
          ·
            refine ⟨14680288541449246098641593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19573718055265661464855457 14680288541449246098641593)
            ·
              refine ⟨11010216406086934573981195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14680288541449246098641593 11010216406086934573981195)
              ·
                refine ⟨16515324609130401860971793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11010216406086934573981195 16515324609130401860971793)
                ·
                  refine ⟨12386493456847801395728845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16515324609130401860971793 12386493456847801395728845)
                  ·
                    refine ⟨4644935046317925523398317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12386493456847801395728845 4644935046317925523398317)
                    ·
                      refine ⟨1741850642369222071274369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4644935046317925523398317 1741850642369222071274369)
                      ·
                        rfl

theorem cell23_3392242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3392242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392242 prefixEnd_3392242 := by exact prefixLift 3392242
  have htrace : WordTrace (prefixWord ++ tailWord_3392242) baseStart_3392242 baseEnd_3392242 := by
    simpa [prefixWord, tailWord_3392242, baseEnd_3392242] using wordTrace_append hprefix tailTrace_3392242
  have hstable : (prefixWord ++ tailWord_3392242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392242).length < 2 ^ (prefixWord ++ tailWord_3392242).sum := by decide
  have hdescent : baseEnd_3392242 < baseStart_3392242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392265 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_3392265 : Nat := 118140960795 + 3392265 * 2 ^ 59
def prefixEnd_3392265 : Nat := 4983230072969 + 3 ^ 40 * 3392265 * 2
def baseEnd_3392265 : Nat := 1741862452424275481286763

theorem tailTrace_3392265 : CollatzResearch.WordTrace tailWord_3392265 prefixEnd_3392265 1741862452424275481286763 := by
  unfold tailWord_3392265
  simp only [CollatzResearch.WordTrace]
  refine ⟨123726069055410732582482249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82484046036940488388321499 123726069055410732582482249)
  ·
    refine ⟨92794551791558049436861687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123726069055410732582482249 92794551791558049436861687)
    ·
      refine ⟨139191827687337074155292531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92794551791558049436861687 139191827687337074155292531)
      ·
        refine ⟨208787741531005611232938797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139191827687337074155292531 208787741531005611232938797)
        ·
          refine ⟨78295403074127104212352049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 208787741531005611232938797 78295403074127104212352049)
          ·
            refine ⟨58721552305595328159264037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78295403074127104212352049 58721552305595328159264037)
            ·
              refine ⟨11010291057299124029862007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58721552305595328159264037 11010291057299124029862007)
              ·
                refine ⟨16515436585948686044793011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11010291057299124029862007 16515436585948686044793011)
                ·
                  refine ⟨24773154878923029067189517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16515436585948686044793011 24773154878923029067189517)
                  ·
                    refine ⟨9289933079596135900196069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24773154878923029067189517 9289933079596135900196069)
                    ·
                      refine ⟨1741862452424275481286763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9289933079596135900196069 1741862452424275481286763)
                      ·
                        rfl

theorem cell23_3392265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_3392265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392265 prefixEnd_3392265 := by exact prefixLift 3392265
  have htrace : WordTrace (prefixWord ++ tailWord_3392265) baseStart_3392265 baseEnd_3392265 := by
    simpa [prefixWord, tailWord_3392265, baseEnd_3392265] using wordTrace_append hprefix tailTrace_3392265
  have hstable : (prefixWord ++ tailWord_3392265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392265).length < 2 ^ (prefixWord ++ tailWord_3392265).sum := by decide
  have hdescent : baseEnd_3392265 < baseStart_3392265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392282 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3392282 : Nat := 118140960795 + 3392282 * 2 ^ 59
def prefixEnd_3392282 : Nat := 4983230072969 + 3 ^ 40 * 3392282 * 2
def baseEnd_3392282 : Nat := 1741871181595401914774185

theorem tailTrace_3392282 : CollatzResearch.WordTrace tailWord_3392282 prefixEnd_3392282 1741871181595401914774185 := by
  unfold tailWord_3392282
  simp only [CollatzResearch.WordTrace]
  refine ⟨30931672274087286121462775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82484459397566096323900733 30931672274087286121462775)
  ·
    refine ⟨46397508411130929182194163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30931672274087286121462775 46397508411130929182194163)
    ·
      refine ⟨69596262616696393773291245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46397508411130929182194163 69596262616696393773291245)
      ·
        refine ⟨26098598481261147664984217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69596262616696393773291245 26098598481261147664984217)
        ·
          refine ⟨19573948860945860748738163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26098598481261147664984217 19573948860945860748738163)
          ·
            refine ⟨29360923291418791123107245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19573948860945860748738163 29360923291418791123107245)
            ·
              refine ⟨11010346234282046671165217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29360923291418791123107245 11010346234282046671165217)
              ·
                refine ⟨8257759675711535003373913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11010346234282046671165217 8257759675711535003373913)
                ·
                  refine ⟨6193319756783651252530435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8257759675711535003373913 6193319756783651252530435)
                  ·
                    refine ⟨9289979635175476878795653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6193319756783651252530435 9289979635175476878795653)
                    ·
                      refine ⟨1741871181595401914774185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9289979635175476878795653 1741871181595401914774185)
                      ·
                        rfl

theorem cell23_3392282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3392282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392282 prefixEnd_3392282 := by exact prefixLift 3392282
  have htrace : WordTrace (prefixWord ++ tailWord_3392282) baseStart_3392282 baseEnd_3392282 := by
    simpa [prefixWord, tailWord_3392282, baseEnd_3392282] using wordTrace_append hprefix tailTrace_3392282
  have hstable : (prefixWord ++ tailWord_3392282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392282).length < 2 ^ (prefixWord ++ tailWord_3392282).sum := by decide
  have hdescent : baseEnd_3392282 < baseStart_3392282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392319 : List Nat := [1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_3392319 : Nat := 118140960795 + 3392319 * 2 ^ 59
def prefixEnd_3392319 : Nat := 4983230072969 + 3 ^ 40 * 3392319 * 2
def baseEnd_3392319 : Nat := 1741890180379618270011515

theorem tailTrace_3392319 : CollatzResearch.WordTrace tailWord_3392319 prefixEnd_3392319 1741890180379618270011515 := by
  unfold tailWord_3392319
  simp only [CollatzResearch.WordTrace]
  refine ⟨123728038597215099804948011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82485359064810066536632007 123728038597215099804948011)
  ·
    refine ⟨185592057895822649707422017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123728038597215099804948011 185592057895822649707422017)
    ·
      refine ⟨139194043421866987280566513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185592057895822649707422017 139194043421866987280566513)
      ·
        refine ⟨104395532566400240460424885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139194043421866987280566513 104395532566400240460424885)
        ·
          refine ⟨9787081178100022543164833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104395532566400240460424885 9787081178100022543164833)
          ·
            refine ⟨7340310883575016907373625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9787081178100022543164833 7340310883575016907373625)
            ·
              refine ⟨5505233162681262680530219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7340310883575016907373625 5505233162681262680530219)
              ·
                refine ⟨8257849744021894020795329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5505233162681262680530219 8257849744021894020795329)
                ·
                  refine ⟨6193387308016420515596497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8257849744021894020795329 6193387308016420515596497)
                  ·
                    refine ⟨4645040481012315386697373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6193387308016420515596497 4645040481012315386697373)
                    ·
                      refine ⟨1741890180379618270011515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645040481012315386697373 1741890180379618270011515)
                      ·
                        rfl

theorem cell23_3392319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_3392319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392319 prefixEnd_3392319 := by exact prefixLift 3392319
  have htrace : WordTrace (prefixWord ++ tailWord_3392319) baseStart_3392319 baseEnd_3392319 := by
    simpa [prefixWord, tailWord_3392319, baseEnd_3392319] using wordTrace_append hprefix tailTrace_3392319
  have hstable : (prefixWord ++ tailWord_3392319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392319).length < 2 ^ (prefixWord ++ tailWord_3392319).sum := by decide
  have hdescent : baseEnd_3392319 < baseStart_3392319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392343 : List Nat := [1, 1, 3, 2, 4, 3, 2, 2, 1, 4]
def baseStart_3392343 : Nat := 118140960795 + 3392343 * 2 ^ 59
def prefixEnd_3392343 : Nat := 4983230072969 + 3 ^ 40 * 3392343 * 2
def baseEnd_3392343 : Nat := 580634167971775392037135

theorem tailTrace_3392343 : CollatzResearch.WordTrace tailWord_3392343 prefixEnd_3392343 580634167971775392037135 := by
  unfold tailWord_3392343
  simp only [CollatzResearch.WordTrace]
  refine ⟨123728913949128151903821683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82485942632752101269214455 123728913949128151903821683)
  ·
    refine ⟨185593370923692227855732525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123728913949128151903821683 185593370923692227855732525)
    ·
      refine ⟨69597514096384585445899697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185593370923692227855732525 69597514096384585445899697)
      ·
        refine ⟨52198135572288439084424773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69597514096384585445899697 52198135572288439084424773)
        ·
          refine ⟨9787150419804082328329645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52198135572288439084424773 9787150419804082328329645)
          ·
            refine ⟨3670181407426530873123617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9787150419804082328329645 3670181407426530873123617)
            ·
              refine ⟨2752636055569898154842713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670181407426530873123617 2752636055569898154842713)
              ·
                refine ⟨2064477041677423616132035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2752636055569898154842713 2064477041677423616132035)
                ·
                  refine ⟨3096715562516135424198053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064477041677423616132035 3096715562516135424198053)
                  ·
                    refine ⟨580634167971775392037135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096715562516135424198053 580634167971775392037135)
                    ·
                      rfl

theorem cell23_3392343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_3392343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392343 prefixEnd_3392343 := by exact prefixLift 3392343
  have htrace : WordTrace (prefixWord ++ tailWord_3392343) baseStart_3392343 baseEnd_3392343 := by
    simpa [prefixWord, tailWord_3392343, baseEnd_3392343] using wordTrace_append hprefix tailTrace_3392343
  have hstable : (prefixWord ++ tailWord_3392343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392343).length < 2 ^ (prefixWord ++ tailWord_3392343).sum := by decide
  have hdescent : baseEnd_3392343 < baseStart_3392343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392389 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_3392389 : Nat := 118140960795 + 3392389 * 2 ^ 59
def prefixEnd_3392389 : Nat := 4983230072969 + 3 ^ 40 * 3392389 * 2
def baseEnd_3392389 : Nat := 1741926124025432996136193

theorem tailTrace_3392389 : CollatzResearch.WordTrace tailWord_3392389 prefixEnd_3392389 1741926124025432996136193 := by
  unfold tailWord_3392389
  simp only [CollatzResearch.WordTrace]
  refine ⟨123730591706961501759996221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82487061137974334506664147 123730591706961501759996221)
  ·
    refine ⟨46398971890110563159998583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123730591706961501759996221 46398971890110563159998583)
    ·
      refine ⟨69598457835165844739997875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46398971890110563159998583 69598457835165844739997875)
      ·
        refine ⟨104397686752748767109996813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69598457835165844739997875 104397686752748767109996813)
        ·
          refine ⟨39149132532280787666248805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104397686752748767109996813 39149132532280787666248805)
          ·
            refine ⟨7340462349802647687421651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39149132532280787666248805 7340462349802647687421651)
            ·
              refine ⟨11010693524703971531132477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7340462349802647687421651 11010693524703971531132477)
              ·
                refine ⟨4129010071763989324174679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11010693524703971531132477 4129010071763989324174679)
                ·
                  refine ⟨6193515107645983986262019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129010071763989324174679 6193515107645983986262019)
                  ·
                    refine ⟨9290272661468975979393029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6193515107645983986262019 9290272661468975979393029)
                    ·
                      refine ⟨1741926124025432996136193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9290272661468975979393029 1741926124025432996136193)
                      ·
                        rfl

theorem cell23_3392389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_3392389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392389 prefixEnd_3392389 := by exact prefixLift 3392389
  have htrace : WordTrace (prefixWord ++ tailWord_3392389) baseStart_3392389 baseEnd_3392389 := by
    simpa [prefixWord, tailWord_3392389, baseEnd_3392389] using wordTrace_append hprefix tailTrace_3392389
  have hstable : (prefixWord ++ tailWord_3392389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392389).length < 2 ^ (prefixWord ++ tailWord_3392389).sum := by decide
  have hdescent : baseEnd_3392389 < baseStart_3392389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392439 : List Nat := [1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_3392439 : Nat := 118140960795 + 3392439 * 2 ^ 59
def prefixEnd_3392439 : Nat := 4983230072969 + 3 ^ 40 * 3392439 * 2
def baseEnd_3392439 : Nat := 1741951798058157800510963

theorem tailTrace_3392439 : CollatzResearch.WordTrace tailWord_3392439 prefixEnd_3392439 1741951798058157800510963 := by
  unfold tailWord_3392439
  simp only [CollatzResearch.WordTrace]
  refine ⟨123732415356780360299316371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82488276904520240199544247 123732415356780360299316371)
  ·
    refine ⟨185598623035170540448974557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123732415356780360299316371 185598623035170540448974557)
    ·
      refine ⟨69599483638188952668365459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185598623035170540448974557 69599483638188952668365459)
      ·
        refine ⟨104399225457283429002548189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69599483638188952668365459 104399225457283429002548189)
        ·
          refine ⟨39149709546481285875955571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104399225457283429002548189 39149709546481285875955571)
          ·
            refine ⟨58724564319721928813933357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39149709546481285875955571 58724564319721928813933357)
            ·
              refine ⟨22021711619895723305225009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58724564319721928813933357 22021711619895723305225009)
              ·
                refine ⟨16516283714921792478918757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22021711619895723305225009 16516283714921792478918757)
                ·
                  refine ⟨3096803196547836089797267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16516283714921792478918757 3096803196547836089797267)
                  ·
                    refine ⟨4645204794821754134695901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3096803196547836089797267 4645204794821754134695901)
                    ·
                      refine ⟨1741951798058157800510963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645204794821754134695901 1741951798058157800510963)
                      ·
                        rfl

theorem cell23_3392439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_3392439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392439 prefixEnd_3392439 := by exact prefixLift 3392439
  have htrace : WordTrace (prefixWord ++ tailWord_3392439) baseStart_3392439 baseEnd_3392439 := by
    simpa [prefixWord, tailWord_3392439, baseEnd_3392439] using wordTrace_append hprefix tailTrace_3392439
  have hstable : (prefixWord ++ tailWord_3392439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392439).length < 2 ^ (prefixWord ++ tailWord_3392439).sum := by decide
  have hdescent : baseEnd_3392439 < baseStart_3392439 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392440 : List Nat := [2, 1, 2, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_3392440 : Nat := 118140960795 + 3392440 * 2 ^ 59
def prefixEnd_3392440 : Nat := 4983230072969 + 3 ^ 40 * 3392440 * 2
def baseEnd_3392440 : Nat := 1741952311538812296598459

theorem tailTrace_3392440 : CollatzResearch.WordTrace tailWord_3392440 prefixEnd_3392440 1741952311538812296598459 := by
  unfold tailWord_3392440
  simp only [CollatzResearch.WordTrace]
  refine ⟨61866225914888368735051387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82488301219851158313401849 61866225914888368735051387)
  ·
    refine ⟨92799338872332553102577081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61866225914888368735051387 92799338872332553102577081)
    ·
      refine ⟨69599504154249414826932811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92799338872332553102577081 69599504154249414826932811)
      ·
        refine ⟨104399256231374122240399217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69599504154249414826932811 104399256231374122240399217)
        ·
          refine ⟨78299442173530591680299413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104399256231374122240399217 78299442173530591680299413)
          ·
            refine ⟨3670286351884246485014035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78299442173530591680299413 3670286351884246485014035)
            ·
              refine ⟨5505429527826369727521053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3670286351884246485014035 5505429527826369727521053)
              ·
                refine ⟨2064536072934888647820395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5505429527826369727521053 2064536072934888647820395)
                ·
                  refine ⟨3096804109402332971730593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064536072934888647820395 3096804109402332971730593)
                  ·
                    refine ⟨2322603082051749728797945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096804109402332971730593 2322603082051749728797945)
                    ·
                      refine ⟨1741952311538812296598459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322603082051749728797945 1741952311538812296598459)
                      ·
                        rfl

theorem cell23_3392440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_3392440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392440 prefixEnd_3392440 := by exact prefixLift 3392440
  have htrace : WordTrace (prefixWord ++ tailWord_3392440) baseStart_3392440 baseEnd_3392440 := by
    simpa [prefixWord, tailWord_3392440, baseEnd_3392440] using wordTrace_append hprefix tailTrace_3392440
  have hstable : (prefixWord ++ tailWord_3392440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392440).length < 2 ^ (prefixWord ++ tailWord_3392440).sum := by decide
  have hdescent : baseEnd_3392440 < baseStart_3392440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392473 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 2, 1, 3]
def baseStart_3392473 : Nat := 118140960795 + 3392473 * 2 ^ 59
def prefixEnd_3392473 : Nat := 4983230072969 + 3 ^ 40 * 3392473 * 2
def baseEnd_3392473 : Nat := 1741969256400410667485807

theorem tailTrace_3392473 : CollatzResearch.WordTrace tailWord_3392473 prefixEnd_3392473 1741969256400410667485807 := by
  unfold tailWord_3392473
  simp only [CollatzResearch.WordTrace]
  refine ⟨123733655438657184106054073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82489103625771456070702715 123733655438657184106054073)
  ·
    refine ⟨92800241578992888079540555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123733655438657184106054073 92800241578992888079540555)
    ·
      refine ⟨139200362368489332119310833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92800241578992888079540555 139200362368489332119310833)
      ·
        refine ⟨104400271776366999089483125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139200362368489332119310833 104400271776366999089483125)
        ·
          refine ⟨9787525479034406164639043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104400271776366999089483125 9787525479034406164639043)
          ·
            refine ⟨14681288218551609246958565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9787525479034406164639043 14681288218551609246958565)
            ·
              refine ⟨2752741540978426733804731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14681288218551609246958565 2752741540978426733804731)
              ·
                refine ⟨4129112311467640100707097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752741540978426733804731 4129112311467640100707097)
                ·
                  refine ⟨3096834233600730075530323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129112311467640100707097 3096834233600730075530323)
                  ·
                    refine ⟨4645251350401095113295485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3096834233600730075530323 4645251350401095113295485)
                    ·
                      refine ⟨1741969256400410667485807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645251350401095113295485 1741969256400410667485807)
                      ·
                        rfl

theorem cell23_3392473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 1, 3].length) (baseStart_3392473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392473 prefixEnd_3392473 := by exact prefixLift 3392473
  have htrace : WordTrace (prefixWord ++ tailWord_3392473) baseStart_3392473 baseEnd_3392473 := by
    simpa [prefixWord, tailWord_3392473, baseEnd_3392473] using wordTrace_append hprefix tailTrace_3392473
  have hstable : (prefixWord ++ tailWord_3392473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392473).length < 2 ^ (prefixWord ++ tailWord_3392473).sum := by decide
  have hdescent : baseEnd_3392473 < baseStart_3392473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392492 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3392492 : Nat := 118140960795 + 3392492 * 2 ^ 59
def prefixEnd_3392492 : Nat := 4983230072969 + 3 ^ 40 * 3392492 * 2
def baseEnd_3392492 : Nat := 1741979012532846093148219

theorem tailTrace_3392492 : CollatzResearch.WordTrace tailWord_3392492 prefixEnd_3392492 1741979012532846093148219 := by
  unfold tailWord_3392492
  simp only [CollatzResearch.WordTrace]
  refine ⟨61867174212794175175497865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82489565617058900233997153 61867174212794175175497865)
  ·
    refine ⟨46400380659595631381623399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61867174212794175175497865 46400380659595631381623399)
    ·
      refine ⟨69600570989393447072435099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46400380659595631381623399 69600570989393447072435099)
      ·
        refine ⟨104400856484090170608652649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69600570989393447072435099 104400856484090170608652649)
        ·
          refine ⟨78300642363067627956489487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104400856484090170608652649 78300642363067627956489487)
          ·
            refine ⟨117450963544601441934734231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78300642363067627956489487 117450963544601441934734231)
            ·
              refine ⟨176176445316902162902101347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117450963544601441934734231 176176445316902162902101347)
              ·
                refine ⟨264264667975353244353152021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176176445316902162902101347 264264667975353244353152021)
                ·
                  refine ⟨12387406311344683329054001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 264264667975353244353152021 12387406311344683329054001)
                  ·
                    refine ⟨9290554733508512496790501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12387406311344683329054001 9290554733508512496790501)
                    ·
                      refine ⟨1741979012532846093148219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9290554733508512496790501 1741979012532846093148219)
                      ·
                        rfl

theorem cell23_3392492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3392492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392492 prefixEnd_3392492 := by exact prefixLift 3392492
  have htrace : WordTrace (prefixWord ++ tailWord_3392492) baseStart_3392492 baseEnd_3392492 := by
    simpa [prefixWord, tailWord_3392492, baseEnd_3392492] using wordTrace_append hprefix tailTrace_3392492
  have hstable : (prefixWord ++ tailWord_3392492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392492).length < 2 ^ (prefixWord ++ tailWord_3392492).sum := by decide
  have hdescent : baseEnd_3392492 < baseStart_3392492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392513 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 2, 2, 2]
def baseStart_3392513 : Nat := 118140960795 + 3392513 * 2 ^ 59
def prefixEnd_3392513 : Nat := 4983230072969 + 3 ^ 40 * 3392513 * 2
def baseEnd_3392513 : Nat := 1741989795626590510985623

theorem tailTrace_3392513 : CollatzResearch.WordTrace tailWord_3392513 prefixEnd_3392513 1741989795626590510985623 := by
  unfold tailWord_3392513
  simp only [CollatzResearch.WordTrace]
  refine ⟨123735114358512270937510193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82490076239008180625006795 123735114358512270937510193)
  ·
    refine ⟨92801335768884203203132645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123735114358512270937510193 92801335768884203203132645)
    ·
      refine ⟨17400250456665788100587371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92801335768884203203132645 17400250456665788100587371)
      ·
        refine ⟨26100375684998682150881057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400250456665788100587371 26100375684998682150881057)
        ·
          refine ⟨19575281763749011613160793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26100375684998682150881057 19575281763749011613160793)
          ·
            refine ⟨14681461322811758709870595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19575281763749011613160793 14681461322811758709870595)
            ·
              refine ⟨22022191984217638064805893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14681461322811758709870595 22022191984217638064805893)
              ·
                refine ⟨4129160997040807137151105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22022191984217638064805893 4129160997040807137151105)
                ·
                  refine ⟨3096870747780605352863329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129160997040807137151105 3096870747780605352863329)
                  ·
                    refine ⟨2322653060835454014647497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3096870747780605352863329 2322653060835454014647497)
                    ·
                      refine ⟨1741989795626590510985623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322653060835454014647497 1741989795626590510985623)
                      ·
                        rfl

theorem cell23_3392513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_3392513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392513 prefixEnd_3392513 := by exact prefixLift 3392513
  have htrace : WordTrace (prefixWord ++ tailWord_3392513) baseStart_3392513 baseEnd_3392513 := by
    simpa [prefixWord, tailWord_3392513, baseEnd_3392513] using wordTrace_append hprefix tailTrace_3392513
  have hstable : (prefixWord ++ tailWord_3392513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392513).length < 2 ^ (prefixWord ++ tailWord_3392513).sum := by decide
  have hdescent : baseEnd_3392513 < baseStart_3392513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392586 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_3392586 : Nat := 118140960795 + 3392586 * 2 ^ 59
def prefixEnd_3392586 : Nat := 4983230072969 + 3 ^ 40 * 3392586 * 2
def baseEnd_3392586 : Nat := 1742027279714368725372787

theorem tailTrace_3392586 : CollatzResearch.WordTrace tailWord_3392586 prefixEnd_3392586 1742027279714368725372787 := by
  unfold tailWord_3392586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30934444221811951101229403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82491851258165202936611741 30934444221811951101229403)
  ·
    refine ⟨46401666332717926651844105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30934444221811951101229403 46401666332717926651844105)
    ·
      refine ⟨34801249749538444988883079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46401666332717926651844105 34801249749538444988883079)
      ·
        refine ⟨52201874624307667483324619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34801249749538444988883079 52201874624307667483324619)
        ·
          refine ⟨78302811936461501224986929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52201874624307667483324619 78302811936461501224986929)
          ·
            refine ⟨58727108952346125918740197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78302811936461501224986929 58727108952346125918740197)
            ·
              refine ⟨11011332928564898609763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58727108952346125918740197 11011332928564898609763787)
              ·
                refine ⟨16516999392847347914645681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11011332928564898609763787 16516999392847347914645681)
                ·
                  refine ⟨12387749544635510935984261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16516999392847347914645681 12387749544635510935984261)
                  ·
                    refine ⟨2322703039619158300497049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12387749544635510935984261 2322703039619158300497049)
                    ·
                      refine ⟨1742027279714368725372787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322703039619158300497049 1742027279714368725372787)
                      ·
                        rfl

theorem cell23_3392586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_3392586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392586 prefixEnd_3392586 := by exact prefixLift 3392586
  have htrace : WordTrace (prefixWord ++ tailWord_3392586) baseStart_3392586 baseEnd_3392586 := by
    simpa [prefixWord, tailWord_3392586, baseEnd_3392586] using wordTrace_append hprefix tailTrace_3392586
  have hstable : (prefixWord ++ tailWord_3392586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392586).length < 2 ^ (prefixWord ++ tailWord_3392586).sum := by decide
  have hdescent : baseEnd_3392586 < baseStart_3392586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392596 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3392596 : Nat := 118140960795 + 3392596 * 2 ^ 59
def prefixEnd_3392596 : Nat := 4983230072969 + 3 ^ 40 * 3392596 * 2
def baseEnd_3392596 : Nat := 580677471506971228749247

theorem tailTrace_3392596 : CollatzResearch.WordTrace tailWord_3392596 prefixEnd_3392596 580677471506971228749247 := by
  unfold tailWord_3392596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61869070808605788056390821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82492094411474384075187761 61869070808605788056390821)
  ·
    refine ⟨11600450776613585260573279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61869070808605788056390821 11600450776613585260573279)
    ·
      refine ⟨17400676164920377890859919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600450776613585260573279 17400676164920377890859919)
      ·
        refine ⟨26101014247380566836289879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17400676164920377890859919 26101014247380566836289879)
        ·
          refine ⟨39151521371070850254434819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26101014247380566836289879 39151521371070850254434819)
          ·
            refine ⟨58727282056606275381652229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39151521371070850254434819 58727282056606275381652229)
            ·
              refine ⟨11011365385613676634059793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58727282056606275381652229 11011365385613676634059793)
              ·
                refine ⟨8258524039210257475544845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11011365385613676634059793 8258524039210257475544845)
                ·
                  refine ⟨3096946514703846553329317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8258524039210257475544845 3096946514703846553329317)
                  ·
                    refine ⟨580677471506971228749247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3096946514703846553329317 580677471506971228749247)
                    ·
                      rfl

theorem cell23_3392596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3392596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392596 prefixEnd_3392596 := by exact prefixLift 3392596
  have htrace : WordTrace (prefixWord ++ tailWord_3392596) baseStart_3392596 baseEnd_3392596 := by
    simpa [prefixWord, tailWord_3392596, baseEnd_3392596] using wordTrace_append hprefix tailTrace_3392596
  have hstable : (prefixWord ++ tailWord_3392596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392596).length < 2 ^ (prefixWord ++ tailWord_3392596).sum := by decide
  have hdescent : baseEnd_3392596 < baseStart_3392596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392663 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_3392663 : Nat := 118140960795 + 3392663 * 2 ^ 59
def prefixEnd_3392663 : Nat := 4983230072969 + 3 ^ 40 * 3392663 * 2
def baseEnd_3392663 : Nat := 1742066817724764924109933

theorem tailTrace_3392663 : CollatzResearch.WordTrace tailWord_3392663 prefixEnd_3392663 1742066817724764924109933 := by
  unfold tailWord_3392663
  simp only [CollatzResearch.WordTrace]
  refine ⟨123740585307968846555470643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82493723538645897703647095 123740585307968846555470643)
  ·
    refine ⟨185610877961953269833205965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123740585307968846555470643 185610877961953269833205965)
    ·
      refine ⟨69604079235732476187452237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185610877961953269833205965 69604079235732476187452237)
      ·
        refine ⟨26101529713399678570294589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69604079235732476187452237 26101529713399678570294589)
        ·
          refine ⟨9788073642524879463860471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26101529713399678570294589 9788073642524879463860471)
          ·
            refine ⟨14682110463787319195790707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788073642524879463860471 14682110463787319195790707)
            ·
              refine ⟨22023165695680978793686061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14682110463787319195790707 22023165695680978793686061)
              ·
                refine ⟨8258687135880367047632273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22023165695680978793686061 8258687135880367047632273)
                ·
                  refine ⟨6194015351910275285724205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8258687135880367047632273 6194015351910275285724205)
                  ·
                    refine ⟨2322755756966353232146577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6194015351910275285724205 2322755756966353232146577)
                    ·
                      refine ⟨1742066817724764924109933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322755756966353232146577 1742066817724764924109933)
                      ·
                        rfl

theorem cell23_3392663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_3392663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392663 prefixEnd_3392663 := by exact prefixLift 3392663
  have htrace : WordTrace (prefixWord ++ tailWord_3392663) baseStart_3392663 baseEnd_3392663 := by
    simpa [prefixWord, tailWord_3392663, baseEnd_3392663] using wordTrace_append hprefix tailTrace_3392663
  have hstable : (prefixWord ++ tailWord_3392663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392663).length < 2 ^ (prefixWord ++ tailWord_3392663).sum := by decide
  have hdescent : baseEnd_3392663 < baseStart_3392663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392673 : List Nat := [1, 2, 3, 3, 1, 1, 5, 1, 1, 5]
def baseStart_3392673 : Nat := 118140960795 + 3392673 * 2 ^ 59
def prefixEnd_3392673 : Nat := 4983230072969 + 3 ^ 40 * 3392673 * 2
def baseEnd_3392673 : Nat := 580690650843769961661629

theorem tailTrace_3392673 : CollatzResearch.WordTrace tailWord_3392673 prefixEnd_3392673 580690650843769961661629 := by
  unfold tailWord_3392673
  simp only [CollatzResearch.WordTrace]
  refine ⟨123740950037932618263334673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82493966691955078842223115 123740950037932618263334673)
  ·
    refine ⟨92805712528449463697501005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123740950037932618263334673 92805712528449463697501005)
    ·
      refine ⟨34802142198168548886562877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92805712528449463697501005 34802142198168548886562877)
      ·
        refine ⟨13050803324313205832461079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34802142198168548886562877 13050803324313205832461079)
        ·
          refine ⟨19576204986469808748691619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13050803324313205832461079 19576204986469808748691619)
          ·
            refine ⟨29364307479704713123037429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19576204986469808748691619 29364307479704713123037429)
            ·
              refine ⟨2752903826222316855284759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29364307479704713123037429 2752903826222316855284759)
              ·
                refine ⟨4129355739333475282927139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752903826222316855284759 4129355739333475282927139)
                ·
                  refine ⟨6194033609000212924390709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129355739333475282927139 6194033609000212924390709)
                  ·
                    refine ⟨580690650843769961661629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6194033609000212924390709 580690650843769961661629)
                    ·
                      rfl

theorem cell23_3392673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 1, 1, 5].length) (baseStart_3392673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392673 prefixEnd_3392673 := by exact prefixLift 3392673
  have htrace : WordTrace (prefixWord ++ tailWord_3392673) baseStart_3392673 baseEnd_3392673 := by
    simpa [prefixWord, tailWord_3392673, baseEnd_3392673] using wordTrace_append hprefix tailTrace_3392673
  have hstable : (prefixWord ++ tailWord_3392673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392673).length < 2 ^ (prefixWord ++ tailWord_3392673).sum := by decide
  have hdescent : baseEnd_3392673 < baseStart_3392673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392724 : List Nat := [2, 4, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_3392724 : Nat := 118140960795 + 3392724 * 2 ^ 59
def prefixEnd_3392724 : Nat := 4983230072969 + 3 ^ 40 * 3392724 * 2
def baseEnd_3392724 : Nat := 580699380014896395149051

theorem tailTrace_3392724 : CollatzResearch.WordTrace tailWord_3392724 prefixEnd_3392724 580699380014896395149051 := by
  unfold tailWord_3392724
  simp only [CollatzResearch.WordTrace]
  refine ⟨61871405080373926986720613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82495206773831902648960817 61871405080373926986720613)
  ·
    refine ⟨11600888452570111310010115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61871405080373926986720613 11600888452570111310010115)
    ·
      refine ⟨17401332678855166965015173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11600888452570111310010115 17401332678855166965015173)
      ·
        refine ⟨3262749877285343805940345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17401332678855166965015173 3262749877285343805940345)
        ·
          refine ⟨2447062407964007854455259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3262749877285343805940345 2447062407964007854455259)
          ·
            refine ⟨3670593611946011781682889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447062407964007854455259 3670593611946011781682889)
            ·
              refine ⟨2752945208959508836262167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3670593611946011781682889 2752945208959508836262167)
              ·
                refine ⟨4129417813439263254393251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2752945208959508836262167 4129417813439263254393251)
                ·
                  refine ⟨6194126720158894881589877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129417813439263254393251 6194126720158894881589877)
                  ·
                    refine ⟨580699380014896395149051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6194126720158894881589877 580699380014896395149051)
                    ·
                      rfl

theorem cell23_3392724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_3392724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392724 prefixEnd_3392724 := by exact prefixLift 3392724
  have htrace : WordTrace (prefixWord ++ tailWord_3392724) baseStart_3392724 baseEnd_3392724 := by
    simpa [prefixWord, tailWord_3392724, baseEnd_3392724] using wordTrace_append hprefix tailTrace_3392724
  have hstable : (prefixWord ++ tailWord_3392724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392724).length < 2 ^ (prefixWord ++ tailWord_3392724).sum := by decide
  have hdescent : baseEnd_3392724 < baseStart_3392724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392796 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3392796 : Nat := 118140960795 + 3392796 * 2 ^ 59
def prefixEnd_3392796 : Nat := 4983230072969 + 3 ^ 40 * 3392796 * 2
def baseEnd_3392796 : Nat := 1742135110651812903746821

theorem tailTrace_3392796 : CollatzResearch.WordTrace tailWord_3392796 prefixEnd_3392796 1742135110651812903746821 := by
  unfold tailWord_3392796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61872718108243505135031121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82496957477658006846708161 61872718108243505135031121)
  ·
    refine ⟨46404538581182628851273341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61872718108243505135031121 46404538581182628851273341)
    ·
      refine ⟨17401701967943485819227503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46404538581182628851273341 17401701967943485819227503)
      ·
        refine ⟨26102552951915228728841255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17401701967943485819227503 26102552951915228728841255)
        ·
          refine ⟨39153829427872843093261883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26102552951915228728841255 39153829427872843093261883)
          ·
            refine ⟨58730744141809264639892825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39153829427872843093261883 58730744141809264639892825)
            ·
              refine ⟨44048058106356948479919619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58730744141809264639892825 44048058106356948479919619)
              ·
                refine ⟨66072087159535422719879429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44048058106356948479919619 66072087159535422719879429)
                ·
                  refine ⟨12388516342412891759977393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66072087159535422719879429 12388516342412891759977393)
                  ·
                    refine ⟨9291387256809668819983045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12388516342412891759977393 9291387256809668819983045)
                    ·
                      refine ⟨1742135110651812903746821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9291387256809668819983045 1742135110651812903746821)
                      ·
                        rfl

theorem cell23_3392796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3392796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392796 prefixEnd_3392796 := by exact prefixLift 3392796
  have htrace : WordTrace (prefixWord ++ tailWord_3392796) baseStart_3392796 baseEnd_3392796 := by
    simpa [prefixWord, tailWord_3392796, baseEnd_3392796] using wordTrace_append hprefix tailTrace_3392796
  have hstable : (prefixWord ++ tailWord_3392796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392796).length < 2 ^ (prefixWord ++ tailWord_3392796).sum := by decide
  have hdescent : baseEnd_3392796 < baseStart_3392796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392816 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3]
def baseStart_3392816 : Nat := 118140960795 + 3392816 * 2 ^ 59
def prefixEnd_3392816 : Nat := 4983230072969 + 3 ^ 40 * 3392816 * 2
def baseEnd_3392816 : Nat := 1742145380264902825496729

theorem tailTrace_3392816 : CollatzResearch.WordTrace tailWord_3392816 prefixEnd_3392816 1742145380264902825496729 := by
  unfold tailWord_3392816
  simp only [CollatzResearch.WordTrace]
  refine ⟨61873082838207276842895151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82497443784276369123860201 61873082838207276842895151)
  ·
    refine ⟨92809624257310915264342727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61873082838207276842895151 92809624257310915264342727)
    ·
      refine ⟨139214436385966372896514091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92809624257310915264342727 139214436385966372896514091)
      ·
        refine ⟨208821654578949559344771137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139214436385966372896514091 208821654578949559344771137)
        ·
          refine ⟨156616240934212169508578353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208821654578949559344771137 156616240934212169508578353)
          ·
            refine ⟨117462180700659127131433765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156616240934212169508578353 117462180700659127131433765)
            ·
              refine ⟨22024158881373586337143831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 117462180700659127131433765 22024158881373586337143831)
              ·
                refine ⟨33036238322060379505715747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22024158881373586337143831 33036238322060379505715747)
                ·
                  refine ⟨49554357483090569258573621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33036238322060379505715747 49554357483090569258573621)
                  ·
                    refine ⟨4645721014039740867991277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49554357483090569258573621 4645721014039740867991277)
                    ·
                      refine ⟨1742145380264902825496729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645721014039740867991277 1742145380264902825496729)
                      ·
                        rfl

theorem cell23_3392816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 5, 3].length) (baseStart_3392816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392816 prefixEnd_3392816 := by exact prefixLift 3392816
  have htrace : WordTrace (prefixWord ++ tailWord_3392816) baseStart_3392816 baseEnd_3392816 := by
    simpa [prefixWord, tailWord_3392816, baseEnd_3392816] using wordTrace_append hprefix tailTrace_3392816
  have hstable : (prefixWord ++ tailWord_3392816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392816).length < 2 ^ (prefixWord ++ tailWord_3392816).sum := by decide
  have hdescent : baseEnd_3392816 < baseStart_3392816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392817 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 2, 2, 2]
def baseStart_3392817 : Nat := 118140960795 + 3392817 * 2 ^ 59
def prefixEnd_3392817 : Nat := 4983230072969 + 3 ^ 40 * 3392817 * 2
def baseEnd_3392817 : Nat := 1742145893745557321584225

theorem tailTrace_3392817 : CollatzResearch.WordTrace tailWord_3392817 prefixEnd_3392817 1742145893745557321584225 := by
  unfold tailWord_3392817
  simp only [CollatzResearch.WordTrace]
  refine ⟨123746202149410930856576705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82497468099607287237717803 123746202149410930856576705)
  ·
    refine ⟨92809651612058198142432529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123746202149410930856576705 92809651612058198142432529)
    ·
      refine ⟨69607238709043648606824397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92809651612058198142432529 69607238709043648606824397)
      ·
        refine ⟨26102714515891368227559149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69607238709043648606824397 26102714515891368227559149)
        ·
          refine ⟨9788517943459263085334681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26102714515891368227559149 9788517943459263085334681)
          ·
            refine ⟨7341388457594447314001011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9788517943459263085334681 7341388457594447314001011)
            ·
              refine ⟨11012082686391670971001517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341388457594447314001011 11012082686391670971001517)
              ·
                refine ⟨4129531007396876614125569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11012082686391670971001517 4129531007396876614125569)
                ·
                  refine ⟨3097148255547657460594177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4129531007396876614125569 3097148255547657460594177)
                  ·
                    refine ⟨2322861191660743095445633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3097148255547657460594177 2322861191660743095445633)
                    ·
                      refine ⟨1742145893745557321584225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322861191660743095445633 1742145893745557321584225)
                      ·
                        rfl

theorem cell23_3392817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_3392817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392817 prefixEnd_3392817 := by exact prefixLift 3392817
  have htrace : WordTrace (prefixWord ++ tailWord_3392817) baseStart_3392817 baseEnd_3392817 := by
    simpa [prefixWord, tailWord_3392817, baseEnd_3392817] using wordTrace_append hprefix tailTrace_3392817
  have hstable : (prefixWord ++ tailWord_3392817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392817).length < 2 ^ (prefixWord ++ tailWord_3392817).sum := by decide
  have hdescent : baseEnd_3392817 < baseStart_3392817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392838 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_3392838 : Nat := 118140960795 + 3392838 * 2 ^ 59
def prefixEnd_3392838 : Nat := 4983230072969 + 3 ^ 40 * 3392838 * 2
def baseEnd_3392838 : Nat := 1742156676839301739421629

theorem tailTrace_3392838 : CollatzResearch.WordTrace tailWord_3392838 prefixEnd_3392838 1742156676839301739421629 := by
  unfold tailWord_3392838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3867092752572964107596599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 82497978721556567628727445 3867092752572964107596599)
  ·
    refine ⟨5800639128859446161394899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3867092752572964107596599 5800639128859446161394899)
    ·
      refine ⟨8700958693289169242092349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5800639128859446161394899 8700958693289169242092349)
      ·
        refine ⟨3262859509983438465784631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8700958693289169242092349 3262859509983438465784631)
        ·
          refine ⟨4894289264975157698676947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3262859509983438465784631 4894289264975157698676947)
          ·
            refine ⟨7341433897462736548015421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894289264975157698676947 7341433897462736548015421)
            ·
              refine ⟨2753037711548526205505783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7341433897462736548015421 2753037711548526205505783)
              ·
                refine ⟨4129556567322789308258675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753037711548526205505783 4129556567322789308258675)
                ·
                  refine ⟨6194334850984183962388013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129556567322789308258675 6194334850984183962388013)
                  ·
                    refine ⟨2322875569119068985895505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6194334850984183962388013 2322875569119068985895505)
                    ·
                      refine ⟨1742156676839301739421629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2322875569119068985895505 1742156676839301739421629)
                      ·
                        rfl

theorem cell23_3392838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_3392838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392838 prefixEnd_3392838 := by exact prefixLift 3392838
  have htrace : WordTrace (prefixWord ++ tailWord_3392838) baseStart_3392838 baseEnd_3392838 := by
    simpa [prefixWord, tailWord_3392838, baseEnd_3392838] using wordTrace_append hprefix tailTrace_3392838
  have hstable : (prefixWord ++ tailWord_3392838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392838).length < 2 ^ (prefixWord ++ tailWord_3392838).sum := by decide
  have hdescent : baseEnd_3392838 < baseStart_3392838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392846 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3392846 : Nat := 118140960795 + 3392846 * 2 ^ 59
def prefixEnd_3392846 : Nat := 4983230072969 + 3 ^ 40 * 3392846 * 2
def baseEnd_3392846 : Nat := 1742160784684537708121591

theorem tailTrace_3392846 : CollatzResearch.WordTrace tailWord_3392846 prefixEnd_3392846 1742160784684537708121591 := by
  unfold tailWord_3392846
  simp only [CollatzResearch.WordTrace]
  refine ⟨15468407483288233601172799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82498173244203912539588261 15468407483288233601172799)
  ·
    refine ⟨23202611224932350401759199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15468407483288233601172799 23202611224932350401759199)
    ·
      refine ⟨34803916837398525602638799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23202611224932350401759199 34803916837398525602638799)
      ·
        refine ⟨52205875256097788403958199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34803916837398525602638799 52205875256097788403958199)
        ·
          refine ⟨78308812884146682605937299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52205875256097788403958199 78308812884146682605937299)
          ·
            refine ⟨117463219326220023908905949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78308812884146682605937299 117463219326220023908905949)
            ·
              refine ⟨44048707247332508965839731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117463219326220023908905949 44048707247332508965839731)
              ·
                refine ⟨66073060870998763448759597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44048707247332508965839731 66073060870998763448759597)
                ·
                  refine ⟨24777397826624536293284849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66073060870998763448759597 24777397826624536293284849)
                  ·
                    refine ⟨18583048369968402219963637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24777397826624536293284849 18583048369968402219963637)
                    ·
                      refine ⟨1742160784684537708121591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18583048369968402219963637 1742160784684537708121591)
                      ·
                        rfl

theorem cell23_3392846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3392846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392846 prefixEnd_3392846 := by exact prefixLift 3392846
  have htrace : WordTrace (prefixWord ++ tailWord_3392846) baseStart_3392846 baseEnd_3392846 := by
    simpa [prefixWord, tailWord_3392846, baseEnd_3392846] using wordTrace_append hprefix tailTrace_3392846
  have hstable : (prefixWord ++ tailWord_3392846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392846).length < 2 ^ (prefixWord ++ tailWord_3392846).sum := by decide
  have hdescent : baseEnd_3392846 < baseStart_3392846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392853 : List Nat := [1, 3, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_3392853 : Nat := 118140960795 + 3392853 * 2 ^ 59
def prefixEnd_3392853 : Nat := 4983230072969 + 3 ^ 40 * 3392853 * 2
def baseEnd_3392853 : Nat := 580721459683039726911353

theorem tailTrace_3392853 : CollatzResearch.WordTrace tailWord_3392853 prefixEnd_3392853 580721459683039726911353 := by
  unfold tailWord_3392853
  simp only [CollatzResearch.WordTrace]
  refine ⟨123747515177280509004887213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82498343451520339336591475 123747515177280509004887213)
  ·
    refine ⟨46405318191480190876832705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123747515177280509004887213 46405318191480190876832705)
    ·
      refine ⟨34803988643610143157624529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46405318191480190876832705 34803988643610143157624529)
      ·
        refine ⟨26102991482707607368218397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34803988643610143157624529 26102991482707607368218397)
        ·
          refine ⟨9788621806015352763081899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26102991482707607368218397 9788621806015352763081899)
          ·
            refine ⟨14682932709023029144622849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9788621806015352763081899 14682932709023029144622849)
            ·
              refine ⟨11012199531767271858467137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14682932709023029144622849 11012199531767271858467137)
              ·
                refine ⟨8259149648825453893850353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012199531767271858467137 8259149648825453893850353)
                ·
                  refine ⟨6194362236619090420387765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8259149648825453893850353 6194362236619090420387765)
                  ·
                    refine ⟨580721459683039726911353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6194362236619090420387765 580721459683039726911353)
                    ·
                      rfl

theorem cell23_3392853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_3392853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392853 prefixEnd_3392853 := by exact prefixLift 3392853
  have htrace : WordTrace (prefixWord ++ tailWord_3392853) baseStart_3392853 baseEnd_3392853 := by
    simpa [prefixWord, tailWord_3392853, baseEnd_3392853] using wordTrace_append hprefix tailTrace_3392853
  have hstable : (prefixWord ++ tailWord_3392853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392853).length < 2 ^ (prefixWord ++ tailWord_3392853).sum := by decide
  have hdescent : baseEnd_3392853 < baseStart_3392853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392893 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_3392893 : Nat := 118140960795 + 3392893 * 2 ^ 59
def prefixEnd_3392893 : Nat := 4983230072969 + 3 ^ 40 * 3392893 * 2
def baseEnd_3392893 : Nat := 1742184918275299024233875

theorem tailTrace_3392893 : CollatzResearch.WordTrace tailWord_3392893 prefixEnd_3392893 1742184918275299024233875 := by
  unfold tailWord_3392893
  simp only [CollatzResearch.WordTrace]
  refine ⟨123748974097135595836343333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82499316064757063890895555 123748974097135595836343333)
  ·
    refine ⟨23202932643212924219314375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 123748974097135595836343333 23202932643212924219314375)
    ·
      refine ⟨34804398964819386328971563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23202932643212924219314375 34804398964819386328971563)
      ·
        refine ⟨52206598447229079493457345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34804398964819386328971563 52206598447229079493457345)
        ·
          refine ⟨39154948835421809620093009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52206598447229079493457345 39154948835421809620093009)
          ·
            refine ⟨29366211626566357215069757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39154948835421809620093009 29366211626566357215069757)
            ·
              refine ⟨11012329359962383955651159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29366211626566357215069757 11012329359962383955651159)
              ·
                refine ⟨16518494039943575933476739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012329359962383955651159 16518494039943575933476739)
                ·
                  refine ⟨24777741059915363900215109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16518494039943575933476739 24777741059915363900215109)
                  ·
                    refine ⟨4645826448734130731290333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24777741059915363900215109 4645826448734130731290333)
                    ·
                      refine ⟨1742184918275299024233875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645826448734130731290333 1742184918275299024233875)
                      ·
                        rfl

theorem cell23_3392893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_3392893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392893 prefixEnd_3392893 := by exact prefixLift 3392893
  have htrace : WordTrace (prefixWord ++ tailWord_3392893) baseStart_3392893 baseEnd_3392893 := by
    simpa [prefixWord, tailWord_3392893, baseEnd_3392893] using wordTrace_append hprefix tailTrace_3392893
  have hstable : (prefixWord ++ tailWord_3392893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392893).length < 2 ^ (prefixWord ++ tailWord_3392893).sum := by decide
  have hdescent : baseEnd_3392893 < baseStart_3392893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392940 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 3]
def baseStart_3392940 : Nat := 118140960795 + 3392940 * 2 ^ 59
def prefixEnd_3392940 : Nat := 4983230072969 + 3 ^ 40 * 3392940 * 2
def baseEnd_3392940 : Nat := 1742209051866060340346159

theorem tailTrace_3392940 : CollatzResearch.WordTrace tailWord_3392940 prefixEnd_3392940 1742209051866060340346159 := by
  unfold tailWord_3392940
  simp only [CollatzResearch.WordTrace]
  refine ⟨61875344163982661431652137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82500458885310215242202849 61875344163982661431652137)
  ·
    refine ⟨46406508122986996073739103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61875344163982661431652137 46406508122986996073739103)
    ·
      refine ⟨69609762184480494110608655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46406508122986996073739103 69609762184480494110608655)
      ·
        refine ⟨104414643276720741165912983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69609762184480494110608655 104414643276720741165912983)
        ·
          refine ⟨156621964915081111748869475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104414643276720741165912983 156621964915081111748869475)
          ·
            refine ⟨234932947372621667623304213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156621964915081111748869475 234932947372621667623304213)
            ·
              refine ⟨11012481908091640669842385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 234932947372621667623304213 11012481908091640669842385)
              ·
                refine ⟨8259361431068730502381789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11012481908091640669842385 8259361431068730502381789)
                ·
                  refine ⟨3097260536650773938393171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8259361431068730502381789 3097260536650773938393171)
                  ·
                    refine ⟨4645890804976160907589757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097260536650773938393171 4645890804976160907589757)
                    ·
                      refine ⟨1742209051866060340346159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645890804976160907589757 1742209051866060340346159)
                      ·
                        rfl

theorem cell23_3392940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 3].length) (baseStart_3392940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392940 prefixEnd_3392940 := by exact prefixLift 3392940
  have htrace : WordTrace (prefixWord ++ tailWord_3392940) baseStart_3392940 baseEnd_3392940 := by
    simpa [prefixWord, tailWord_3392940, baseEnd_3392940] using wordTrace_append hprefix tailTrace_3392940
  have hstable : (prefixWord ++ tailWord_3392940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392940).length < 2 ^ (prefixWord ++ tailWord_3392940).sum := by decide
  have hdescent : baseEnd_3392940 < baseStart_3392940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392993 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_3392993 : Nat := 118140960795 + 3392993 * 2 ^ 59
def prefixEnd_3392993 : Nat := 4983230072969 + 3 ^ 40 * 3392993 * 2
def baseEnd_3392993 : Nat := 1742236266340748632983415

theorem tailTrace_3392993 : CollatzResearch.WordTrace tailWord_3392993 prefixEnd_3392993 1742236266340748632983415 := by
  unfold tailWord_3392993
  simp only [CollatzResearch.WordTrace]
  refine ⟨123752621396773312914983633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82501747597848875276655755 123752621396773312914983633)
  ·
    refine ⟨92814466047579984686237725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123752621396773312914983633 92814466047579984686237725)
    ·
      refine ⟨34805424767842494257339147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92814466047579984686237725 34805424767842494257339147)
      ·
        refine ⟨52208137151763741386008721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34805424767842494257339147 52208137151763741386008721)
        ·
          refine ⟨39156102863822806039506541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52208137151763741386008721 39156102863822806039506541)
          ·
            refine ⟨14683538573933552264814953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39156102863822806039506541 14683538573933552264814953)
            ·
              refine ⟨11012653930450164198611215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14683538573933552264814953 11012653930450164198611215)
              ·
                refine ⟨16518980895675246297916823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012653930450164198611215 16518980895675246297916823)
                ·
                  refine ⟨24778471343512869446875235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16518980895675246297916823 24778471343512869446875235)
                  ·
                    refine ⟨37167707015269304170312853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24778471343512869446875235 37167707015269304170312853)
                    ·
                      refine ⟨1742236266340748632983415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37167707015269304170312853 1742236266340748632983415)
                      ·
                        rfl

theorem cell23_3392993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_3392993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392993 prefixEnd_3392993 := by exact prefixLift 3392993
  have htrace : WordTrace (prefixWord ++ tailWord_3392993) baseStart_3392993 baseEnd_3392993 := by
    simpa [prefixWord, tailWord_3392993, baseEnd_3392993] using wordTrace_append hprefix tailTrace_3392993
  have hstable : (prefixWord ++ tailWord_3392993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392993).length < 2 ^ (prefixWord ++ tailWord_3392993).sum := by decide
  have hdescent : baseEnd_3392993 < baseStart_3392993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3392997 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_3392997 : Nat := 118140960795 + 3392997 * 2 ^ 59
def prefixEnd_3392997 : Nat := 4983230072969 + 3 ^ 40 * 3392997 * 2
def baseEnd_3392997 : Nat := 1742238320263366617333397

theorem tailTrace_3392997 : CollatzResearch.WordTrace tailWord_3392997 prefixEnd_3392997 1742238320263366617333397 := by
  unfold tailWord_3392997
  simp only [CollatzResearch.WordTrace]
  refine ⟨123752767288758821598129245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82501844859172547732086163 123752767288758821598129245)
  ·
    refine ⟨46407287733284558099298467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123752767288758821598129245 46407287733284558099298467)
    ·
      refine ⟨69610931599926837148947701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46407287733284558099298467 69610931599926837148947701)
      ·
        refine ⟨6526024837493140982713847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69610931599926837148947701 6526024837493140982713847)
        ·
          refine ⟨9789037256239711474070771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526024837493140982713847 9789037256239711474070771)
          ·
            refine ⟨14683555884359567211106157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789037256239711474070771 14683555884359567211106157)
            ·
              refine ⟨5506333456634837704164809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14683555884359567211106157 5506333456634837704164809)
              ·
                refine ⟨4129750092476128278123607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506333456634837704164809 4129750092476128278123607)
                ·
                  refine ⟨6194625138714192417185411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129750092476128278123607 6194625138714192417185411)
                  ·
                    refine ⟨9291937708071288625778117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6194625138714192417185411 9291937708071288625778117)
                    ·
                      refine ⟨1742238320263366617333397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9291937708071288625778117 1742238320263366617333397)
                      ·
                        rfl

theorem cell23_3392997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_3392997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3392997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3392997 prefixEnd_3392997 := by exact prefixLift 3392997
  have htrace : WordTrace (prefixWord ++ tailWord_3392997) baseStart_3392997 baseEnd_3392997 := by
    simpa [prefixWord, tailWord_3392997, baseEnd_3392997] using wordTrace_append hprefix tailTrace_3392997
  have hstable : (prefixWord ++ tailWord_3392997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3392997).length < 2 ^ (prefixWord ++ tailWord_3392997).sum := by decide
  have hdescent : baseEnd_3392997 < baseStart_3392997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3392997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393000 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3393000 : Nat := 118140960795 + 3393000 * 2 ^ 59
def prefixEnd_3393000 : Nat := 4983230072969 + 3 ^ 40 * 3393000 * 2
def baseEnd_3393000 : Nat := 1742239860705330105595883

theorem tailTrace_3393000 : CollatzResearch.WordTrace tailWord_3393000 prefixEnd_3393000 1742239860705330105595883 := by
  unfold tailWord_3393000
  simp only [CollatzResearch.WordTrace]
  refine ⟨61876438353873976555244227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82501917805165302073658969 61876438353873976555244227)
  ·
    refine ⟨92814657530810964832866341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61876438353873976555244227 92814657530810964832866341)
    ·
      refine ⟨17402748287027055906162439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92814657530810964832866341 17402748287027055906162439)
      ·
        refine ⟨26104122430540583859243659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402748287027055906162439 26104122430540583859243659)
        ·
          refine ⟨39156183645810875788865489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26104122430540583859243659 39156183645810875788865489)
          ·
            refine ⟨29367137734358156841649117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39156183645810875788865489 29367137734358156841649117)
            ·
              refine ⟨11012676650384308815618419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29367137734358156841649117 11012676650384308815618419)
              ·
                refine ⟨16519014975576463223427629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012676650384308815618419 16519014975576463223427629)
                ·
                  refine ⟨6194630615841173708785361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16519014975576463223427629 6194630615841173708785361)
                  ·
                    refine ⟨4645972961880880281589021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6194630615841173708785361 4645972961880880281589021)
                    ·
                      refine ⟨1742239860705330105595883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4645972961880880281589021 1742239860705330105595883)
                      ·
                        rfl

theorem cell23_3393000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3393000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393000 prefixEnd_3393000 := by exact prefixLift 3393000
  have htrace : WordTrace (prefixWord ++ tailWord_3393000) baseStart_3393000 baseEnd_3393000 := by
    simpa [prefixWord, tailWord_3393000, baseEnd_3393000] using wordTrace_append hprefix tailTrace_3393000
  have hstable : (prefixWord ++ tailWord_3393000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393000).length < 2 ^ (prefixWord ++ tailWord_3393000).sum := by decide
  have hdescent : baseEnd_3393000 < baseStart_3393000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393010 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3393010 : Nat := 118140960795 + 3393010 * 2 ^ 59
def prefixEnd_3393010 : Nat := 4983230072969 + 3 ^ 40 * 3393010 * 2
def baseEnd_3393010 : Nat := 1742244995511875066470837

theorem tailTrace_3393010 : CollatzResearch.WordTrace tailWord_3393010 prefixEnd_3393010 1742244995511875066470837 := by
  unfold tailWord_3393010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30938310359427931204588121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82502160958474483212234989 30938310359427931204588121)
  ·
    refine ⟨23203732769570948403441091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30938310359427931204588121 23203732769570948403441091)
    ·
      refine ⟨34805599154356422605161637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23203732769570948403441091 34805599154356422605161637)
      ·
        refine ⟨6526049841441829238467807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34805599154356422605161637 6526049841441829238467807)
        ·
          refine ⟨9789074762162743857701711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526049841441829238467807 9789074762162743857701711)
          ·
            refine ⟨14683612143244115786552567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9789074762162743857701711 14683612143244115786552567)
            ·
              refine ⟨22025418214866173679828851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14683612143244115786552567 22025418214866173679828851)
              ·
                refine ⟨33038127322299260519743277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22025418214866173679828851 33038127322299260519743277)
                ·
                  refine ⟨12389297745862222694903729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33038127322299260519743277 12389297745862222694903729)
                  ·
                    refine ⟨9291973309396667021177797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12389297745862222694903729 9291973309396667021177797)
                    ·
                      refine ⟨1742244995511875066470837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9291973309396667021177797 1742244995511875066470837)
                      ·
                        rfl

theorem cell23_3393010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3393010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393010 prefixEnd_3393010 := by exact prefixLift 3393010
  have htrace : WordTrace (prefixWord ++ tailWord_3393010) baseStart_3393010 baseEnd_3393010 := by
    simpa [prefixWord, tailWord_3393010, baseEnd_3393010] using wordTrace_append hprefix tailTrace_3393010
  have hstable : (prefixWord ++ tailWord_3393010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393010).length < 2 ^ (prefixWord ++ tailWord_3393010).sum := by decide
  have hdescent : baseEnd_3393010 < baseStart_3393010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393014 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4]
def baseStart_3393014 : Nat := 118140960795 + 3393014 * 2 ^ 59
def prefixEnd_3393014 : Nat := 4983230072969 + 3 ^ 40 * 3393014 * 2
def baseEnd_3393014 : Nat := 1742247049434493050820819

theorem tailTrace_3393014 : CollatzResearch.WordTrace tailWord_3393014 prefixEnd_3393014 1742247049434493050820819 := by
  unfold tailWord_3393014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734586708106077093843631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82502258219798155667665397 7734586708106077093843631)
  ·
    refine ⟨11601880062159115640765447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7734586708106077093843631 11601880062159115640765447)
    ·
      refine ⟨17402820093238673461148171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11601880062159115640765447 17402820093238673461148171)
      ·
        refine ⟨26104230139858010191722257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17402820093238673461148171 26104230139858010191722257)
        ·
          refine ⟨19578172604893507643791693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26104230139858010191722257 19578172604893507643791693)
          ·
            refine ⟨7341814726835065366421885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19578172604893507643791693 7341814726835065366421885)
            ·
              refine ⟨2753180522563149512408207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7341814726835065366421885 2753180522563149512408207)
              ·
                refine ⟨4129770783844724268612311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753180522563149512408207 4129770783844724268612311)
                ·
                  refine ⟨6194656175767086402918467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4129770783844724268612311 6194656175767086402918467)
                  ·
                    refine ⟨9291984263650629604377701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6194656175767086402918467 9291984263650629604377701)
                    ·
                      refine ⟨1742247049434493050820819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9291984263650629604377701 1742247049434493050820819)
                      ·
                        rfl

theorem cell23_3393014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4].length) (baseStart_3393014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393014 prefixEnd_3393014 := by exact prefixLift 3393014
  have htrace : WordTrace (prefixWord ++ tailWord_3393014) baseStart_3393014 baseEnd_3393014 := by
    simpa [prefixWord, tailWord_3393014, baseEnd_3393014] using wordTrace_append hprefix tailTrace_3393014
  have hstable : (prefixWord ++ tailWord_3393014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393014).length < 2 ^ (prefixWord ++ tailWord_3393014).sum := by decide
  have hdescent : baseEnd_3393014 < baseStart_3393014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393031 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3393031 : Nat := 118140960795 + 3393031 * 2 ^ 59
def prefixEnd_3393031 : Nat := 4983230072969 + 3 ^ 40 * 3393031 * 2
def baseEnd_3393031 : Nat := 1742255778605619484308241

theorem tailTrace_3393031 : CollatzResearch.WordTrace tailWord_3393031 prefixEnd_3393031 1742255778605619484308241 := by
  unfold tailWord_3393031
  simp only [CollatzResearch.WordTrace]
  refine ⟨123754007370635645404866947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82502671580423763603244631 123754007370635645404866947)
  ·
    refine ⟨185631011055953468107300421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123754007370635645404866947 185631011055953468107300421)
    ·
      refine ⟨34805814572991275270118829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 185631011055953468107300421 34805814572991275270118829)
      ·
        refine ⟨13052180464871728226294561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34805814572991275270118829 13052180464871728226294561)
        ·
          refine ⟨9789135348653796169720921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13052180464871728226294561 9789135348653796169720921)
          ·
            refine ⟨7341851511490347127290691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789135348653796169720921 7341851511490347127290691)
            ·
              refine ⟨11012777267235520690936037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7341851511490347127290691 11012777267235520690936037)
              ·
                refine ⟨2064895737606660129550507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11012777267235520690936037 2064895737606660129550507)
                ·
                  refine ⟨3097343606409990194325761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2064895737606660129550507 3097343606409990194325761)
                  ·
                    refine ⟨2323007704807492645744321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3097343606409990194325761 2323007704807492645744321)
                    ·
                      refine ⟨1742255778605619484308241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323007704807492645744321 1742255778605619484308241)
                      ·
                        rfl

theorem cell23_3393031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3393031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393031 prefixEnd_3393031 := by exact prefixLift 3393031
  have htrace : WordTrace (prefixWord ++ tailWord_3393031) baseStart_3393031 baseEnd_3393031 := by
    simpa [prefixWord, tailWord_3393031, baseEnd_3393031] using wordTrace_append hprefix tailTrace_3393031
  have hstable : (prefixWord ++ tailWord_3393031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393031).length < 2 ^ (prefixWord ++ tailWord_3393031).sum := by decide
  have hdescent : baseEnd_3393031 < baseStart_3393031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393044 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3393044 : Nat := 118140960795 + 3393044 * 2 ^ 59
def prefixEnd_3393044 : Nat := 4983230072969 + 3 ^ 40 * 3393044 * 2
def baseEnd_3393044 : Nat := 1742262453854127933445681

theorem tailTrace_3393044 : CollatzResearch.WordTrace tailWord_3393044 prefixEnd_3393044 1742262453854127933445681 := by
  unfold tailWord_3393044
  simp only [CollatzResearch.WordTrace]
  refine ⟨61877240759794274312545093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82502987679725699083393457 61877240759794274312545093)
  ·
    refine ⟨11601982642461426433602205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61877240759794274312545093 11601982642461426433602205)
    ·
      refine ⟨4350743490923034912600827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11601982642461426433602205 4350743490923034912600827)
      ·
        refine ⟨6526115236384552368901241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4350743490923034912600827 6526115236384552368901241)
        ·
          refine ⟨4894586427288414276675931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6526115236384552368901241 4894586427288414276675931)
          ·
            refine ⟨7341879640932621415013897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4894586427288414276675931 7341879640932621415013897)
            ·
              refine ⟨5506409730699466061260423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7341879640932621415013897 5506409730699466061260423)
              ·
                refine ⟨8259614596049199091890635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506409730699466061260423 8259614596049199091890635)
                ·
                  refine ⟨12389421894073798637835953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8259614596049199091890635 12389421894073798637835953)
                  ·
                    refine ⟨9292066420555348978376965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12389421894073798637835953 9292066420555348978376965)
                    ·
                      refine ⟨1742262453854127933445681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9292066420555348978376965 1742262453854127933445681)
                      ·
                        rfl

theorem cell23_3393044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3393044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393044 prefixEnd_3393044 := by exact prefixLift 3393044
  have htrace : WordTrace (prefixWord ++ tailWord_3393044) baseStart_3393044 baseEnd_3393044 := by
    simpa [prefixWord, tailWord_3393044, baseEnd_3393044] using wordTrace_append hprefix tailTrace_3393044
  have hstable : (prefixWord ++ tailWord_3393044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393044).length < 2 ^ (prefixWord ++ tailWord_3393044).sum := by decide
  have hdescent : baseEnd_3393044 < baseStart_3393044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393057 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3393057 : Nat := 118140960795 + 3393057 * 2 ^ 59
def prefixEnd_3393057 : Nat := 4983230072969 + 3 ^ 40 * 3393057 * 2
def baseEnd_3393057 : Nat := 1742269129102636382583121

theorem tailTrace_3393057 : CollatzResearch.WordTrace tailWord_3393057 prefixEnd_3393057 1742269129102636382583121 := by
  unfold tailWord_3393057
  simp only [CollatzResearch.WordTrace]
  refine ⟨123754955668541451845313425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82503303779027634563542283 123754955668541451845313425)
  ·
    refine ⟨92816216751406088883985069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123754955668541451845313425 92816216751406088883985069)
    ·
      refine ⟨34806081281777283331494401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92816216751406088883985069 34806081281777283331494401)
      ·
        refine ⟨26104560961332962498620801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34806081281777283331494401 26104560961332962498620801)
        ·
          refine ⟨19578420720999721873965601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26104560961332962498620801 19578420720999721873965601)
          ·
            refine ⟨14683815540749791405474201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19578420720999721873965601 14683815540749791405474201)
            ·
              refine ⟨11012861655562343554105651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14683815540749791405474201 11012861655562343554105651)
              ·
                refine ⟨16519292483343515331158477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11012861655562343554105651 16519292483343515331158477)
                ·
                  refine ⟨6194734681253818249184429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16519292483343515331158477 6194734681253818249184429)
                  ·
                    refine ⟨2323025505470181843444161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6194734681253818249184429 2323025505470181843444161)
                    ·
                      refine ⟨1742269129102636382583121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323025505470181843444161 1742269129102636382583121)
                      ·
                        rfl

theorem cell23_3393057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3393057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393057 prefixEnd_3393057 := by exact prefixLift 3393057
  have htrace : WordTrace (prefixWord ++ tailWord_3393057) baseStart_3393057 baseEnd_3393057 := by
    simpa [prefixWord, tailWord_3393057, baseEnd_3393057] using wordTrace_append hprefix tailTrace_3393057
  have hstable : (prefixWord ++ tailWord_3393057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393057).length < 2 ^ (prefixWord ++ tailWord_3393057).sum := by decide
  have hdescent : baseEnd_3393057 < baseStart_3393057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393073 : List Nat := [1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_3393073 : Nat := 118140960795 + 3393073 * 2 ^ 59
def prefixEnd_3393073 : Nat := 4983230072969 + 3 ^ 40 * 3393073 * 2
def baseEnd_3393073 : Nat := 1742277344793108319983047

theorem tailTrace_3393073 : CollatzResearch.WordTrace tailWord_3393073 prefixEnd_3393073 1742277344793108319983047 := by
  unfold tailWord_3393073
  simp only [CollatzResearch.WordTrace]
  refine ⟨123755539236483486577895873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82503692824322324385263915 123755539236483486577895873)
  ·
    refine ⟨92816654427362614933421905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123755539236483486577895873 92816654427362614933421905)
    ·
      refine ⟨69612490820521961200066429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92816654427362614933421905 69612490820521961200066429)
      ·
        refine ⟨26104684057695735450024911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69612490820521961200066429 26104684057695735450024911)
        ·
          refine ⟨39157026086543603175037367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26104684057695735450024911 39157026086543603175037367)
          ·
            refine ⟨58735539129815404762556051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39157026086543603175037367 58735539129815404762556051)
            ·
              refine ⟨88103308694723107143834077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58735539129815404762556051 88103308694723107143834077)
              ·
                refine ⟨33038740760521165178937779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88103308694723107143834077 33038740760521165178937779)
                ·
                  refine ⟨49558111140781747768406669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33038740760521165178937779 49558111140781747768406669)
                  ·
                    refine ⟨18584291677793155413152501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49558111140781747768406669 18584291677793155413152501)
                    ·
                      refine ⟨1742277344793108319983047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18584291677793155413152501 1742277344793108319983047)
                      ·
                        rfl

theorem cell23_3393073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_3393073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393073 prefixEnd_3393073 := by exact prefixLift 3393073
  have htrace : WordTrace (prefixWord ++ tailWord_3393073) baseStart_3393073 baseEnd_3393073 := by
    simpa [prefixWord, tailWord_3393073, baseEnd_3393073] using wordTrace_append hprefix tailTrace_3393073
  have hstable : (prefixWord ++ tailWord_3393073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393073).length < 2 ^ (prefixWord ++ tailWord_3393073).sum := by decide
  have hdescent : baseEnd_3393073 < baseStart_3393073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393100 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3393100 : Nat := 118140960795 + 3393100 * 2 ^ 59
def prefixEnd_3393100 : Nat := 4983230072969 + 3 ^ 40 * 3393100 * 2
def baseEnd_3393100 : Nat := 1742291208770779714345423

theorem tailTrace_3393100 : CollatzResearch.WordTrace tailWord_3393100 prefixEnd_3393100 1742291208770779714345423 := by
  unfold tailWord_3393100
  simp only [CollatzResearch.WordTrace]
  refine ⟨61878262003692835094564377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82504349338257113459419169 61878262003692835094564377)
  ·
    refine ⟨46408696502769626320923283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61878262003692835094564377 46408696502769626320923283)
    ·
      refine ⟨69613044754154439481384925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46408696502769626320923283 69613044754154439481384925)
      ·
        refine ⟨26104891782807914805519347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69613044754154439481384925 26104891782807914805519347)
        ·
          refine ⟨39157337674211872208279021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26104891782807914805519347 39157337674211872208279021)
          ·
            refine ⟨14684001627829452078104633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39157337674211872208279021 14684001627829452078104633)
            ·
              refine ⟨11013001220872089058578475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14684001627829452078104633 11013001220872089058578475)
              ·
                refine ⟨16519501831308133587867713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11013001220872089058578475 16519501831308133587867713)
                ·
                  refine ⟨12389626373481100190900785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16519501831308133587867713 12389626373481100190900785)
                  ·
                    refine ⟨9292219780110825143175589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12389626373481100190900785 9292219780110825143175589)
                    ·
                      refine ⟨1742291208770779714345423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9292219780110825143175589 1742291208770779714345423)
                      ·
                        rfl

theorem cell23_3393100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3393100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393100 prefixEnd_3393100 := by exact prefixLift 3393100
  have htrace : WordTrace (prefixWord ++ tailWord_3393100) baseStart_3393100 baseEnd_3393100 := by
    simpa [prefixWord, tailWord_3393100, baseEnd_3393100] using wordTrace_append hprefix tailTrace_3393100
  have hstable : (prefixWord ++ tailWord_3393100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393100).length < 2 ^ (prefixWord ++ tailWord_3393100).sum := by decide
  have hdescent : baseEnd_3393100 < baseStart_3393100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393127 : List Nat := [1, 1, 5, 1, 1, 1, 5, 3, 5]
def baseStart_3393127 : Nat := 118140960795 + 3393127 * 2 ^ 59
def prefixEnd_3393127 : Nat := 4983230072969 + 3 ^ 40 * 3393127 * 2
def baseEnd_3393127 : Nat := 193589452527605678745311

theorem tailTrace_3393127 : CollatzResearch.WordTrace tailWord_3393127 prefixEnd_3393127 193589452527605678745311 := by
  unfold tailWord_3393127
  simp only [CollatzResearch.WordTrace]
  refine ⟨123757508778287853800361635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82505005852191902533574423 123757508778287853800361635)
  ·
    refine ⟨185636263167431780700542453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123757508778287853800361635 185636263167431780700542453)
    ·
      refine ⟨17403399671946729440675855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 185636263167431780700542453 17403399671946729440675855)
      ·
        refine ⟨26105099507920094161013783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17403399671946729440675855 26105099507920094161013783)
        ·
          refine ⟨39157649261880141241520675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26105099507920094161013783 39157649261880141241520675)
          ·
            refine ⟨58736473892820211862281013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39157649261880141241520675 58736473892820211862281013)
            ·
              refine ⟨5506544427451894862088845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58736473892820211862281013 5506544427451894862088845)
              ·
                refine ⟨2064954160294460573283317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5506544427451894862088845 2064954160294460573283317)
                ·
                  refine ⟨193589452527605678745311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2064954160294460573283317 193589452527605678745311)
                  ·
                    rfl

theorem cell23_3393127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 5].length) (baseStart_3393127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393127 prefixEnd_3393127 := by exact prefixLift 3393127
  have htrace : WordTrace (prefixWord ++ tailWord_3393127) baseStart_3393127 baseEnd_3393127 := by
    simpa [prefixWord, tailWord_3393127, baseEnd_3393127] using wordTrace_append hprefix tailTrace_3393127
  have hstable : (prefixWord ++ tailWord_3393127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393127).length < 2 ^ (prefixWord ++ tailWord_3393127).sum := by decide
  have hdescent : baseEnd_3393127 < baseStart_3393127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393200 : List Nat := [2, 1, 1, 1, 2, 1, 5, 4, 6]
def baseStart_3393200 : Nat := 118140960795 + 3393200 * 2 ^ 59
def prefixEnd_3393200 : Nat := 4983230072969 + 3 ^ 40 * 3393200 * 2
def baseEnd_3393200 : Nat := 193593617426247702566107

theorem tailTrace_3393200 : CollatzResearch.WordTrace tailWord_3393200 prefixEnd_3393200 193593617426247702566107 := by
  unfold tailWord_3393200
  simp only [CollatzResearch.WordTrace]
  refine ⟨61880085653511693633884527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82506780871348924845179369 61880085653511693633884527)
  ·
    refine ⟨92820128480267540450826791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61880085653511693633884527 92820128480267540450826791)
    ·
      refine ⟨139230192720401310676240187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92820128480267540450826791 139230192720401310676240187)
      ·
        refine ⟨208845289080601966014360281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139230192720401310676240187 208845289080601966014360281)
        ·
          refine ⟨156633966810451474510770211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208845289080601966014360281 156633966810451474510770211)
          ·
            refine ⟨234950950215677211766155317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156633966810451474510770211 234950950215677211766155317)
            ·
              refine ⟨22026651582719738603077061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234950950215677211766155317 22026651582719738603077061)
              ·
                refine ⟨4129997171759950988076949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22026651582719738603077061 4129997171759950988076949)
                ·
                  refine ⟨193593617426247702566107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4129997171759950988076949 193593617426247702566107)
                  ·
                    rfl

theorem cell23_3393200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 6].length) (baseStart_3393200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393200 prefixEnd_3393200 := by exact prefixLift 3393200
  have htrace : WordTrace (prefixWord ++ tailWord_3393200) baseStart_3393200 baseEnd_3393200 := by
    simpa [prefixWord, tailWord_3393200, baseEnd_3393200] using wordTrace_append hprefix tailTrace_3393200
  have hstable : (prefixWord ++ tailWord_3393200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393200).length < 2 ^ (prefixWord ++ tailWord_3393200).sum := by decide
  have hdescent : baseEnd_3393200 < baseStart_3393200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393247 : List Nat := [1, 1, 2, 3, 2, 2, 3, 3, 1, 5]
def baseStart_3393247 : Nat := 118140960795 + 3393247 * 2 ^ 59
def prefixEnd_3393247 : Nat := 4983230072969 + 3 ^ 40 * 3393247 * 2
def baseEnd_3393247 : Nat := 580788896808996879735749

theorem tailTrace_3393247 : CollatzResearch.WordTrace tailWord_3393247 prefixEnd_3393247 580788896808996879735749 := by
  unfold tailWord_3393247
  simp only [CollatzResearch.WordTrace]
  refine ⟨123761885537853114294729995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82507923691902076196486663 123761885537853114294729995)
  ·
    refine ⟨185642828306779671442094993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123761885537853114294729995 185642828306779671442094993)
    ·
      refine ⟨139232121230084753581571245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185642828306779671442094993 139232121230084753581571245)
      ·
        refine ⟨52212045461281782593089217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 139232121230084753581571245 52212045461281782593089217)
        ·
          refine ⟨39159034095961336944816913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52212045461281782593089217 39159034095961336944816913)
          ·
            refine ⟨29369275571971002708612685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39159034095961336944816913 29369275571971002708612685)
            ·
              refine ⟨11013478339489126015729757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29369275571971002708612685 11013478339489126015729757)
              ·
                refine ⟨4130054377308422255898659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11013478339489126015729757 4130054377308422255898659)
                ·
                  refine ⟨6195081565962633383847989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130054377308422255898659 6195081565962633383847989)
                  ·
                    refine ⟨580788896808996879735749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6195081565962633383847989 580788896808996879735749)
                    ·
                      rfl

theorem cell23_3393247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_3393247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393247 prefixEnd_3393247 := by exact prefixLift 3393247
  have htrace : WordTrace (prefixWord ++ tailWord_3393247) baseStart_3393247 baseEnd_3393247 := by
    simpa [prefixWord, tailWord_3393247, baseEnd_3393247] using wordTrace_append hprefix tailTrace_3393247
  have hstable : (prefixWord ++ tailWord_3393247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393247).length < 2 ^ (prefixWord ++ tailWord_3393247).sum := by decide
  have hdescent : baseEnd_3393247 < baseStart_3393247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393251 : List Nat := [1, 1, 1, 7, 3, 1, 1, 2, 6]
def baseStart_3393251 : Nat := 118140960795 + 3393251 * 2 ^ 59
def prefixEnd_3393251 : Nat := 4983230072969 + 3 ^ 40 * 3393251 * 2
def baseEnd_3393251 : Nat := 193596527149956513728581

theorem tailTrace_3393251 : CollatzResearch.WordTrace tailWord_3393251 prefixEnd_3393251 193596527149956513728581 := by
  unfold tailWord_3393251
  simp only [CollatzResearch.WordTrace]
  refine ⟨123762031429838622977875607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82508020953225748651917071 123762031429838622977875607)
  ·
    refine ⟨185643047144757934466813411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123762031429838622977875607 185643047144757934466813411)
    ·
      refine ⟨278464570717136901700220117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185643047144757934466813411 278464570717136901700220117)
      ·
        refine ⟨6526513376182896133598909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 278464570717136901700220117 6526513376182896133598909)
        ·
          refine ⟨2447442516068586050099591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6526513376182896133598909 2447442516068586050099591)
          ·
            refine ⟨3671163774102879075149387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2447442516068586050099591 3671163774102879075149387)
            ·
              refine ⟨5506745661154318612724081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3671163774102879075149387 5506745661154318612724081)
              ·
                refine ⟨4130059245865738959543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5506745661154318612724081 4130059245865738959543061)
                ·
                  refine ⟨193596527149956513728581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130059245865738959543061 193596527149956513728581)
                  ·
                    rfl

theorem cell23_3393251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 6].length) (baseStart_3393251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393251 prefixEnd_3393251 := by exact prefixLift 3393251
  have htrace : WordTrace (prefixWord ++ tailWord_3393251) baseStart_3393251 baseEnd_3393251 := by
    simpa [prefixWord, tailWord_3393251, baseEnd_3393251] using wordTrace_append hprefix tailTrace_3393251
  have hstable : (prefixWord ++ tailWord_3393251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393251).length < 2 ^ (prefixWord ++ tailWord_3393251).sum := by decide
  have hdescent : baseEnd_3393251 < baseStart_3393251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393260 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 3, 6]
def baseStart_3393260 : Nat := 118140960795 + 3393260 * 2 ^ 59
def prefixEnd_3393260 : Nat := 4983230072969 + 3 ^ 40 * 3393260 * 2
def baseEnd_3393260 : Nat := 580791121891833029448229

theorem tailTrace_3393260 : CollatzResearch.WordTrace tailWord_3393260 prefixEnd_3393260 580791121891833029448229 := by
  unfold tailWord_3393260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881179843403008757476617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82508239791204011676635489 61881179843403008757476617)
  ·
    refine ⟨46410884882552256568107463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61881179843403008757476617 46410884882552256568107463)
    ·
      refine ⟨69616327323828384852161195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46410884882552256568107463 69616327323828384852161195)
      ·
        refine ⟨104424490985742577278241793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69616327323828384852161195 104424490985742577278241793)
        ·
          refine ⟨78318368239306932958681345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104424490985742577278241793 78318368239306932958681345)
          ·
            refine ⟨58738776179480199719011009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78318368239306932958681345 58738776179480199719011009)
            ·
              refine ⟨44054082134610149789258257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58738776179480199719011009 44054082134610149789258257)
              ·
                refine ⟨33040561600957612341943693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44054082134610149789258257 33040561600957612341943693)
                ·
                  refine ⟨12390210600359104628228885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33040561600957612341943693 12390210600359104628228885)
                  ·
                    refine ⟨580791121891833029448229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12390210600359104628228885 580791121891833029448229)
                    ·
                      rfl

theorem cell23_3393260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_3393260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393260 prefixEnd_3393260 := by exact prefixLift 3393260
  have htrace : WordTrace (prefixWord ++ tailWord_3393260) baseStart_3393260 baseEnd_3393260 := by
    simpa [prefixWord, tailWord_3393260, baseEnd_3393260] using wordTrace_append hprefix tailTrace_3393260
  have hstable : (prefixWord ++ tailWord_3393260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393260).length < 2 ^ (prefixWord ++ tailWord_3393260).sum := by decide
  have hdescent : baseEnd_3393260 < baseStart_3393260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393261 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3393261 : Nat := 118140960795 + 3393261 * 2 ^ 59
def prefixEnd_3393261 : Nat := 4983230072969 + 3 ^ 40 * 3393261 * 2
def baseEnd_3393261 : Nat := 1742373879156153584432183

theorem tailTrace_3393261 : CollatzResearch.WordTrace tailWord_3393261 prefixEnd_3393261 1742373879156153584432183 := by
  unfold tailWord_3393261
  simp only [CollatzResearch.WordTrace]
  refine ⟨123762396159802394685739637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82508264106534929790493091 123762396159802394685739637)
  ·
    refine ⟨11602724639981474501788091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 123762396159802394685739637 11602724639981474501788091)
    ·
      refine ⟨17404086959972211752682137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11602724639981474501788091 17404086959972211752682137)
      ·
        refine ⟨13053065219979158814511603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17404086959972211752682137 13053065219979158814511603)
        ·
          refine ⟨19579597829968738221767405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13053065219979158814511603 19579597829968738221767405)
          ·
            refine ⟨7342349186238276833162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19579597829968738221767405 7342349186238276833162777)
            ·
              refine ⟨5506761889678707624872083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342349186238276833162777 5506761889678707624872083)
              ·
                refine ⟨8260142834518061437308125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5506761889678707624872083 8260142834518061437308125)
                ·
                  refine ⟨3097553562944273038990547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8260142834518061437308125 3097553562944273038990547)
                  ·
                    refine ⟨4646330344416409558485821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097553562944273038990547 4646330344416409558485821)
                    ·
                      refine ⟨1742373879156153584432183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646330344416409558485821 1742373879156153584432183)
                      ·
                        rfl

theorem cell23_3393261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3393261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393261 prefixEnd_3393261 := by exact prefixLift 3393261
  have htrace : WordTrace (prefixWord ++ tailWord_3393261) baseStart_3393261 baseEnd_3393261 := by
    simpa [prefixWord, tailWord_3393261, baseEnd_3393261] using wordTrace_append hprefix tailTrace_3393261
  have hstable : (prefixWord ++ tailWord_3393261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393261).length < 2 ^ (prefixWord ++ tailWord_3393261).sum := by decide
  have hdescent : baseEnd_3393261 < baseStart_3393261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393268 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3393268 : Nat := 118140960795 + 3393268 * 2 ^ 59
def prefixEnd_3393268 : Nat := 4983230072969 + 3 ^ 40 * 3393268 * 2
def baseEnd_3393268 : Nat := 193597497057859450782739

theorem tailTrace_3393268 : CollatzResearch.WordTrace tailWord_3393268 prefixEnd_3393268 193597497057859450782739 := by
  unfold tailWord_3393268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881325735388517440622229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82508434313851356587496305 61881325735388517440622229)
  ·
    refine ⟨2900687143846336755029167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61881325735388517440622229 2900687143846336755029167)
    ·
      refine ⟨4351030715769505132543751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2900687143846336755029167 4351030715769505132543751)
      ·
        refine ⟨6526546073654257698815627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351030715769505132543751 6526546073654257698815627)
        ·
          refine ⟨9789819110481386548223441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6526546073654257698815627 9789819110481386548223441)
          ·
            refine ⟨7342364332861039911167581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9789819110481386548223441 7342364332861039911167581)
            ·
              refine ⟨2753386624822889966687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342364332861039911167581 2753386624822889966687843)
              ·
                refine ⟨4130079937234334950031765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753386624822889966687843 4130079937234334950031765)
                ·
                  refine ⟨193597497057859450782739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130079937234334950031765 193597497057859450782739)
                  ·
                    rfl

theorem cell23_3393268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3393268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393268 prefixEnd_3393268 := by exact prefixLift 3393268
  have htrace : WordTrace (prefixWord ++ tailWord_3393268) baseStart_3393268 baseEnd_3393268 := by
    simpa [prefixWord, tailWord_3393268, baseEnd_3393268] using wordTrace_append hprefix tailTrace_3393268
  have hstable : (prefixWord ++ tailWord_3393268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393268).length < 2 ^ (prefixWord ++ tailWord_3393268).sum := by decide
  have hdescent : baseEnd_3393268 < baseStart_3393268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393280 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6]
def baseStart_3393280 : Nat := 118140960795 + 3393280 * 2 ^ 59
def prefixEnd_3393280 : Nat := 4983230072969 + 3 ^ 40 * 3393280 * 2
def baseEnd_3393280 : Nat := 1742383635288589010094595

theorem tailTrace_3393280 : CollatzResearch.WordTrace tailWord_3393280 prefixEnd_3393280 1742383635288589010094595 := by
  unfold tailWord_3393280
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881544573366780465340647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82508726097822373953787529 61881544573366780465340647)
  ·
    refine ⟨92822316860050170698010971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61881544573366780465340647 92822316860050170698010971)
    ·
      refine ⟨139233475290075256047016457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92822316860050170698010971 139233475290075256047016457)
      ·
        refine ⟨104425106467556442035262343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139233475290075256047016457 104425106467556442035262343)
        ·
          refine ⟨156637659701334663052893515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104425106467556442035262343 156637659701334663052893515)
          ·
            refine ⟨234956489552001994579340273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156637659701334663052893515 234956489552001994579340273)
            ·
              refine ⟨176217367164001495934505205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234956489552001994579340273 176217367164001495934505205)
              ·
                refine ⟨16520378171625140243859863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 176217367164001495934505205 16520378171625140243859863)
                ·
                  refine ⟨24780567257437710365789795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16520378171625140243859863 24780567257437710365789795)
                  ·
                    refine ⟨37170850886156565548684693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24780567257437710365789795 37170850886156565548684693)
                    ·
                      refine ⟨1742383635288589010094595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37170850886156565548684693 1742383635288589010094595)
                      ·
                        rfl

theorem cell23_3393280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_3393280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393280 prefixEnd_3393280 := by exact prefixLift 3393280
  have htrace : WordTrace (prefixWord ++ tailWord_3393280) baseStart_3393280 baseEnd_3393280 := by
    simpa [prefixWord, tailWord_3393280, baseEnd_3393280] using wordTrace_append hprefix tailTrace_3393280
  have hstable : (prefixWord ++ tailWord_3393280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393280).length < 2 ^ (prefixWord ++ tailWord_3393280).sum := by decide
  have hdescent : baseEnd_3393280 < baseStart_3393280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393284 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3393284 : Nat := 118140960795 + 3393284 * 2 ^ 59
def prefixEnd_3393284 : Nat := 4983230072969 + 3 ^ 40 * 3393284 * 2
def baseEnd_3393284 : Nat := 1742385689211206994444577

theorem tailTrace_3393284 : CollatzResearch.WordTrace tailWord_3393284 prefixEnd_3393284 1742385689211206994444577 := by
  unfold tailWord_3393284
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881617519359534806913453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82508823359146046409217937 61881617519359534806913453)
  ·
    refine ⟨23205606569759825552592545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61881617519359534806913453 23205606569759825552592545)
    ·
      refine ⟨17404204927319869164444409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23205606569759825552592545 17404204927319869164444409)
      ·
        refine ⟨13053153695489901873333307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17404204927319869164444409 13053153695489901873333307)
        ·
          refine ⟨19579730543234852809999961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13053153695489901873333307 19579730543234852809999961)
          ·
            refine ⟨14684797907426139607499971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19579730543234852809999961 14684797907426139607499971)
            ·
              refine ⟨22027196861139209411249957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14684797907426139607499971 22027196861139209411249957)
              ·
                refine ⟨4130099411463601764609367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22027196861139209411249957 4130099411463601764609367)
                ·
                  refine ⟨6195149117195402646914051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130099411463601764609367 6195149117195402646914051)
                  ·
                    refine ⟨9292723675793103970371077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195149117195402646914051 9292723675793103970371077)
                    ·
                      refine ⟨1742385689211206994444577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9292723675793103970371077 1742385689211206994444577)
                      ·
                        rfl

theorem cell23_3393284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3393284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393284 prefixEnd_3393284 := by exact prefixLift 3393284
  have htrace : WordTrace (prefixWord ++ tailWord_3393284) baseStart_3393284 baseEnd_3393284 := by
    simpa [prefixWord, tailWord_3393284, baseEnd_3393284] using wordTrace_append hprefix tailTrace_3393284
  have hstable : (prefixWord ++ tailWord_3393284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393284).length < 2 ^ (prefixWord ++ tailWord_3393284).sum := by decide
  have hdescent : baseEnd_3393284 < baseStart_3393284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393304 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_3393304 : Nat := 118140960795 + 3393304 * 2 ^ 59
def prefixEnd_3393304 : Nat := 4983230072969 + 3 ^ 40 * 3393304 * 2
def baseEnd_3393304 : Nat := 1742395958824296916194485

theorem tailTrace_3393304 : CollatzResearch.WordTrace tailWord_3393304 prefixEnd_3393304 1742395958824296916194485 := by
  unfold tailWord_3393304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61881982249323306514777483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82509309665764408686369977 61881982249323306514777483)
  ·
    refine ⟨92822973373984959772166225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61881982249323306514777483 92822973373984959772166225)
    ·
      refine ⟨69617230030488719829124669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92822973373984959772166225 69617230030488719829124669)
      ·
        refine ⟨26106461261433269935921751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69617230030488719829124669 26106461261433269935921751)
        ·
          refine ⟨39159691892149904903882627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26106461261433269935921751 39159691892149904903882627)
          ·
            refine ⟨58739537838224857355823941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39159691892149904903882627 58739537838224857355823941)
            ·
              refine ⟨11013663344667160754216989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58739537838224857355823941 11013663344667160754216989)
              ·
                refine ⟨4130123754250185282831371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11013663344667160754216989 4130123754250185282831371)
                ·
                  refine ⟨6195185631375277924247057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130123754250185282831371 6195185631375277924247057)
                  ·
                    refine ⟨4646389223531458443185293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6195185631375277924247057 4646389223531458443185293)
                    ·
                      refine ⟨1742395958824296916194485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646389223531458443185293 1742395958824296916194485)
                      ·
                        rfl

theorem cell23_3393304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_3393304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393304 prefixEnd_3393304 := by exact prefixLift 3393304
  have htrace : WordTrace (prefixWord ++ tailWord_3393304) baseStart_3393304 baseEnd_3393304 := by
    simpa [prefixWord, tailWord_3393304, baseEnd_3393304] using wordTrace_append hprefix tailTrace_3393304
  have hstable : (prefixWord ++ tailWord_3393304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393304).length < 2 ^ (prefixWord ++ tailWord_3393304).sum := by decide
  have hdescent : baseEnd_3393304 < baseStart_3393304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393377 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_3393377 : Nat := 118140960795 + 3393377 * 2 ^ 59
def prefixEnd_3393377 : Nat := 4983230072969 + 3 ^ 40 * 3393377 * 2
def baseEnd_3393377 : Nat := 1742433442912075130581649

theorem tailTrace_3393377 : CollatzResearch.WordTrace tailWord_3393377 prefixEnd_3393377 1742433442912075130581649 := by
  unfold tailWord_3393377
  simp only [CollatzResearch.WordTrace]
  refine ⟨123766627027382146496962385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82511084684921430997974923 123766627027382146496962385)
  ·
    refine ⟨92824970270536609872721789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 123766627027382146496962385 92824970270536609872721789)
    ·
      refine ⟨34809363851451228702270671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92824970270536609872721789 34809363851451228702270671)
      ·
        refine ⟨52214045777176843053406007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34809363851451228702270671 52214045777176843053406007)
        ·
          refine ⟨78321068665765264580109011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52214045777176843053406007 78321068665765264580109011)
          ·
            refine ⟨117481602998647896870163517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78321068665765264580109011 117481602998647896870163517)
            ·
              refine ⟨44055601124492961326311319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 117481602998647896870163517 44055601124492961326311319)
              ·
                refine ⟨66083401686739441989466979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44055601124492961326311319 66083401686739441989466979)
                ·
                  refine ⟨99125102530109162984200469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66083401686739441989466979 99125102530109162984200469)
                  ·
                    refine ⟨4646489181098867014884397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99125102530109162984200469 4646489181098867014884397)
                    ·
                      refine ⟨1742433442912075130581649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646489181098867014884397 1742433442912075130581649)
                      ·
                        rfl

theorem cell23_3393377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_3393377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393377 prefixEnd_3393377 := by exact prefixLift 3393377
  have htrace : WordTrace (prefixWord ++ tailWord_3393377) baseStart_3393377 baseEnd_3393377 := by
    simpa [prefixWord, tailWord_3393377, baseEnd_3393377] using wordTrace_append hprefix tailTrace_3393377
  have hstable : (prefixWord ++ tailWord_3393377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393377).length < 2 ^ (prefixWord ++ tailWord_3393377).sum := by decide
  have hdescent : baseEnd_3393377 < baseStart_3393377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393407 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_3393407 : Nat := 118140960795 + 3393407 * 2 ^ 59
def prefixEnd_3393407 : Nat := 4983230072969 + 3 ^ 40 * 3393407 * 2
def baseEnd_3393407 : Nat := 1742448847331710013206511

theorem tailTrace_3393407 : CollatzResearch.WordTrace tailWord_3393407 prefixEnd_3393407 1742448847331710013206511 := by
  unfold tailWord_3393407
  simp only [CollatzResearch.WordTrace]
  refine ⟨123767721217273461620554475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82511814144848974413702983 123767721217273461620554475)
  ·
    refine ⟨185651581825910192430831713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123767721217273461620554475 185651581825910192430831713)
    ·
      refine ⟨139238686369432644323123785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185651581825910192430831713 139238686369432644323123785)
      ·
        refine ⟨104429014777074483242342839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139238686369432644323123785 104429014777074483242342839)
        ·
          refine ⟨156643522165611724863514259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104429014777074483242342839 156643522165611724863514259)
          ·
            refine ⟨234965283248417587295271389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156643522165611724863514259 234965283248417587295271389)
            ·
              refine ⟨88111981218156595235726771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234965283248417587295271389 88111981218156595235726771)
              ·
                refine ⟨132167971827234892853590157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88111981218156595235726771 132167971827234892853590157)
                ·
                  refine ⟨49562989435213084820096309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132167971827234892853590157 49562989435213084820096309)
                  ·
                    refine ⟨4646530259551226701884029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49562989435213084820096309 4646530259551226701884029)
                    ·
                      refine ⟨1742448847331710013206511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646530259551226701884029 1742448847331710013206511)
                      ·
                        rfl

theorem cell23_3393407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_3393407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393407 prefixEnd_3393407 := by exact prefixLift 3393407
  have htrace : WordTrace (prefixWord ++ tailWord_3393407) baseStart_3393407 baseEnd_3393407 := by
    simpa [prefixWord, tailWord_3393407, baseEnd_3393407] using wordTrace_append hprefix tailTrace_3393407
  have hstable : (prefixWord ++ tailWord_3393407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393407).length < 2 ^ (prefixWord ++ tailWord_3393407).sum := by decide
  have hdescent : baseEnd_3393407 < baseStart_3393407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393442 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_3393442 : Nat := 118140960795 + 3393442 * 2 ^ 59
def prefixEnd_3393442 : Nat := 4983230072969 + 3 ^ 40 * 3393442 * 2
def baseEnd_3393442 : Nat := 1742466819154617376268851

theorem tailTrace_3393442 : CollatzResearch.WordTrace tailWord_3393442 prefixEnd_3393442 1742466819154617376268851 := by
  unfold tailWord_3393442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30942249443036665649519645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82512665181431108398719053 30942249443036665649519645)
  ·
    refine ⟨11603343541138749618569867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30942249443036665649519645 11603343541138749618569867)
    ·
      refine ⟨17405015311708124427854801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11603343541138749618569867 17405015311708124427854801)
      ·
        refine ⟨13053761483781093320891101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17405015311708124427854801 13053761483781093320891101)
        ·
          refine ⟨4895160556417909995334163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13053761483781093320891101 4895160556417909995334163)
          ·
            refine ⟨7342740834626864993001245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895160556417909995334163 7342740834626864993001245)
            ·
              refine ⟨2753527812985074372375467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7342740834626864993001245 2753527812985074372375467)
              ·
                refine ⟨4130291719477611558563201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753527812985074372375467 4130291719477611558563201)
                ·
                  refine ⟨3097718789608208668922401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130291719477611558563201 3097718789608208668922401)
                  ·
                    refine ⟨2323289092206156501691801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3097718789608208668922401 2323289092206156501691801)
                    ·
                      refine ⟨1742466819154617376268851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323289092206156501691801 1742466819154617376268851)
                      ·
                        rfl

theorem cell23_3393442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_3393442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393442 prefixEnd_3393442 := by exact prefixLift 3393442
  have htrace : WordTrace (prefixWord ++ tailWord_3393442) baseStart_3393442 baseEnd_3393442 := by
    simpa [prefixWord, tailWord_3393442, baseEnd_3393442] using wordTrace_append hprefix tailTrace_3393442
  have hstable : (prefixWord ++ tailWord_3393442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393442).length < 2 ^ (prefixWord ++ tailWord_3393442).sum := by decide
  have hdescent : baseEnd_3393442 < baseStart_3393442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393464 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_3393464 : Nat := 118140960795 + 3393464 * 2 ^ 59
def prefixEnd_3393464 : Nat := 4983230072969 + 3 ^ 40 * 3393464 * 2
def baseEnd_3393464 : Nat := 1742478115729016290193749

theorem tailTrace_3393464 : CollatzResearch.WordTrace tailWord_3393464 prefixEnd_3393464 1742478115729016290193749 := by
  unfold tailWord_3393464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61884900089033480177689723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82513200118711306903586297 61884900089033480177689723)
  ·
    refine ⟨92827350133550220266534585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61884900089033480177689723 92827350133550220266534585)
    ·
      refine ⟨69620512600162665199900939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92827350133550220266534585 69620512600162665199900939)
      ·
        refine ⟨104430768900243997799851409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69620512600162665199900939 104430768900243997799851409)
        ·
          refine ⟨78323076675182998349888557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104430768900243997799851409 78323076675182998349888557)
          ·
            refine ⟨29371153753193624381208209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78323076675182998349888557 29371153753193624381208209)
            ·
              refine ⟨22028365314895218285906157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29371153753193624381208209 22028365314895218285906157)
              ·
                refine ⟨8260636993085706857214809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22028365314895218285906157 8260636993085706857214809)
                ·
                  refine ⟨6195477744814280142911107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260636993085706857214809 6195477744814280142911107)
                  ·
                    refine ⟨9293216617221420214366661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195477744814280142911107 9293216617221420214366661)
                    ·
                      refine ⟨1742478115729016290193749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9293216617221420214366661 1742478115729016290193749)
                      ·
                        rfl

theorem cell23_3393464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_3393464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393464 prefixEnd_3393464 := by exact prefixLift 3393464
  have htrace : WordTrace (prefixWord ++ tailWord_3393464) baseStart_3393464 baseEnd_3393464 := by
    simpa [prefixWord, tailWord_3393464, baseEnd_3393464] using wordTrace_append hprefix tailTrace_3393464
  have hstable : (prefixWord ++ tailWord_3393464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393464).length < 2 ^ (prefixWord ++ tailWord_3393464).sum := by decide
  have hdescent : baseEnd_3393464 < baseStart_3393464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393477 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_3393477 : Nat := 118140960795 + 3393477 * 2 ^ 59
def prefixEnd_3393477 : Nat := 4983230072969 + 3 ^ 40 * 3393477 * 2
def baseEnd_3393477 : Nat := 1742484790977524739331189

theorem tailTrace_3393477 : CollatzResearch.WordTrace tailWord_3393477 prefixEnd_3393477 1742484790977524739331189 := by
  unfold tailWord_3393477
  simp only [CollatzResearch.WordTrace]
  refine ⟨123770274327019863575602685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82513516218013242383735123 123770274327019863575602685)
  ·
    refine ⟨46413852872632448840851007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123770274327019863575602685 46413852872632448840851007)
    ·
      refine ⟨69620779308948673261276511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46413852872632448840851007 69620779308948673261276511)
      ·
        refine ⟨104431168963423009891914767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69620779308948673261276511 104431168963423009891914767)
        ·
          refine ⟨156646753445134514837872151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104431168963423009891914767 156646753445134514837872151)
          ·
            refine ⟨234970130167701772256808227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156646753445134514837872151 234970130167701772256808227)
            ·
              refine ⟨352455195251552658385212341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234970130167701772256808227 352455195251552658385212341)
              ·
                refine ⟨33042674554833061723613657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 352455195251552658385212341 33042674554833061723613657)
                ·
                  refine ⟨24782005916124796292710243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33042674554833061723613657 24782005916124796292710243)
                  ·
                    refine ⟨37173008874187194439065365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24782005916124796292710243 37173008874187194439065365)
                    ·
                      refine ⟨1742484790977524739331189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37173008874187194439065365 1742484790977524739331189)
                      ·
                        rfl

theorem cell23_3393477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_3393477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393477 prefixEnd_3393477 := by exact prefixLift 3393477
  have htrace : WordTrace (prefixWord ++ tailWord_3393477) baseStart_3393477 baseEnd_3393477 := by
    simpa [prefixWord, tailWord_3393477, baseEnd_3393477] using wordTrace_append hprefix tailTrace_3393477
  have hstable : (prefixWord ++ tailWord_3393477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393477).length < 2 ^ (prefixWord ++ tailWord_3393477).sum := by decide
  have hdescent : baseEnd_3393477 < baseStart_3393477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393487 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 8]
def baseStart_3393487 : Nat := 118140960795 + 3393487 * 2 ^ 59
def prefixEnd_3393487 : Nat := 4983230072969 + 3 ^ 40 * 3393487 * 2
def baseEnd_3393487 : Nat := 193609991753785522245127

theorem tailTrace_3393487 : CollatzResearch.WordTrace tailWord_3393487 prefixEnd_3393487 193609991753785522245127 := by
  unfold tailWord_3393487
  simp only [CollatzResearch.WordTrace]
  refine ⟨123770639056983635283466715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82513759371322423522311143 123770639056983635283466715)
  ·
    refine ⟨185655958585475452925200073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123770639056983635283466715 185655958585475452925200073)
    ·
      refine ⟨139241968939106589693900055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185655958585475452925200073 139241968939106589693900055)
      ·
        refine ⟨208862953408659884540850083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139241968939106589693900055 208862953408659884540850083)
        ·
          refine ⟨313294430112989826811275125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208862953408659884540850083 313294430112989826811275125)
          ·
            refine ⟨29371352823092796263557043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 313294430112989826811275125 29371352823092796263557043)
            ·
              refine ⟨44057029234639194395335565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29371352823092796263557043 44057029234639194395335565)
              ·
                refine ⟨16521385962989697898250837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44057029234639194395335565 16521385962989697898250837)
                ·
                  refine ⟨193609991753785522245127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16521385962989697898250837 193609991753785522245127)
                  ·
                    rfl

theorem cell23_3393487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 8].length) (baseStart_3393487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393487 prefixEnd_3393487 := by exact prefixLift 3393487
  have htrace : WordTrace (prefixWord ++ tailWord_3393487) baseStart_3393487 baseEnd_3393487 := by
    simpa [prefixWord, tailWord_3393487, baseEnd_3393487] using wordTrace_append hprefix tailTrace_3393487
  have hstable : (prefixWord ++ tailWord_3393487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393487).length < 2 ^ (prefixWord ++ tailWord_3393487).sum := by decide
  have hdescent : baseEnd_3393487 < baseStart_3393487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393518 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_3393518 : Nat := 118140960795 + 3393518 * 2 ^ 59
def prefixEnd_3393518 : Nat := 4983230072969 + 3 ^ 40 * 3393518 * 2
def baseEnd_3393518 : Nat := 1742505843684359078918501

theorem tailTrace_3393518 : CollatzResearch.WordTrace tailWord_3393518 prefixEnd_3393518 1742505843684359078918501 := by
  unfold tailWord_3393518
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471471214983915947230651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82514513146580885051896805 15471471214983915947230651)
  ·
    refine ⟨23207206822475873920845977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15471471214983915947230651 23207206822475873920845977)
    ·
      refine ⟨17405405116856905440634483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23207206822475873920845977 17405405116856905440634483)
      ·
        refine ⟨26108107675285358160951725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17405405116856905440634483 26108107675285358160951725)
        ·
          refine ⟨9790540378232009310356897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26108107675285358160951725 9790540378232009310356897)
          ·
            refine ⟨7342905283674006982767673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790540378232009310356897 7342905283674006982767673)
            ·
              refine ⟨5507178962755505237075755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7342905283674006982767673 5507178962755505237075755)
              ·
                refine ⟨8260768444133257855613633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5507178962755505237075755 8260768444133257855613633)
                ·
                  refine ⟨6195576333099943391710225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8260768444133257855613633 6195576333099943391710225)
                  ·
                    refine ⟨4646682249824957543782669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6195576333099943391710225 4646682249824957543782669)
                    ·
                      refine ⟨1742505843684359078918501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646682249824957543782669 1742505843684359078918501)
                      ·
                        rfl

theorem cell23_3393518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_3393518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393518 prefixEnd_3393518 := by exact prefixLift 3393518
  have htrace : WordTrace (prefixWord ++ tailWord_3393518) baseStart_3393518 baseEnd_3393518 := by
    simpa [prefixWord, tailWord_3393518, baseEnd_3393518] using wordTrace_append hprefix tailTrace_3393518
  have hstable : (prefixWord ++ tailWord_3393518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393518).length < 2 ^ (prefixWord ++ tailWord_3393518).sum := by decide
  have hdescent : baseEnd_3393518 < baseStart_3393518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393527 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_3393527 : Nat := 118140960795 + 3393527 * 2 ^ 59
def prefixEnd_3393527 : Nat := 4983230072969 + 3 ^ 40 * 3393527 * 2
def baseEnd_3393527 : Nat := 1742510465010249543705959

theorem tailTrace_3393527 : CollatzResearch.WordTrace tailWord_3393527 prefixEnd_3393527 1742510465010249543705959 := by
  unfold tailWord_3393527
  simp only [CollatzResearch.WordTrace]
  refine ⟨123772097976838722114922835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82514731984559148076615223 123772097976838722114922835)
  ·
    refine ⟨185658146965258083172384253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123772097976838722114922835 185658146965258083172384253)
    ·
      refine ⟨69621805111971781189644095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 185658146965258083172384253 69621805111971781189644095)
      ·
        refine ⟨104432707667957671784466143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69621805111971781189644095 104432707667957671784466143)
        ·
          refine ⟨156649061501936507676699215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104432707667957671784466143 156649061501936507676699215)
          ·
            refine ⟨234973592252904761515048823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156649061501936507676699215 234973592252904761515048823)
            ·
              refine ⟨352460388379357142272573235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234973592252904761515048823 352460388379357142272573235)
              ·
                refine ⟨528690582569035713408859853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 352460388379357142272573235 528690582569035713408859853)
                ·
                  refine ⟨198258968463388392528322445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 528690582569035713408859853 198258968463388392528322445)
                  ·
                    refine ⟨74347113173770647198120917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 198258968463388392528322445 74347113173770647198120917)
                    ·
                      refine ⟨1742510465010249543705959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 74347113173770647198120917 1742510465010249543705959)
                      ·
                        rfl

theorem cell23_3393527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_3393527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393527 prefixEnd_3393527 := by exact prefixLift 3393527
  have htrace : WordTrace (prefixWord ++ tailWord_3393527) baseStart_3393527 baseEnd_3393527 := by
    simpa [prefixWord, tailWord_3393527, baseEnd_3393527] using wordTrace_append hprefix tailTrace_3393527
  have hstable : (prefixWord ++ tailWord_3393527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393527).length < 2 ^ (prefixWord ++ tailWord_3393527).sum := by decide
  have hdescent : baseEnd_3393527 < baseStart_3393527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393571 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 4]
def baseStart_3393571 : Nat := 118140960795 + 3393571 * 2 ^ 59
def prefixEnd_3393571 : Nat := 4983230072969 + 3 ^ 40 * 3393571 * 2
def baseEnd_3393571 : Nat := 1742533058159047371555757

theorem tailTrace_3393571 : CollatzResearch.WordTrace tailWord_3393571 prefixEnd_3393571 1742533058159047371555757 := by
  unfold tailWord_3393571
  simp only [CollatzResearch.WordTrace]
  refine ⟨123773702788679317629524567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82515801859119545086349711 123773702788679317629524567)
  ·
    refine ⟨185660554183018976444286851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123773702788679317629524567 185660554183018976444286851)
    ·
      refine ⟨278490831274528464666430277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185660554183018976444286851 278490831274528464666430277)
      ·
        refine ⟨52217030863974087124955677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 278490831274528464666430277 52217030863974087124955677)
        ·
          refine ⟨19581386573990282671858379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52217030863974087124955677 19581386573990282671858379)
          ·
            refine ⟨29372079860985424007787569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19581386573990282671858379 29372079860985424007787569)
            ·
              refine ⟨22029059895739068005840677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29372079860985424007787569 22029059895739068005840677)
              ·
                refine ⟨4130448730451075251095127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22029059895739068005840677 4130448730451075251095127)
                ·
                  refine ⟨6195673095676612876642691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130448730451075251095127 6195673095676612876642691)
                  ·
                    refine ⟨9293509643514919314964037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195673095676612876642691 9293509643514919314964037)
                    ·
                      refine ⟨1742533058159047371555757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9293509643514919314964037 1742533058159047371555757)
                      ·
                        rfl

theorem cell23_3393571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_3393571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393571 prefixEnd_3393571 := by exact prefixLift 3393571
  have htrace : WordTrace (prefixWord ++ tailWord_3393571) baseStart_3393571 baseEnd_3393571 := by
    simpa [prefixWord, tailWord_3393571, baseEnd_3393571] using wordTrace_append hprefix tailTrace_3393571
  have hstable : (prefixWord ++ tailWord_3393571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393571).length < 2 ^ (prefixWord ++ tailWord_3393571).sum := by decide
  have hdescent : baseEnd_3393571 < baseStart_3393571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393575 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3393575 : Nat := 118140960795 + 3393575 * 2 ^ 59
def prefixEnd_3393575 : Nat := 4983230072969 + 3 ^ 40 * 3393575 * 2
def baseEnd_3393575 : Nat := 1742535112081665355905739

theorem tailTrace_3393575 : CollatzResearch.WordTrace tailWord_3393575 prefixEnd_3393575 1742535112081665355905739 := by
  unfold tailWord_3393575
  simp only [CollatzResearch.WordTrace]
  refine ⟨123773848680664826312670179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82515899120443217541780119 123773848680664826312670179)
  ·
    refine ⟨185660773020997239469005269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123773848680664826312670179 185660773020997239469005269)
    ·
      refine ⟨4351424367679622800054811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 185660773020997239469005269 4351424367679622800054811)
      ·
        refine ⟨6527136551519434200082217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351424367679622800054811 6527136551519434200082217)
        ·
          refine ⟨4895352413639575650061663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6527136551519434200082217 4895352413639575650061663)
          ·
            refine ⟨7343028620459363475092495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895352413639575650061663 7343028620459363475092495)
            ·
              refine ⟨11014542930689045212638743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343028620459363475092495 11014542930689045212638743)
              ·
                refine ⟨16521814396033567818958115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11014542930689045212638743 16521814396033567818958115)
                ·
                  refine ⟨24782721594050351728437173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16521814396033567818958115 24782721594050351728437173)
                  ·
                    refine ⟨2323380149442220474540985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24782721594050351728437173 2323380149442220474540985)
                    ·
                      refine ⟨1742535112081665355905739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323380149442220474540985 1742535112081665355905739)
                      ·
                        rfl

theorem cell23_3393575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3393575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393575 prefixEnd_3393575 := by exact prefixLift 3393575
  have htrace : WordTrace (prefixWord ++ tailWord_3393575) baseStart_3393575 baseEnd_3393575 := by
    simpa [prefixWord, tailWord_3393575, baseEnd_3393575] using wordTrace_append hprefix tailTrace_3393575
  have hstable : (prefixWord ++ tailWord_3393575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393575).length < 2 ^ (prefixWord ++ tailWord_3393575).sum := by decide
  have hdescent : baseEnd_3393575 < baseStart_3393575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393582 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_3393582 : Nat := 118140960795 + 3393582 * 2 ^ 59
def prefixEnd_3393582 : Nat := 4983230072969 + 3 ^ 40 * 3393582 * 2
def baseEnd_3393582 : Nat := 1742538706446246828518207

theorem tailTrace_3393582 : CollatzResearch.WordTrace tailWord_3393582 prefixEnd_3393582 1742538706446246828518207 := by
  unfold tailWord_3393582
  simp only [CollatzResearch.WordTrace]
  refine ⟨15471762998954933313521875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82516069327759644338783333 15471762998954933313521875)
  ·
    refine ⟨23207644498432399970282813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15471762998954933313521875 23207644498432399970282813)
    ·
      refine ⟨8702866686912149988856055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23207644498432399970282813 8702866686912149988856055)
      ·
        refine ⟨13054300030368224983284083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8702866686912149988856055 13054300030368224983284083)
        ·
          refine ⟨19581450045552337474926125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054300030368224983284083 19581450045552337474926125)
          ·
            refine ⟨7343043767082126553097297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19581450045552337474926125 7343043767082126553097297)
            ·
              refine ⟨5507282825311594914822973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343043767082126553097297 5507282825311594914822973)
              ·
                refine ⟨2065231059491848093058615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5507282825311594914822973 2065231059491848093058615)
                ·
                  refine ⟨3097846589237772139587923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065231059491848093058615 3097846589237772139587923)
                  ·
                    refine ⟨4646769883856658209381885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097846589237772139587923 4646769883856658209381885)
                    ·
                      refine ⟨1742538706446246828518207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646769883856658209381885 1742538706446246828518207)
                      ·
                        rfl

theorem cell23_3393582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_3393582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393582 prefixEnd_3393582 := by exact prefixLift 3393582
  have htrace : WordTrace (prefixWord ++ tailWord_3393582) baseStart_3393582 baseEnd_3393582 := by
    simpa [prefixWord, tailWord_3393582, baseEnd_3393582] using wordTrace_append hprefix tailTrace_3393582
  have hstable : (prefixWord ++ tailWord_3393582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393582).length < 2 ^ (prefixWord ++ tailWord_3393582).sum := by decide
  have hdescent : baseEnd_3393582 < baseStart_3393582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393622 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3393622 : Nat := 118140960795 + 3393622 * 2 ^ 59
def prefixEnd_3393622 : Nat := 4983230072969 + 3 ^ 40 * 3393622 * 2
def baseEnd_3393622 : Nat := 1742559245672426672018023

theorem tailTrace_3393622 : CollatzResearch.WordTrace tailWord_3393622 prefixEnd_3393622 1742559245672426672018023 := by
  unfold tailWord_3393622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735972681968409583726945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 82517041940996368893087413 7735972681968409583726945)
  ·
    refine ⟨5801979511476307187795209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7735972681968409583726945 5801979511476307187795209)
    ·
      refine ⟨4351484633607230390846407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5801979511476307187795209 4351484633607230390846407)
      ·
        refine ⟨6527226950410845586269611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351484633607230390846407 6527226950410845586269611)
        ·
          refine ⟨9790840425616268379404417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527226950410845586269611 9790840425616268379404417)
          ·
            refine ⟨7343130319212201284553313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9790840425616268379404417 7343130319212201284553313)
            ·
              refine ⟨5507347739409150963414985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7343130319212201284553313 5507347739409150963414985)
              ·
                refine ⟨4130510804556863222561239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5507347739409150963414985 4130510804556863222561239)
                ·
                  refine ⟨6195766206835294833841859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4130510804556863222561239 6195766206835294833841859)
                  ·
                    refine ⟨9293649310252942250762789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6195766206835294833841859 9293649310252942250762789)
                    ·
                      refine ⟨1742559245672426672018023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9293649310252942250762789 1742559245672426672018023)
                      ·
                        rfl

theorem cell23_3393622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3393622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393622 prefixEnd_3393622 := by exact prefixLift 3393622
  have htrace : WordTrace (prefixWord ++ tailWord_3393622) baseStart_3393622 baseEnd_3393622 := by
    simpa [prefixWord, tailWord_3393622, baseEnd_3393622] using wordTrace_append hprefix tailTrace_3393622
  have hstable : (prefixWord ++ tailWord_3393622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393622).length < 2 ^ (prefixWord ++ tailWord_3393622).sum := by decide
  have hdescent : baseEnd_3393622 < baseStart_3393622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393628 : List Nat := [2, 2, 4, 1, 1, 4, 2, 7]
def baseStart_3393628 : Nat := 118140960795 + 3393628 * 2 ^ 59
def prefixEnd_3393628 : Nat := 4983230072969 + 3 ^ 40 * 3393628 * 2
def baseEnd_3393628 : Nat := 64539345428013098094185

theorem tailTrace_3393628 : CollatzResearch.WordTrace tailWord_3393628 prefixEnd_3393628 64539345428013098094185 := by
  unfold tailWord_3393628
  simp only [CollatzResearch.WordTrace]
  refine ⟨61887890874736408182174769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82517187832981877576233025 61887890874736408182174769)
  ·
    refine ⟨46415918156052306136631077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61887890874736408182174769 46415918156052306136631077)
    ·
      refine ⟨8702984654259807400618327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46415918156052306136631077 8702984654259807400618327)
      ·
        refine ⟨13054476981389711100927491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8702984654259807400618327 13054476981389711100927491)
        ·
          refine ⟨19581715472084566651391237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13054476981389711100927491 19581715472084566651391237)
          ·
            refine ⟨3671571651015856247135857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19581715472084566651391237 3671571651015856247135857)
            ·
              refine ⟨2753678738261892185351893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671571651015856247135857 2753678738261892185351893)
              ·
                refine ⟨64539345428013098094185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2753678738261892185351893 64539345428013098094185)
                ·
                  rfl

theorem cell23_3393628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 7].length) (baseStart_3393628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393628 prefixEnd_3393628 := by exact prefixLift 3393628
  have htrace : WordTrace (prefixWord ++ tailWord_3393628) baseStart_3393628 baseEnd_3393628 := by
    simpa [prefixWord, tailWord_3393628, baseEnd_3393628] using wordTrace_append hprefix tailTrace_3393628
  have hstable : (prefixWord ++ tailWord_3393628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393628).length < 2 ^ (prefixWord ++ tailWord_3393628).sum := by decide
  have hdescent : baseEnd_3393628 < baseStart_3393628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393664 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_3393664 : Nat := 118140960795 + 3393664 * 2 ^ 59
def prefixEnd_3393664 : Nat := 4983230072969 + 3 ^ 40 * 3393664 * 2
def baseEnd_3393664 : Nat := 1742580811859915507692829

theorem tailTrace_3393664 : CollatzResearch.WordTrace tailWord_3393664 prefixEnd_3393664 1742580811859915507692829 := by
  unfold tailWord_3393664
  simp only [CollatzResearch.WordTrace]
  refine ⟨61888547388671197256330023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82518063184894929675106697 61888547388671197256330023)
  ·
    refine ⟨92832821083006795884495035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61888547388671197256330023 92832821083006795884495035)
    ·
      refine ⟨139249231624510193826742553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92832821083006795884495035 139249231624510193826742553)
      ·
        refine ⟨104436923718382645370056915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139249231624510193826742553 104436923718382645370056915)
        ·
          refine ⟨156655385577573968055085373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104436923718382645370056915 156655385577573968055085373)
          ·
            refine ⟨58745769591590238020657015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156655385577573968055085373 58745769591590238020657015)
            ·
              refine ⟨88118654387385357030985523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58745769591590238020657015 88118654387385357030985523)
              ·
                refine ⟨132177981581078035546478285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88118654387385357030985523 132177981581078035546478285)
                ·
                  refine ⟨49566743092904263329929357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 132177981581078035546478285 49566743092904263329929357)
                  ·
                    refine ⟨18587528659839098748723509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49566743092904263329929357 18587528659839098748723509)
                    ·
                      refine ⟨1742580811859915507692829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18587528659839098748723509 1742580811859915507692829)
                      ·
                        rfl

theorem cell23_3393664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_3393664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393664 prefixEnd_3393664 := by exact prefixLift 3393664
  have htrace : WordTrace (prefixWord ++ tailWord_3393664) baseStart_3393664 baseEnd_3393664 := by
    simpa [prefixWord, tailWord_3393664, baseEnd_3393664] using wordTrace_append hprefix tailTrace_3393664
  have hstable : (prefixWord ++ tailWord_3393664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393664).length < 2 ^ (prefixWord ++ tailWord_3393664).sum := by decide
  have hdescent : baseEnd_3393664 < baseStart_3393664 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393672 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_3393672 : Nat := 118140960795 + 3393672 * 2 ^ 59
def prefixEnd_3393672 : Nat := 4983230072969 + 3 ^ 40 * 3393672 * 2
def baseEnd_3393672 : Nat := 1742584919705151476392793

theorem tailTrace_3393672 : CollatzResearch.WordTrace tailWord_3393672 prefixEnd_3393672 1742584919705151476392793 := by
  unfold tailWord_3393672
  simp only [CollatzResearch.WordTrace]
  refine ⟨61888693280656705939475635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82518257707542274585967513 61888693280656705939475635)
  ·
    refine ⟨92833039920985058909213453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61888693280656705939475635 92833039920985058909213453)
    ·
      refine ⟨34812389970369397090955045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92833039920985058909213453 34812389970369397090955045)
      ·
        refine ⟨6527323119444261954554071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34812389970369397090955045 6527323119444261954554071)
        ·
          refine ⟨9790984679166392931831107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527323119444261954554071 9790984679166392931831107)
          ·
            refine ⟨14686477018749589397746661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9790984679166392931831107 14686477018749589397746661)
            ·
              refine ⟨2753714441015548012077499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14686477018749589397746661 2753714441015548012077499)
              ·
                refine ⟨4130571661523322018116249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753714441015548012077499 4130571661523322018116249)
                ·
                  refine ⟨3097928746142491513587187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4130571661523322018116249 3097928746142491513587187)
                  ·
                    refine ⟨4646893119213737270380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3097928746142491513587187 4646893119213737270380781)
                    ·
                      refine ⟨1742584919705151476392793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646893119213737270380781 1742584919705151476392793)
                      ·
                        rfl

theorem cell23_3393672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_3393672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393672 prefixEnd_3393672 := by exact prefixLift 3393672
  have htrace : WordTrace (prefixWord ++ tailWord_3393672) baseStart_3393672 baseEnd_3393672 := by
    simpa [prefixWord, tailWord_3393672, baseEnd_3393672] using wordTrace_append hprefix tailTrace_3393672
  have hstable : (prefixWord ++ tailWord_3393672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393672).length < 2 ^ (prefixWord ++ tailWord_3393672).sum := by decide
  have hdescent : baseEnd_3393672 < baseStart_3393672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393695 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3393695 : Nat := 118140960795 + 3393695 * 2 ^ 59
def prefixEnd_3393695 : Nat := 4983230072969 + 3 ^ 40 * 3393695 * 2
def baseEnd_3393695 : Nat := 1742596729760204886405187

theorem tailTrace_3393695 : CollatzResearch.WordTrace tailWord_3393695 prefixEnd_3393695 1742596729760204886405187 := by
  unfold tailWord_3393695
  simp only [CollatzResearch.WordTrace]
  refine ⟨123778225440230086807038539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82518816960153391204692359 123778225440230086807038539)
  ·
    refine ⟨185667338160345130210557809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123778225440230086807038539 185667338160345130210557809)
    ·
      refine ⟨139250503620258847657918357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185667338160345130210557809 139250503620258847657918357)
      ·
        refine ⟨6527367357199633483964923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 139250503620258847657918357 6527367357199633483964923)
        ·
          refine ⟨9791051035799450225947385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527367357199633483964923 9791051035799450225947385)
          ·
            refine ⟨7343288276849587669460539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791051035799450225947385 7343288276849587669460539)
            ·
              refine ⟨11014932415274381504190809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343288276849587669460539 11014932415274381504190809)
              ·
                refine ⟨8261199311455786128143107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11014932415274381504190809 8261199311455786128143107)
                ·
                  refine ⟨12391798967183679192214661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261199311455786128143107 12391798967183679192214661)
                  ·
                    refine ⟨2323462306346939848540249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12391798967183679192214661 2323462306346939848540249)
                    ·
                      refine ⟨1742596729760204886405187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323462306346939848540249 1742596729760204886405187)
                      ·
                        rfl

theorem cell23_3393695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3393695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393695 prefixEnd_3393695 := by exact prefixLift 3393695
  have htrace : WordTrace (prefixWord ++ tailWord_3393695) baseStart_3393695 baseEnd_3393695 := by
    simpa [prefixWord, tailWord_3393695, baseEnd_3393695] using wordTrace_append hprefix tailTrace_3393695
  have hstable : (prefixWord ++ tailWord_3393695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393695).length < 2 ^ (prefixWord ++ tailWord_3393695).sum := by decide
  have hdescent : baseEnd_3393695 < baseStart_3393695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393698 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_3393698 : Nat := 118140960795 + 3393698 * 2 ^ 59
def prefixEnd_3393698 : Nat := 4983230072969 + 3 ^ 40 * 3393698 * 2
def baseEnd_3393698 : Nat := 1742598270202168374667673

theorem tailTrace_3393698 : CollatzResearch.WordTrace tailWord_3393698 prefixEnd_3393698 1742598270202168374667673 := by
  unfold tailWord_3393698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30944583714804804579849437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82518889906146145546265165 30944583714804804579849437)
  ·
    refine ⟨11604218893051801717443539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30944583714804804579849437 11604218893051801717443539)
    ·
      refine ⟨17406328339577702576165309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11604218893051801717443539 17406328339577702576165309)
      ·
        refine ⟨6527373127341638466061991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17406328339577702576165309 6527373127341638466061991)
        ·
          refine ⟨9791059691012457699092987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527373127341638466061991 9791059691012457699092987)
          ·
            refine ⟨14686589536518686548639481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791059691012457699092987 14686589536518686548639481)
            ·
              refine ⟨11014942152389014911479611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14686589536518686548639481 11014942152389014911479611)
              ·
                refine ⟨16522413228583522367219417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11014942152389014911479611 16522413228583522367219417)
                ·
                  refine ⟨12391809921437641775414563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16522413228583522367219417 12391809921437641775414563)
                  ·
                    refine ⟨18587714882156462663121845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12391809921437641775414563 18587714882156462663121845)
                    ·
                      refine ⟨1742598270202168374667673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18587714882156462663121845 1742598270202168374667673)
                      ·
                        rfl

theorem cell23_3393698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_3393698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393698 prefixEnd_3393698 := by exact prefixLift 3393698
  have htrace : WordTrace (prefixWord ++ tailWord_3393698) baseStart_3393698 baseEnd_3393698 := by
    simpa [prefixWord, tailWord_3393698, baseEnd_3393698] using wordTrace_append hprefix tailTrace_3393698
  have hstable : (prefixWord ++ tailWord_3393698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393698).length < 2 ^ (prefixWord ++ tailWord_3393698).sum := by decide
  have hdescent : baseEnd_3393698 < baseStart_3393698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393711 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_3393711 : Nat := 118140960795 + 3393711 * 2 ^ 59
def prefixEnd_3393711 : Nat := 4983230072969 + 3 ^ 40 * 3393711 * 2
def baseEnd_3393711 : Nat := 1742604945450676823805113

theorem tailTrace_3393711 : CollatzResearch.WordTrace tailWord_3393711 prefixEnd_3393711 1742604945450676823805113 := by
  unfold tailWord_3393711
  simp only [CollatzResearch.WordTrace]
  refine ⟨123778809008172121539620987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82519206005448081026413991 123778809008172121539620987)
  ·
    refine ⟨185668213512258182309431481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123778809008172121539620987 185668213512258182309431481)
    ·
      refine ⟨139251160134193636732073611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185668213512258182309431481 139251160134193636732073611)
      ·
        refine ⟨208876740201290455098110417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139251160134193636732073611 208876740201290455098110417)
        ·
          refine ⟨156657555150967841323582813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208876740201290455098110417 156657555150967841323582813)
          ·
            refine ⟨58746583181612940496343555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156657555150967841323582813 58746583181612940496343555)
            ·
              refine ⟨88119874772419410744515333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58746583181612940496343555 88119874772419410744515333)
              ·
                refine ⟨16522476519828639514596625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88119874772419410744515333 16522476519828639514596625)
                ·
                  refine ⟨12391857389871479635947469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16522476519828639514596625 12391857389871479635947469)
                  ·
                    refine ⟨4646946521201804863480301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391857389871479635947469 4646946521201804863480301)
                    ·
                      refine ⟨1742604945450676823805113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646946521201804863480301 1742604945450676823805113)
                      ·
                        rfl

theorem cell23_3393711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_3393711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393711 prefixEnd_3393711 := by exact prefixLift 3393711
  have htrace : WordTrace (prefixWord ++ tailWord_3393711) baseStart_3393711 baseEnd_3393711 := by
    simpa [prefixWord, tailWord_3393711, baseEnd_3393711] using wordTrace_append hprefix tailTrace_3393711
  have hstable : (prefixWord ++ tailWord_3393711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393711).length < 2 ^ (prefixWord ++ tailWord_3393711).sum := by decide
  have hdescent : baseEnd_3393711 < baseStart_3393711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393728 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3]
def baseStart_3393728 : Nat := 118140960795 + 3393728 * 2 ^ 59
def prefixEnd_3393728 : Nat := 4983230072969 + 3 ^ 40 * 3393728 * 2
def baseEnd_3393728 : Nat := 1742613674621803257292535

theorem tailTrace_3393728 : CollatzResearch.WordTrace tailWord_3393728 prefixEnd_3393728 1742613674621803257292535 := by
  unfold tailWord_3393728
  simp only [CollatzResearch.WordTrace]
  refine ⟨61889714524555266721494919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82519619366073688961993225 61889714524555266721494919)
  ·
    refine ⟨92834571786832900082242379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61889714524555266721494919 92834571786832900082242379)
    ·
      refine ⟨139251857680249350123363569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92834571786832900082242379 139251857680249350123363569)
      ·
        refine ⟨104438893260187012592522677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 139251857680249350123363569 104438893260187012592522677)
        ·
          refine ⟨9791146243142532430549001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 104438893260187012592522677 9791146243142532430549001)
          ·
            refine ⟨7343359682356899322911751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9791146243142532430549001 7343359682356899322911751)
            ·
              refine ⟨11015039523535348984367627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7343359682356899322911751 11015039523535348984367627)
              ·
                refine ⟨16522559285303023476551441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11015039523535348984367627 16522559285303023476551441)
                ·
                  refine ⟨12391919463977267607413581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16522559285303023476551441 12391919463977267607413581)
                  ·
                    refine ⟨4646969798991475352780093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12391919463977267607413581 4646969798991475352780093)
                    ·
                      refine ⟨1742613674621803257292535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4646969798991475352780093 1742613674621803257292535)
                      ·
                        rfl

theorem cell23_3393728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_3393728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393728 prefixEnd_3393728 := by exact prefixLift 3393728
  have htrace : WordTrace (prefixWord ++ tailWord_3393728) baseStart_3393728 baseEnd_3393728 := by
    simpa [prefixWord, tailWord_3393728, baseEnd_3393728] using wordTrace_append hprefix tailTrace_3393728
  have hstable : (prefixWord ++ tailWord_3393728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393728).length < 2 ^ (prefixWord ++ tailWord_3393728).sum := by decide
  have hdescent : baseEnd_3393728 < baseStart_3393728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393738 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_3393738 : Nat := 118140960795 + 3393738 * 2 ^ 59
def prefixEnd_3393738 : Nat := 4983230072969 + 3 ^ 40 * 3393738 * 2
def baseEnd_3393738 : Nat := 1742618809428348218167489

theorem tailTrace_3393738 : CollatzResearch.WordTrace tailWord_3393738 prefixEnd_3393738 1742618809428348218167489 := by
  unfold tailWord_3393738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30944948444768576287713467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82519862519382870100569245 30944948444768576287713467)
  ·
    refine ⟨46417422667152864431570201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30944948444768576287713467 46417422667152864431570201)
    ·
      refine ⟨34813067000364648323677651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46417422667152864431570201 34813067000364648323677651)
      ·
        refine ⟨52219600500546972485516477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34813067000364648323677651 52219600500546972485516477)
        ·
          refine ⟨19582350187705114682068679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52219600500546972485516477 19582350187705114682068679)
          ·
            refine ⟨29373525281557672023103019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19582350187705114682068679 29373525281557672023103019)
            ·
              refine ⟨44060287922336508034654529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29373525281557672023103019 44060287922336508034654529)
              ·
                refine ⟨33045215941752381025990897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44060287922336508034654529 33045215941752381025990897)
                ·
                  refine ⟨24783911956314285769493173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33045215941752381025990897 24783911956314285769493173)
                  ·
                    refine ⟨2323491745904464290889985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24783911956314285769493173 2323491745904464290889985)
                    ·
                      refine ⟨1742618809428348218167489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323491745904464290889985 1742618809428348218167489)
                      ·
                        rfl

theorem cell23_3393738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_3393738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393738 prefixEnd_3393738 := by exact prefixLift 3393738
  have htrace : WordTrace (prefixWord ++ tailWord_3393738) baseStart_3393738 baseEnd_3393738 := by
    simpa [prefixWord, tailWord_3393738, baseEnd_3393738] using wordTrace_append hprefix tailTrace_3393738
  have hstable : (prefixWord ++ tailWord_3393738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393738).length < 2 ^ (prefixWord ++ tailWord_3393738).sum := by decide
  have hdescent : baseEnd_3393738 < baseStart_3393738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393788 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3393788 : Nat := 118140960795 + 3393788 * 2 ^ 59
def prefixEnd_3393788 : Nat := 4983230072969 + 3 ^ 40 * 3393788 * 2
def baseEnd_3393788 : Nat := 1742644483461073022542259

theorem tailTrace_3393788 : CollatzResearch.WordTrace tailWord_3393788 prefixEnd_3393788 1742644483461073022542259 := by
  unfold tailWord_3393788
  simp only [CollatzResearch.WordTrace]
  refine ⟨61890808714446581845087009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82521078285928775793449345 61890808714446581845087009)
  ·
    refine ⟨46418106535834936383815257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61890808714446581845087009 46418106535834936383815257)
    ·
      refine ⟨34813579901876202287861443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46418106535834936383815257 34813579901876202287861443)
      ·
        refine ⟨52220369852814303431792165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34813579901876202287861443 52220369852814303431792165)
        ·
          refine ⟨9791319347402681893461031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52220369852814303431792165 9791319347402681893461031)
          ·
            refine ⟨14686979021104022840191547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791319347402681893461031 14686979021104022840191547)
            ·
              refine ⟨22030468531656034260287321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14686979021104022840191547 22030468531656034260287321)
              ·
                refine ⟨16522851398742025695215491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22030468531656034260287321 16522851398742025695215491)
                ·
                  refine ⟨24784277098113038542823237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16522851398742025695215491 24784277098113038542823237)
                  ·
                    refine ⟨4647051955896194726779357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24784277098113038542823237 4647051955896194726779357)
                    ·
                      refine ⟨1742644483461073022542259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647051955896194726779357 1742644483461073022542259)
                      ·
                        rfl

theorem cell23_3393788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3393788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393788 prefixEnd_3393788 := by exact prefixLift 3393788
  have htrace : WordTrace (prefixWord ++ tailWord_3393788) baseStart_3393788 baseEnd_3393788 := by
    simpa [prefixWord, tailWord_3393788, baseEnd_3393788] using wordTrace_append hprefix tailTrace_3393788
  have hstable : (prefixWord ++ tailWord_3393788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393788).length < 2 ^ (prefixWord ++ tailWord_3393788).sum := by decide
  have hdescent : baseEnd_3393788 < baseStart_3393788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393822 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3393822 : Nat := 118140960795 + 3393822 * 2 ^ 59
def prefixEnd_3393822 : Nat := 4983230072969 + 3 ^ 40 * 3393822 * 2
def baseEnd_3393822 : Nat := 1742661941803325889517103

theorem tailTrace_3393822 : CollatzResearch.WordTrace tailWord_3393822 prefixEnd_3393822 1742661941803325889517103 := by
  unfold tailWord_3393822
  simp only [CollatzResearch.WordTrace]
  refine ⟨15472857188846248437113965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 82521905007179991664607813 15472857188846248437113965)
  ·
    refine ⟨5802321445817343163917737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15472857188846248437113965 5802321445817343163917737)
    ·
      refine ⟨4351741084363007372938303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5802321445817343163917737 4351741084363007372938303)
      ·
        refine ⟨6527611626544511059407455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4351741084363007372938303 6527611626544511059407455)
        ·
          refine ⟨9791417439816766589111183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6527611626544511059407455 9791417439816766589111183)
          ·
            refine ⟨14687126159725149883666775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9791417439816766589111183 14687126159725149883666775)
            ·
              refine ⟨22030689239587724825500163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14687126159725149883666775 22030689239587724825500163)
              ·
                refine ⟨33046033859381587238250245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22030689239587724825500163 33046033859381587238250245)
                ·
                  refine ⟨6196131348634047607171921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33046033859381587238250245 6196131348634047607171921)
                  ·
                    refine ⟨4647098511475535705378941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6196131348634047607171921 4647098511475535705378941)
                    ·
                      refine ⟨1742661941803325889517103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4647098511475535705378941 1742661941803325889517103)
                      ·
                        rfl

theorem cell23_3393822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3393822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393822 prefixEnd_3393822 := by exact prefixLift 3393822
  have htrace : WordTrace (prefixWord ++ tailWord_3393822) baseStart_3393822 baseEnd_3393822 := by
    simpa [prefixWord, tailWord_3393822, baseEnd_3393822] using wordTrace_append hprefix tailTrace_3393822
  have hstable : (prefixWord ++ tailWord_3393822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393822).length < 2 ^ (prefixWord ++ tailWord_3393822).sum := by decide
  have hdescent : baseEnd_3393822 < baseStart_3393822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393829 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 1, 4]
def baseStart_3393829 : Nat := 118140960795 + 3393829 * 2 ^ 59
def prefixEnd_3393829 : Nat := 4983230072969 + 3 ^ 40 * 3393829 * 2
def baseEnd_3393829 : Nat := 580888512055969120709857

theorem tailTrace_3393829 : CollatzResearch.WordTrace tailWord_3393829 prefixEnd_3393829 580888512055969120709857 := by
  unfold tailWord_3393829
  simp only [CollatzResearch.WordTrace]
  refine ⟨123783112821744627692416541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82522075214496418461611027 123783112821744627692416541)
  ·
    refine ⟨46418667308154235384656203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123783112821744627692416541 46418667308154235384656203)
    ·
      refine ⟨69628000962231353076984305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46418667308154235384656203 69628000962231353076984305)
      ·
        refine ⟨52221000721673514807738229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69628000962231353076984305 52221000721673514807738229)
        ·
          refine ⟨4895718817656892013225459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52221000721673514807738229 4895718817656892013225459)
          ·
            refine ⟨7343578226485338019838189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4895718817656892013225459 7343578226485338019838189)
            ·
              refine ⟨2753841834932001757439321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7343578226485338019838189 2753841834932001757439321)
              ·
                refine ⟨2065381376199001318079491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2753841834932001757439321 2065381376199001318079491)
                ·
                  refine ⟨3098072064298501977119237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2065381376199001318079491 3098072064298501977119237)
                  ·
                    refine ⟨580888512055969120709857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3098072064298501977119237 580888512055969120709857)
                    ·
                      rfl

theorem cell23_3393829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_3393829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393829 prefixEnd_3393829 := by exact prefixLift 3393829
  have htrace : WordTrace (prefixWord ++ tailWord_3393829) baseStart_3393829 baseEnd_3393829 := by
    simpa [prefixWord, tailWord_3393829, baseEnd_3393829] using wordTrace_append hprefix tailTrace_3393829
  have hstable : (prefixWord ++ tailWord_3393829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393829).length < 2 ^ (prefixWord ++ tailWord_3393829).sum := by decide
  have hdescent : baseEnd_3393829 < baseStart_3393829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393842 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 6]
def baseStart_3393842 : Nat := 118140960795 + 3393842 * 2 ^ 59
def prefixEnd_3393842 : Nat := 4983230072969 + 3 ^ 40 * 3393842 * 2
def baseEnd_3393842 : Nat := 193630245712935090140779

theorem tailTrace_3393842 : CollatzResearch.WordTrace tailWord_3393842 prefixEnd_3393842 193630245712935090140779 := by
  unfold tailWord_3393842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30945896742674382728159945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 82522391313798353941759853 30945896742674382728159945)
  ·
    refine ⟨23209422557005787046119959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30945896742674382728159945 23209422557005787046119959)
    ·
      refine ⟨34814133835508680569179939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23209422557005787046119959 34814133835508680569179939)
      ·
        refine ⟨52221200753263020853769909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34814133835508680569179939 52221200753263020853769909)
        ·
          refine ⟨4895737570618408205040929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52221200753263020853769909 4895737570618408205040929)
          ·
            refine ⟨3671803177963806153780697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4895737570618408205040929 3671803177963806153780697)
            ·
              refine ⟨2753852383472854615335523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3671803177963806153780697 2753852383472854615335523)
              ·
                refine ⟨4130778575209281923003285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2753852383472854615335523 4130778575209281923003285)
                ·
                  refine ⟨193630245712935090140779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4130778575209281923003285 193630245712935090140779)
                  ·
                    rfl

theorem cell23_3393842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_3393842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393842 prefixEnd_3393842 := by exact prefixLift 3393842
  have htrace : WordTrace (prefixWord ++ tailWord_3393842) baseStart_3393842 baseEnd_3393842 := by
    simpa [prefixWord, tailWord_3393842, baseEnd_3393842] using wordTrace_append hprefix tailTrace_3393842
  have hstable : (prefixWord ++ tailWord_3393842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393842).length < 2 ^ (prefixWord ++ tailWord_3393842).sum := by decide
  have hdescent : baseEnd_3393842 < baseStart_3393842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393845 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_3393845 : Nat := 118140960795 + 3393845 * 2 ^ 59
def prefixEnd_3393845 : Nat := 4983230072969 + 3 ^ 40 * 3393845 * 2
def baseEnd_3393845 : Nat := 1742673751858379299529497

theorem tailTrace_3393845 : CollatzResearch.WordTrace tailWord_3393845 prefixEnd_3393845 1742673751858379299529497 := by
  unfold tailWord_3393845
  simp only [CollatzResearch.WordTrace]
  refine ⟨123783696389686662424998989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82522464259791108283332659 123783696389686662424998989)
  ·
    refine ⟨46418886146132498409374621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123783696389686662424998989 46418886146132498409374621)
    ·
      refine ⟨17407082304799686903515483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46418886146132498409374621 17407082304799686903515483)
      ·
        refine ⟨26110623457199530355273225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17407082304799686903515483 26110623457199530355273225)
        ·
          refine ⟨19582967592899647766454919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26110623457199530355273225 19582967592899647766454919)
          ·
            refine ⟨29374451389349471649682379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19582967592899647766454919 29374451389349471649682379)
            ·
              refine ⟨44061677084024207474523569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29374451389349471649682379 44061677084024207474523569)
              ·
                refine ⟨33046257813018155605892677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44061677084024207474523569 33046257813018155605892677)
                ·
                  refine ⟨6196173339940904176104877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33046257813018155605892677 6196173339940904176104877)
                  ·
                    refine ⟨2323565002477839066039329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6196173339940904176104877 2323565002477839066039329)
                    ·
                      refine ⟨1742673751858379299529497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323565002477839066039329 1742673751858379299529497)
                      ·
                        rfl

theorem cell23_3393845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_3393845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393845 prefixEnd_3393845 := by exact prefixLift 3393845
  have htrace : WordTrace (prefixWord ++ tailWord_3393845) baseStart_3393845 baseEnd_3393845 := by
    simpa [prefixWord, tailWord_3393845, baseEnd_3393845] using wordTrace_append hprefix tailTrace_3393845
  have hstable : (prefixWord ++ tailWord_3393845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393845).length < 2 ^ (prefixWord ++ tailWord_3393845).sum := by decide
  have hdescent : baseEnd_3393845 < baseStart_3393845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393861 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_3393861 : Nat := 118140960795 + 3393861 * 2 ^ 59
def prefixEnd_3393861 : Nat := 4983230072969 + 3 ^ 40 * 3393861 * 2
def baseEnd_3393861 : Nat := 1742681967548851236929423

theorem tailTrace_3393861 : CollatzResearch.WordTrace tailWord_3393861 prefixEnd_3393861 1742681967548851236929423 := by
  unfold tailWord_3393861
  simp only [CollatzResearch.WordTrace]
  refine ⟨123784279957628697157581437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82522853305085798105054291 123784279957628697157581437)
  ·
    refine ⟨46419104984110761434093039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 123784279957628697157581437 46419104984110761434093039)
    ·
      refine ⟨69628657476166142151139559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419104984110761434093039 69628657476166142151139559)
      ·
        refine ⟨104442986214249213226709339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69628657476166142151139559 104442986214249213226709339)
        ·
          refine ⟨156664479321373819840064009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104442986214249213226709339 156664479321373819840064009)
          ·
            refine ⟨117498359491030364880048007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156664479321373819840064009 117498359491030364880048007)
            ·
              refine ⟨176247539236545547320072011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117498359491030364880048007 176247539236545547320072011)
              ·
                refine ⟨264371308854818320980108017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 176247539236545547320072011 264371308854818320980108017)
                ·
                  refine ⟨198278481641113740735081013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 264371308854818320980108017 198278481641113740735081013)
                  ·
                    refine ⟨18588607653854413193913845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 198278481641113740735081013 18588607653854413193913845)
                    ·
                      refine ⟨1742681967548851236929423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18588607653854413193913845 1742681967548851236929423)
                      ·
                        rfl

theorem cell23_3393861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_3393861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393861 prefixEnd_3393861 := by exact prefixLift 3393861
  have htrace : WordTrace (prefixWord ++ tailWord_3393861) baseStart_3393861 baseEnd_3393861 := by
    simpa [prefixWord, tailWord_3393861, baseEnd_3393861] using wordTrace_append hprefix tailTrace_3393861
  have hstable : (prefixWord ++ tailWord_3393861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393861).length < 2 ^ (prefixWord ++ tailWord_3393861).sum := by decide
  have hdescent : baseEnd_3393861 < baseStart_3393861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393868 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 6]
def baseStart_3393868 : Nat := 118140960795 + 3393868 * 2 ^ 59
def prefixEnd_3393868 : Nat := 4983230072969 + 3 ^ 40 * 3393868 * 2
def baseEnd_3393868 : Nat := 580895187304477569847297

theorem tailTrace_3393868 : CollatzResearch.WordTrace tailWord_3393868 prefixEnd_3393868 580895187304477569847297 := by
  unfold tailWord_3393868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61892267634301668676543129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 82523023512402224902057505 61892267634301668676543129)
  ·
    refine ⟨46419200725726251507407347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61892267634301668676543129 46419200725726251507407347)
    ·
      refine ⟨69628801088589377261111021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46419200725726251507407347 69628801088589377261111021)
      ·
        refine ⟨26110800408221016472916633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69628801088589377261111021 26110800408221016472916633)
        ·
          refine ⟨19583100306165762354687475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26110800408221016472916633 19583100306165762354687475)
          ·
            refine ⟨29374650459248643532031213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19583100306165762354687475 29374650459248643532031213)
            ·
              refine ⟨11015493922218241324511705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29374650459248643532031213 11015493922218241324511705)
              ·
                refine ⟨8261620441663680993383779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11015493922218241324511705 8261620441663680993383779)
                ·
                  refine ⟨12392430662495521490075669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8261620441663680993383779 12392430662495521490075669)
                  ·
                    refine ⟨580895187304477569847297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12392430662495521490075669 580895187304477569847297)
                    ·
                      rfl

theorem cell23_3393868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_3393868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393868 prefixEnd_3393868 := by exact prefixLift 3393868
  have htrace : WordTrace (prefixWord ++ tailWord_3393868) baseStart_3393868 baseEnd_3393868 := by
    simpa [prefixWord, tailWord_3393868, baseEnd_3393868] using wordTrace_append hprefix tailTrace_3393868
  have hstable : (prefixWord ++ tailWord_3393868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393868).length < 2 ^ (prefixWord ++ tailWord_3393868).sum := by decide
  have hdescent : baseEnd_3393868 < baseStart_3393868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393871 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_3393871 : Nat := 118140960795 + 3393871 * 2 ^ 59
def prefixEnd_3393871 : Nat := 4983230072969 + 3 ^ 40 * 3393871 * 2
def baseEnd_3393871 : Nat := 1742687102355396197804377

theorem tailTrace_3393871 : CollatzResearch.WordTrace tailWord_3393871 prefixEnd_3393871 1742687102355396197804377 := by
  unfold tailWord_3393871
  simp only [CollatzResearch.WordTrace]
  refine ⟨123784644687592468865445467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82523096458394979243630311 123784644687592468865445467)
  ·
    refine ⟨185676967031388703298168201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123784644687592468865445467 185676967031388703298168201)
    ·
      refine ⟨139257725273541527473626151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 185676967031388703298168201 139257725273541527473626151)
      ·
        refine ⟨208886587910312291210439227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139257725273541527473626151 208886587910312291210439227)
        ·
          refine ⟨313329881865468436815658841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208886587910312291210439227 313329881865468436815658841)
          ·
            refine ⟨234997411399101327611744131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313329881865468436815658841 234997411399101327611744131)
            ·
              refine ⟨352496117098651991417616197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234997411399101327611744131 352496117098651991417616197)
              ·
                refine ⟨66093021955997248390803037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352496117098651991417616197 66093021955997248390803037)
                ·
                  refine ⟨24784883233498968146551139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66093021955997248390803037 24784883233498968146551139)
                  ·
                    refine ⟨37177324850248452219826709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24784883233498968146551139 37177324850248452219826709)
                    ·
                      refine ⟨1742687102355396197804377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 37177324850248452219826709 1742687102355396197804377)
                      ·
                        rfl

theorem cell23_3393871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_3393871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393871 prefixEnd_3393871 := by exact prefixLift 3393871
  have htrace : WordTrace (prefixWord ++ tailWord_3393871) baseStart_3393871 baseEnd_3393871 := by
    simpa [prefixWord, tailWord_3393871, baseEnd_3393871] using wordTrace_append hprefix tailTrace_3393871
  have hstable : (prefixWord ++ tailWord_3393871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393871).length < 2 ^ (prefixWord ++ tailWord_3393871).sum := by decide
  have hdescent : baseEnd_3393871 < baseStart_3393871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3393875 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 7, 2, 2]
def baseStart_3393875 : Nat := 118140960795 + 3393875 * 2 ^ 59
def prefixEnd_3393875 : Nat := 4983230072969 + 3 ^ 40 * 3393875 * 2
def baseEnd_3393875 : Nat := 1742689156278014182154359

theorem tailTrace_3393875 : CollatzResearch.WordTrace tailWord_3393875 prefixEnd_3393875 1742689156278014182154359 := by
  unfold tailWord_3393875
  simp only [CollatzResearch.WordTrace]
  refine ⟨123784790579577977548591079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 82523193719718651699060719 123784790579577977548591079)
  ·
    refine ⟨185677185869366966322886619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 123784790579577977548591079 185677185869366966322886619)
    ·
      refine ⟨278515778804050449484329929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 185677185869366966322886619 278515778804050449484329929)
      ·
        refine ⟨208886834103037837113247447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278515778804050449484329929 208886834103037837113247447)
        ·
          refine ⟨313330251154556755669871171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208886834103037837113247447 313330251154556755669871171)
          ·
            refine ⟨469995376731835133504806757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313330251154556755669871171 469995376731835133504806757)
            ·
              refine ⟨88124133137219087532151267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 469995376731835133504806757 88124133137219087532151267)
              ·
                refine ⟨132186199705828631298226901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88124133137219087532151267 132186199705828631298226901)
                ·
                  refine ⟨3098114055605358546052193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 132186199705828631298226901 3098114055605358546052193)
                  ·
                    refine ⟨2323585541704018909539145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3098114055605358546052193 2323585541704018909539145)
                    ·
                      refine ⟨1742689156278014182154359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2323585541704018909539145 1742689156278014182154359)
                      ·
                        rfl

theorem cell23_3393875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 2, 2].length) (baseStart_3393875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3393875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3393875 prefixEnd_3393875 := by exact prefixLift 3393875
  have htrace : WordTrace (prefixWord ++ tailWord_3393875) baseStart_3393875 baseEnd_3393875 := by
    simpa [prefixWord, tailWord_3393875, baseEnd_3393875] using wordTrace_append hprefix tailTrace_3393875
  have hstable : (prefixWord ++ tailWord_3393875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3393875).length < 2 ^ (prefixWord ++ tailWord_3393875).sum := by decide
  have hdescent : baseEnd_3393875 < baseStart_3393875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3393875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
